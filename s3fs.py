#!/usr/bin/env python
#
#    Copyright (C) 2006 Gary Ng <anything followed by funny at sign then garyng then a dot then com>
#
#    s3FS - S3 Filesystem Version 0.1
#    This program can be distributed under the terms of the GNU GPL.
#    See the file COPYING.
#    
#    This program is inspired by gmailfs  so credit should go to the author of
#    it as well
#
    
"""
s3FS provides a filesystem using Amazon's S3 web service as the backend storage

Overview:

Each s3fs would use ONE(1) bucket to store its data, the bucket name is
choosen as a md5 hash of the AWS key used(unless override for case of change
AWS key) + a choosen name(like the volume label). This allow multiple
bucket(100 as limited by Amazon).

objects stored on S3 consist of two categories, inode which stores the
meta data and small things(directory entries, symlinks) and dnode(for actual
regular file data). each dnode is fixed in size. file larger than blocksize
would be spread among multiple dnodes. ojbect key is in the form of
prefix_ino_index, say inode_1_0, inode_1_1 ... _0 is the inode, _1... are the
dnodes. 

This has the consequence that file operation unfortunately is not atomic but
means rename, chmod, chown etc. operation don't need to touch the actual data
nodes(thus much faster say if the file is 10M in size) as S3 doesn't support 
update operation. In addition, streaming for large file and retrieve/update 
offset in file is much more efficient.

directory is stored internally as python dictionary(path=inode) pairs and
pickle to store in the inode data body. file attributes are stored as S3
object metadata. symlink is stored in the inode data body

"""

# import 
from fuse import Fuse
import os
from errno import *
from stat import *
from os.path import abspath, expanduser

import thread
import quopri

import sys,traceback,re,string,time,tempfile,array,logging,logging.handlers,signal,optparse
import md5
import hmac
#import bitbucket
import cPickle
import httplib
import zlib
import random
import struct
import getpass
from threading import Thread
import atexit
import binascii
import boto.connection as S3
try: import boto.key as S3Key
except: import boto.s3.key as S3Key
from boto.exception import S3DataError
import socket
import select
import fcntl

# Globals
DefaultUsername = None
DefaultPassword = None
DefaultFsname = 's3fs'
CacheDir="/tmp"
CACHE_OBSERVER=0
CACHE_KEEP=1
CACHE_REMOVE_ON_UMOUNT=2
CACHE_REMOVE_ON_CLOSE=3
Cache_Policy=1
References={}
s3Link=None
RootIno = 1     #must be > 0, better be 1
ActiveFiles={}
Observe_Freq=10
FullFlushInterval = 5
LazyWrite = 2

rand = random.Random(time.time())
maxll = 2**63
#BLOCK_NEEDS_LOCAL_CACHE=2*1024*1024
BLOCK_NEEDS_LOCAL_CACHE=32*1024
TRIGGER = "."+md5.new(str(time.time())).hexdigest()

try:
    import psyco
    psyco.full()
except: pass

class AtomicCounter(object):
    def __init__(self):
        self._count = 0
        self.lock = thread.allocate_lock()

    def inc(self, x=1):
        self.lock.acquire()
        self._count+=x
        self.lock.release()

    def dec(self, x=1):
        self.lock.acquire()
        self._count-=x
        self.lock.release()

    def cnt(self): return self._count

class WaitableEvent(object):
    """Provides an abstract object that can be used to resume select loops with
    indefinite waits from another thread or process. This mimics the standard
    threading.Event interface."""
    def __init__(self):
        self._read_fd, self._write_fd = os.pipe()

    def wait(self, timeout=None):
        rfds, wfds, efds = select.select([self._read_fd], [], [], timeout)
        return self._read_fd in rfds

    def isSet(self):
        return self.wait(0)

    def clear(self):
        if self.isSet():
            os.read(self._read_fd, 1)

    def set(self):
        if not self.isSet():
            os.write(self._write_fd, '1')

    def fileno(self):
        """Return the FD number of the read side of the pipe, allows this object to
        be used with select.select()."""
        return self._read_fd

    def __del__(self):
        os.close(self._read_fd)
        os.close(self._write_fd)

class ARC4(object):
    """
    ARC4 encoder/decoder
    """
    def __init__(self, key, nonce, drop=1024):
        """
        key is the secret key
        nonce is the used once random number
        drop is how many bytes that would be dropped from the initial arc4
        stream, which somehow leaks key info in early stream
        """
        key = self.key = hmac.new(key, nonce).digest()
        self.nonce = nonce
        self.drop = drop
        self.salt = random.Random(key).randrange #weaker stream as salt
        arc4 = self.arc4 = self.arc4_key_stream(key) #ARC4 stream
        for x in xrange(drop): arc4.next() #drop the first 1024 byte

    def arc4_key_stream(self, key):
        """
        this function produce ARC4 random stream based on key
        it is recommended the first 256 byte should be discarded to
        work around a weakness in the algorithm if key is not choosen properly
        """
        state = range(256)
        klen = len(key)
        key = map(ord,key)
        j = 0
        # key scheduling
        for i in xrange(256):
            ki = i % klen
            j = (key[ki] + state[i] + j) % 256
            t = state[j]
            state[j] = state[i]
            state[i] = t

        i = j = 0 #ready to use
        while True: #produce as much byte as needed from now on
            i = (i + 1) % 256
            j = (j + state[i]) % 256
            t = state[j]
            state[j] = state[i]
            state[i] = t
            yield state[(state[i] + state[j]) % 256]

    def crypt(self, str):
        """
        the real encoder/decoder which is simple, just xor the two random
        stream against the input
        """
        arc4 = self.arc4
        salt = self.salt
        for x in str: yield chr(ord(x)^salt(256)^arc4.next())

def fork_it(f, *argv, **kw):
    pid = os.fork()
    if pid: return pid

    keep_running = argv[0]
    log = logging.getLogger('s3fs')
    def handler_term(sig, frame): 
        keep_running[0] = False
        log.info("Terminating forked child")

    signal.signal(signal.SIGTERM, handler_term)
    f(*argv, **kw)
    sys.exit(0)
    
def fork_wrapper(f):
    def _f(*argv, **kw):
        pid = os.fork()
        if pid: return pid

        keep_running = argv[0]
        log = logging.getLogger('s3fs')
        def handler_term(sig, frame): 
            keep_running[0] = False
            log.info("Terminating timer")

        signal.signal(signal.SIGTERM, handler_term)
        f(*argv, **kw)
        sys.exit(0)
    return _f
    
def Timer(keep_running, mountpoint, periodic=10):

    t = "%s/%s" % (mountpoint, TRIGGER)
    log.info("Timer started")
    while keep_running[0]:
        try: os.stat(t)
        except OSError: pass
        time.sleep(periodic)
    log.info("Timer stopped")

def _split_node_info(name):
    """
    in-transit node file is in the form of
    bucket_prefix_inode_N_hash_nonce_transit
    we need nonce as well since it is used for encryption and to be stored
    seperately in the object metadata
    """
    bucket, key = name.split("_",1)
    key, block, hash, nonce, state = key.rsplit("_", 4)
    return (bucket, key, block, hash, nonce, state)

def S3KeyRemover(keep_running, cache, prefix, s3link, periodic=5):
    while keep_running[0]:
        t = [ a for a in os.listdir(cache) if a.startswith(prefix) and a.endswith("_remove") ]
        cache = cache + "/"
        now = time.time()
        for x in t:
            path = cache + x
            bucket, ikey, block, hash, nonce, state = _split_node_info(x)
            key = ikey + "_" + block
            try:
                s3link.remove(key)
                log.debug("S3KeyRemover: %s is deleted" % (key,))
            except KeyError:
                log.warning("S3KeyRemover: %s is not found" % (key,))
            try: os.unlink(path)
            except OSError: pass
        end = time.time()
        if end - now < periodic: time.sleep(periodic)


def ReloadInTransit(keep_running, cache, prefix, s3link, periodic=5):
    """
    this function reload in transit inode blocks back to server, the equivalent
    of re-appling journal in a journaled FS, should only be run before
    mounting
    """
    def _send_to_S3(cache=cache, lazy=False):
        if lazy:
            t = [ a for a in os.listdir(cache) if a.startswith(prefix) and a.endswith("_lazy") ]
        else:
            t = [ a for a in os.listdir(cache) if a.startswith(prefix) and
                    (a.endswith("_transit") or a.endswith("_lazy")) ]

        t.sort()
        #log.info("Start re-applying in-transit-nodes %s/%s_*" % (cache,prefix ))
        cache = cache + "/"

        for x in t:
            path = cache + x
            bucket, ikey, block, hash, nonce, state = _split_node_info(x)
            key = ikey + "_" + block

            try:
                bits = s3link.get_head(key) #none existing one 
                old_md5 = bits.metadata['md5']
                if old_md5 == hash:
                    log.info("ReloadInTransit: %s data match S3 version, skipped" % (key,))
                    try: os.unlink(path)
                    except OSError: pass
                    continue
            except KeyError:
                old_md5 = None

            if int(block): #we only check this for data black
                try: 
                    bits = s3link.get_head(ikey+"_0") #none existing one 
                    log.debug("ReloadInTransit: inode data found for (%s, %s)" % (ikey, key))
                except KeyError: 
                    log.debug("ReloadInTransit: inode not found(%s)" % (ikey, ))
                    continue

            try: mtime = os.stat(path)[8]
            except OSError, e: continue

            bits = S3Key.Key()
            bits.key = key
            bits.metadata['md5']=hash
            bits.metadata['mtime']=str(mtime)
            try: bits.set_metadata('nonce', binascii.a2b_hex(nonce))
            except TypeError: pass

            try:
                x = path + "_reloading"
                os.rename(path, x)
                r = s3Link.set_file(bits, x)
                if r:
                    log.error("ReloadInTransit: %s upload failed" % (path, ))
                    try: os.rename(x, path)
                    except OSError: pass
                else:
                    log.info("ReloadInTransit: %s uploaded" % (key,))
                    os.unlink(x)
            except (OSError, IOError), e: 
                if e.errno == ENOENT: 
                    log.error("ReloadInTransit: %s disappeared" % (path, ))
                else:
                    log.error("ReloadInTransit: %s upload failed" % (path, ))

        #log.info("All in-transit-node uploaded")

    _send_to_S3()
    log.info("S3 uploader started")
    while keep_running[0]:
        now = time.time()
        _send_to_S3(lazy=True)
        end = time.time()
        if end - now < periodic: time.sleep(periodic)
    log.info("S3 uploader stopped")

def ManageCache(keep_running, cache, prefix, cache_for, periodic=5):
    """
    This function manage cache files found in cache(a directory)
    It would ignore file(relative, not full path) in in_transit dict
    files older(mtime/ctime < current) than cache_for seconds would be removed
    it runs for every periodic seconds
    """
    def _exclude(x):
        for a in ["_s3", "_remove", "_transit", "_lazy", "_reloading"]:
            if x.endswith(a): return True
        return False

    def _dirty(file):
        bucket, key = file.split("_",1)
        ikey, block = key.rsplit("_", 1)
        ikey = ikey + "_0"
        block = int(block)
        old_md5 = None
        mtime = os.stat(file)[8]
        try: 
            bits = s3Link.get_head(key)
            try: old_md5 = bits.metadata['md5']
            except KeyError: old_md5=None
        except KeyError: 
            log.info("ManageCache: block not on server(%s)" % (key,))
            try: 
                bits = s3Link.get_head(ikey)
            except KeyError: 
                now = time.time()
                log.info("ManageCache: inode not on server (%s)" % (ikey,))
                return now - mtime < 10*24*60*60 #we keep it for ten days
        try:
            f = open(file,"rb")
            x = f.read()
            f.close()
        except IOError, e: 
            if e.errno == ENOENT: return False
            pass

        if len(x) <= x.count("") and not old_md5: 
            log.debug("ManageCache: empty/sparse file")
            return False
        m_hash = md5.new(x).hexdigest()
        if m_hash != old_md5:
            log.info("ManageCache: m_hash(%s), s3(%s)" % (m_hash,old_md5))
            return True
        else: 
            return False

    log.info("Cache Manager started on %s/%s_" % (cache, prefix))
    while keep_running[0]:
        now = time.time()
        for x in os.listdir(cache):
            if not x.startswith(prefix) or _exclude(x): continue
            try:
                path = "%s/%s" % (cache, x)
                st = os.stat(path)
                if st[0] & S_IFDIR: continue
                #st[0] is mode
                #st[7] is atime, st[8] is mtime
                t = st[8]
                live = now - t
                if live > cache_for or (Cache_Policy == CACHE_OBSERVER and live > Observe_Freq):
                    dirty = _dirty(path)
                    if not dirty or Cache_Policy == CACHE_OBSERVER:
                        try: 
                            os.unlink(path) #remove it
                            log.debug("expired %s removed" % (path,))
                        except OSError, e: 
                            log.debug("Error in cleaning cache %s(%s)" % (path, str(e)))
                            pass #don't care about error
                    else:
                        log.info("hash doesn't match S3 version(%s)" % (path,))

                else: 
                    log.debug("%s age(%i) seconds" % (path, now - t))
                    #os.utime(path, (st[7], st[8])) #we atime is disrupted by us
            except OSError, e:
                if e.errno == ENOENT: pass #the file may have been deleted
        time.sleep(periodic)
    log.info("Cache Manager ended")

def daemonize(sin=None,so=None,serr=None):
    """
    after calling this function, the running process would be daemonized
    it is usually called in __main__
    sin/so/srr are the 3 basic files which if not specified would be
    redirected to /dev/null
    """
    try:
        pid = os.fork()
        if pid > 0: os._exit(0) #exist first parent
    except OSError, e: 
        raise Exception, "%s [%d]" % (e.strerror, e.errno)


    #first child
    os.chdir("/")
    os.umask(0)
    os.setsid()

    try:
        pid = os.fork()
        if pid > 0: os._exit(0) # Exit parent (the first child) of the second child.
    except OSError, e: 
        raise Exception, "%s [%d]" % (e.strerror, e.errno)

    #now we are the real daemon


    # The standard I/O file descriptors are redirected to /dev/null by default.
    if (hasattr(os, "devnull")): null = os.devnull
    else: null = "/dev/null"

    if not sin: sin = null

    MAXFD = 1024
    import resource		# Resource usage information.
    maxfd = resource.getrlimit(resource.RLIMIT_NOFILE)[1]
    if (maxfd == resource.RLIM_INFINITY): maxfd = MAXFD
  
    # Iterate through and close all file descriptors.
    for fd in range(0, maxfd):
        try: os.close(fd)
        except OSError:	pass # ERROR, fd wasn't open to begin with (ignored)

    os.open(sin, os.O_RDWR)	 # standard input (0)

    if not so: os.dup2(0, 1) # redirect to stdin if not specified
    else: os.open(so,os.O_RDWR)

    if not so: os.dup2(0, 2) # redirect to stdin if not specified
    else: os.open(so,os.O_RDWR)

    return(0)

def get_secret(prompt):
    """
    prompt user input without showing the input
    """
    for x in xrange(5):
        p1 = getpass.getpass(prompt)
        p2 = getpass.getpass("Type again:")
        if p1 == p2: return p1
        else: print "data entered doesn't match: try again"

    print "data entered doesn't match: ignored"
    return None
    
def _splitpath(path):
    """
    split a full path into (parent,fname) pair
    """
    try: ind = path.index('/')
    except ValueError: return ("",path) #no path delimited

    path = path.rstrip("/") #strip possible trailing "/"
    try: rind = path.rindex('/')
    except ValueError: return ("","/") #already the root
        
    parent = path[:rind].rstrip("/") #also strip unnessary "/"
    try: me = path[rind+1:]
    except IndexError: me = "/" # me is the root

    if parent=="": parent="/"
    return (parent, me)

def _human_size(b):
    """
    turn human used short cut to real number
    """
    b=b.strip()
    if not b[-1].isdigit():
        b,u = b[:-1],b[-1]
        if u == "k": u = 1000
        elif u == "K": u = 1024
        elif u == "m": u = 1000000
        elif u == "M": u = 1024*1024
        else: u = 1024
    else: u = 1
    return int(b)*u

def _blocks_spread(off, size, blocksize):
    """
    calculate how data from off of size is spreaded if each block is of
    blocksize
    """
    b1 = _block_no(off + 1, blocksize) #block the first byte is in
    b2 = _block_no(off + size, blocksize) #block the last byte is in
    for i, x in enumerate(xrange(b1,b2+1)):
        if i:
            boff = 0
            bsize = min(blocksize, size)
        else:
            boff = off % blocksize
            bsize = min(blocksize - boff, size)

        size -= bsize
        yield (x, boff , bsize)

def _blocks_needed(size, blocksize):
    """
    calculate how many blocks are needed for size with blocksize
    """
    return size//blocksize + ((size % blocksize) != 0)

def _block_no(offset, blocksize):
    return _blocks_needed(offset, blocksize) - 1

def _mkBucketName(name, aws_key):
    """
    Since S3 requires unique bucket name across system, we would make use of
    of KEY as part of the bucket name with the user choose name at the end
	to obfuscate it a bit, we use a md5 one way hash on the AWS key
    """
    return "%s.%s" % (md5.new(aws_key).hexdigest(), name)

def _cachePrefix():
    return "%s_%s" % (s3Link.bucketname, s3Link.fs_prefix)

def _mkInodeKey(inode, block=0):
    """
    construct key for a given inode block. _0 suffix is the inode, other
    numeric suffix are the dnodes
    """
    return "%s_%s_%s_%s" % (s3Link.fs_prefix, s3Link.inode_prefix, inode, block)

def _addLoggingHandlerHelper(handler):
    """ Sets our default formatter on the log handler before adding it to
        the log object. """
    handler.setFormatter(defaultLogFormatter)
    log.addHandler(handler)

def s3Config(fname):
    """ 
    Load configuration from fname, return config dict
    """
    import ConfigParser
    cp = ConfigParser.ConfigParser()
    global References
    global DefaultUsername, DefaultPassword, DefaultFsname
    global NumberQueryRetries
    try:
      cp.read(fname)
    except:
      log.warning("Unable to read configuration file: " + fname)
      return {}

    config = {}
    sections = cp.sections()
    if "account" in sections:
      options = cp.options("account")
      if "username" in options:
          config['username'] = cp.get("account", "username")
      if "password" in options:
          config['password'] = cp.get("account", "password")
    else:
      log.warning("No S3 account configuration in %s" % (fname,))

    if "filesystem" in sections:
      options = cp.options("filesystem")
      if "bucket" in options:
          config['bucket'] = cp.get("filesystem", "bucket")
      if "blocksize" in options:
          b = cp.get("filesystem", "blocksize").strip()
          config['blocksize'] = _human_size(b)
      if "encrypt" in options:
          config['encrypt'] = int(cp.get("filesystem", "encrypt"))
      if "compress" in options:
          config['compress'] = int(cp.get("filesystem", "compress"))
      if "enc_key" in options:
          config['enc_key'] = cp.get("filesystem", "enc_key")
      if "cache" in options:
          config['cache'] = cp.get("filesystem", "cache")
      if "cache_policy" in options:
          config['cache_policy'] = cp.get("filesystem", "cache_policy")
      if "cache_age" in options:
          config['cache_age'] = cp.get("filesystem", "cache_age")
      if "flush_freq" in options:
          config['flush_freq'] = cp.get("filesystem", "flush_freq")
      if "lazy_write" in options:
          global LazyWrite
          LazyWrite = int(cp.get("filesystem", "lazy_write"))
      if "observe_freq" in options:
          global Observe_Freq
          Observe_Freq = int(cp.get("filesystem", "observe_freq"))
      if "cache_block" in options:
          b = _human_size(cp.get("filesystem", "cache_block"))
          global BLOCK_NEEDS_LOCAL_CACHE
          BLOCK_NEEDS_LOCAL_CACHE = b
          config['cache_block'] = b
    else:
      log.info("Using default file system name %s" % (DefaultFsname,))
      
    if "logs" in sections:
      options = cp.options("logs")
      if "level" in options:
        level = cp.get("logs", "level")
        log.setLevel(logging._levelNames[level])
      if "logfile" in options:
        logfile = abspath(expanduser(cp.get("logs", "logfile")))
        log.removeHandler(defaultLoggingHandler)
        _addLoggingHandlerHelper(logging.handlers.RotatingFileHandler(logfile,
                                "a", 5242880, 3))

    return config
        
def _logException(msg):
    traceback.print_exc(file=sys.stderr)
    log.exception(msg)

def _terminate(code):
    if code:
        log.error("s3fs terminated with error")
    else:
        log.info("s3fs terminated")
    sys.exit(code)

class S3Inode(object):
    """
    Class used to store s3fs inode details
    inode_0 is for metadata 
    inode_1 ... stores the actual file data each with fixed block size
    size of inode is expressed as the TOTAL of the sum of all data
    therefore, number of data blocks = size/block_size + (size > 0)

    Note: we don't do dnode cache meaning there is no data associated with
    each inode instance, only metadata, caching may be implemented in the
    future
    """

    _attributes = ['ino', 'mode', 'dev', 'nlink', 'uid', 'gid', 'size',
                    'atime', 'mtime', 'ctime', 'blocksize', 'block',
                    'compress', 'encrypt' ] 
    _inodeCache={}
    _dirtyList={}

    def __init__(self, ino):
        my_dict = self.__dict__
        for x in self._attributes: my_dict[x] = 0
        self.blocksize = s3Link.blocksize
        self.compress = s3Link.compress
        self.encrypt = s3Link.encrypt
        self.uid = UID
        self.gid = GID
        self.data=dict(meta={},content={})
        self.ro = False
        self.in_transit={}
        self.dirty={}
        self.needs_flush=False
        self.last_lazy={}

        if ino == -1:
            #create new inode using datetime, can also be 
            #other means like some random number
            #self.ino = int(time.mktime(time.gmtime()))
            self.ino = rand.randint(1,sys.maxint)
        else:
            log.debug("S3Inode: inodeCache(%s)" %(self._inodeCache.keys()))
            if self._inodeCache.has_key(ino):
                log.debug("S3Inode: ino(%i) in cache" % (ino,))
            else:
                log.debug("S3Inode: trying to get inode(%i) from server" % (ino,))
                self.readInode(ino)

    @classmethod
    def Flush(cls,force=False):
        t = cls._dirtyList.keys()
        for ino in t:
            try:
                inode = cls._inodeCache[ino]['inode']
                if inode.needs_flush:
                    log.debug("S3Inode: flushing ino(%i)" % (inode.ino,))
                    if not force: inode.update(flush=(LazyWrite > 1 and LazyWrite or True))
                    else: inode.update(True)
            except KeyError: pass

    @classmethod
    def GetInode(cls, ino):
        now = time.time()
        try: 
            if ino == -1: raise KeyError
            c = cls._inodeCache[ino]
            if Cache_Policy == CACHE_OBSERVER and now - c['live'] > Observe_Freq:
                log.debug("S3Inode: cached(%i) expired" % (ino,))
                del cls._inodeCache[ino]
                raise KeyError

            log.debug("S3Inode: cached(%i, %i) " % (ino,c['inode'].mode))
            return c['inode']
        except KeyError:
            x = cls(ino)
            if x.ino != -1: cls._inodeCache[x.ino]=dict(live=now, inode=x)
            return x
        
    @classmethod
    def CacheFlush(cls, cache, prefix):
        """
        this would read all the existing cache and either flush them
        up to S3 or remove them(in case of observer). cache content
        is supposed to be work in progress which in general use should
        not be updated to S3, and this is usually done only on either
        mount or umount
        """
        def _exclude(x):
            for a in ["_s3", "_remove", "_transit", "_lazy", "_reloading"]:
                if x.endswith(a): return True
            return False

        for x in os.listdir(cache):
            if not x.startswith(prefix) or _exclude(x): continue
            path = cache + "/" + x
            bucket, fs_prefix, n_prefix, ino, block = x.split("_", 4)
            ino = int(ino)
            block = int(block)
            log.info("S3Inode.CacheFlush: found(%i, %i)" % (ino, block))
            inode = cls.GetInode(ino)
            if inode.ino == ino:
                log.info("S3Inode.CacheFlush: flushing %s to S3" % (x,))
                if block:
                    cache = self.cacheFile(block)
                    if cache:
                        inode.writeDnode(block-1,[],lazy=False)
                    else:
                        try:
                            f = open(path)
                            b = list(f.read())
                            f.close()
                            inode.writeDnode(block-1,b,lazy=False)
                        except IOError: pass
                else:
                    inode.update(flush=True)
            else:
                log.info("S3Inode.CacheFlush: %s has no S3 version, cache removed" % (x,))

            try: os.unlink(path)
            except OSError: pass

    def filter_file(self, src, dest, nonce,out=True):
        """
        this function encrypt/decrypt from src to dest
        return the src and dest md5 hash
        """
        if nonce:
            arc4 = ARC4(s3Link.encryptionKey, nonce)
            crypt = arc4.crypt
        else:
            crypt = lambda x: x

        o_hash=md5.new()
        n_hash=md5.new()
        if out: 
            if self.compress:
                z = zlib.compressobj()
                fz = z.compress
                flush = z.flush
            else:
                fz = lambda x: x
                flush = lambda : None
        else: 
            #we don't know what input it is
            #always try decompress first
            z = zlib.decompressobj()
            fz = z.decompress
            flush = z.flush

        buf_size = 32767
        f1 = open(src,"rwb+")
        f2 = open(dest,"wb+")

        if out:
            x = f1.read(buf_size)
            while x:
                o_hash.update(x)
                try: x = fz(x)
                except zlib.error: pass
                y = ''.join(crypt(x))
                n_hash.update(y)
                f2.write(y)
                x = f1.read(buf_size)  

            try:
                l = flush() 
                if l: 
                    y = ''.join(crypt(l))
                    n_hash.update(y)
                    f2.write(y)
            except zlib.error: pass

        else:
            x = f1.read(buf_size)

            while x:
                o_hash.update(x)
                y = ''.join(crypt(x))
                try: y = fz(y)
                except zlib.error: pass
                n_hash.update(y)
                f2.write(y)
                x = f1.read(buf_size)        

            try:
                l = flush() 
                if l: 
                    n_hash.update(l)
                    f2.write(l)
            except zlib.error: pass

        f1.close()
        f2.close()
        return (o_hash.hexdigest(), n_hash.hexdigest())

    def xor(self, str, nonce):
        """
        this function encrypt the str by xor it with a RC4 random stream which
        if used properly is highly effective and efficient, the essence is,
        the key must not be used twice, thus the nonce(random number) which
        must be stored with the data(somewhere) for proper decrypt
        """
        if not nonce: return str
        arc4 = ARC4(s3Link.encryptionKey, nonce)
        return arc4.crypt(str)

    def _filterin(self, str):
        try:
            if self.compress: return zlib.decompress(str)
            else: return str
        except zlib.error, e:
            log.warning("_filterin: can't decompress (%s)", e)
            return str

        
    def _filterout(self, str):
        if self.compress: return zlib.compress(str)
        else: return str
        
    def _data_pickle(self, src=None):
        if not src:
            content = self.data['content'].items()
            content.sort()
            meta = self.data['meta'].items()
            meta.sort()
            data = "dict(%s)\ndict(%s)" % (str(meta), str(content))
            return data
        else:
            try:
                meta,content= src.split("\n")
                self.data['meta'] = eval(meta, dict(__builtins__={}), dict(dict=dict))
                self.data['content'] = eval(content, dict(__builtins__={}), dict(dict=dict))
            except: raise cPickle.UnpicklingError 

    def cacheFile(self, block=1, force=False):
        """
        return cache file name, or None
        """
        if self.blocksize < BLOCK_NEEDS_LOCAL_CACHE and not force: return None
        key = _mkInodeKey(self.ino, block)
        return "%s/%s_%s" % (CacheDir.rstrip("/"), s3Link.bucket.name, key.replace("/","_"))

    def cacheNode(self, block=1):
        """
        cache inode_block content to local cache location
        if it already exist, always assume it is newer than S3 version and do
        nothing except when we are observer
        """
        file =  self.cacheFile(block, True)
        try: 
            os.utime(file, None) #refresh utime to hold it longer
            if Cache_Policy == CACHE_OBSERVER:
                key = _mkInodeKey(self.ino, block)
                try:
                    bits = s3Link.get_head(key)
                    try: nonce = bits.metadata['nonce']
                    except KeyError: nonce = None
                    try:  old_md5 = bits.metadata['md5']
                    except (KeyError, AttributeError): old_md5 = None
                    s_hash,o_hash = self.filter_file(file, os.devnull, nonce)
                    if s_hash != old_md5:  
                        log.debug("S3Inode.cacheNode: cached node %s(%s) expired " %(self.ino, key))
                        try: os.unlink(file)
                        except OSError: pass
                        e = OSError("No such file or directory")
                        e.errno = ENOENT
                        raise e #fall through as if cache not exist
                    else:
                        log.debug("S3Inode.cacheNode: inode %s(%s) match S3 version" %(self.ino, key))
                        return 0
                except KeyError:
                    log.warning("S3Inode.cacheNode: dnode %s(%s) not on server, observer removing local cache" %(self.ino, key))
                    #as an observer, we need to remove the cache
                    try: os.unlink(file)
                    except OSError: pass
                    return 1
        except OSError, e:
            if e.errno == ENOENT: 
                key = _mkInodeKey(self.ino, block)
                try: 
                    bits = s3Link.get_head(key)
                    try: nonce = bits.metadata['nonce']
                    except KeyError: 
                        nonce = None
                    except AttributeError:
                        raise KeyError
                    if not nonce:
                        s3Link.get(bits, file)
                    else:
                        s3Link.get(bits, file+"_s3")
                        s_hash,o_hash = self.filter_file(file+"_s3", file, nonce, out=False)
                        log.debug("S3Inode.cacheNode: node(%s) hash(%s,%s)" %(key, s_hash, o_hash))
                        os.unlink(file+"_s3")
                except KeyError:
                    log.warning("S3Inode.cacheNode: dnode %s(%s) not on server, assume hole" %(self.ino, key))
                    #sparse support, just create one empty block with zeros
                    f = open(file,"wb+")
                    f.seek(self.blocksize-1)
                    f.write("\0")
                    f.close()
            else: 
                log.error("S3Inode.cacheNode: file access error(%s), %(s)" % (file, str(e)))
                return 1
        return 0

    def cacheInode(self, bits):
        cache = self.cacheFile(0)
        data = self._data_pickle()
        hash = md5.new(data).hexdigest()
        if hash != bits.metadata['md5']:
           log.warn("S3Inode.cacheInode: ino(%i) hash not match(%s,%s)" % (self.ino,hash, bits.metadata['md5']))
        try:
            f = open(cache,"wb")
            f.write(data)
            f.close()
        except (TypeError, IOError): pass

    def readInode(self,ino):
        """
        Load S3 bits info from bucket 
        """
        key = _mkInodeKey(ino, 0)
        bits = S3Key.Key()
        bits.key = key
        from_cache = False
        try:
            cache = self.cacheFile(0)
            try:
                f = open(cache,"rb")
                data = f.read()
                f.close()
                from_cache = True
            except (TypeError, IOError, OSError): 
                log.debug("S3Inode.readInode: Requesting inode(%s) from server: " %(key))
                bits,data = s3Link.get(bits)
                # unpickle the content
                try: nonce = bits.metadata['nonce'] #see if it is encrypted
                except KeyError: nonce = None
                data = self._filterin(''.join(self.xor(data,nonce)))

            try: self._data_pickle(data)
            except cPickle.UnpicklingError: 
                log.error("S3Inode.readInode: failed to access inode(%i)" % (ino,))
                self.ro = True
                self.data=dict(meta={},content={})
            my_dict = self.__dict__
            for x in self._attributes: 
                #try: my_dict[x] = int(bits.metadata[x])
                try: my_dict[x] = self.data['meta'][x]
                except KeyError: pass
            if not from_cache: self.cacheInode(bits) #update cache
        except KeyError:
            log.debug("S3Inode: inode %s(%s) not on server: " %(ino, key))
            self.ino = -1
            
    def readDnode(self, block):
        """
        Load data of block(start from 0) from S3 as list or cache file handle
        return empty block
        """
        if _blocks_needed(self.size, self.blocksize) < block + 1 or \
            self.size == 0:
            return list("\0"*self.blocksize)
            
        cache = self.cacheFile(block+1)
        if cache:
            self.cacheNode(block+1)
            return cache
        else:
            key = _mkInodeKey(self.ino, block+1)
            bits = S3Key.Key()
            bits.key = key
            try:
                bits,data = s3Link.get(bits)
            except KeyError:
                log.debug("inode %s(%s) not in bucket: " %(self.ino, key))
                return list("\0"*self.blocksize)

            try: nonce = bits.metadata['nonce'] #see if it is encrypted
            except KeyError: nonce = None
            data = self._filterin(''.join(self.xor(data,nonce)))
            return list(data)

    def file_in_transit(self, path, hash, nonce=None, lazy=False):
        """
        create a "in-transit" file
        nonce is needed if the data is encrypted
        """
        try: nonce = binascii.b2a_hex(nonce)
        except TypeError: nonce="None"
        if not lazy:
            p = "%s_%s_%s_transit" % (path, hash, nonce)
        else:
            p = "%s_%s_%s_lazy" % (path, hash, nonce)

        return p

    def send_file(self, key, file, o_hash, nonce, block):
        """
        send file to S3
        """
        bits = S3Key.Key()
        bits.key = key
        bits.metadata['md5'] = o_hash
        bits.metadata['mtime'] = str(self.mtime)
        bits.metadata['compress'] = str(self.compress)
        if nonce: bits.metadata['nonce'] = nonce

        old_md5, old_tag = self.getNodeHash(key)
        if o_hash != old_md5:
            self.in_transit[block] = file
            try:
                s3Link.set_file(bits, file)
                del self.in_transit[block]
                try: os.unlink(file)
                except OSError: pass
            except (IOError, OSError), e:
                log.error("S3Inode.send_file: failed to upload %s to S3(%s)", (file, str(e)))
        else:
            log.debug("S3Inode.send_file: cache matches S3 version, skipped")
            

    def getNodeHash(self, key):
        try: 
            bits = s3Link.get_head(key)
            try: old_md5 = bits.metadata['md5']
            except KeyError: old_md5 = ""
            try: etag = bits.etag.strip("\"")
            except AttributeError: etag=""
        except (AttributeError, KeyError): 
            log.debug("S3Inode.writeDnode: block not on server(%s)" % (key,))
            old_md5 = ""
            etag = ""
        return (old_md5, etag)

    def _remove_lazy(self, block):
        """
        remove lazy in transit block
        and return non-zero if something is already in flight
        """
        try:
            last_lazy = self.last_lazy[block]
            try: os.unlink(last_lazy)
            except OSError: pass
            last_lazy_reloading = last_lazy + "_reloading"
            try: 
                os.stat(last_lazy_reloading)
                log.info("S3Inode._remove_lazy: block is already in flight(%s)" % (last_lazy_reloading,))
                return 1
            except OSError, e:
                if e.errno != ENOENT: 
                    log.warn("S3Inode._remove_lazy: in flight checking error(%s,%s)" % (last_lazy_reloading, str(e)))
                    return 1
            del self.last_lazy[block] 
        except KeyError: pass
        key = _mkInodeKey(self.ino, block)
        f = "%s/%s_%s_None_None_remove" % (CacheDir.rstrip("/"), s3Link.bucket.name, key.replace("/","_"))
        try: 
            os.stat(f)
            log.info("S3Inode._remove_lazy: delete block is already in flight(%s)" % (f,))
            os.unlink(f)
        except OSError: pass

    def writeDnode(self, block, list_buf, lazy=False):
        """
        Write data out to data node on S3
        block is the block number, starting from 0
        list_buf must be a list and would be truncated to blocksize
        """
        if self.ro: return 1

        try:
            #already have something in transit
            in_transit = self.in_transit[block+1]
            try: os.stat(in_transit)
            except OSError, e:
                if e.errno == ENOENT:
                    del in_transit[key]
                    raise KeyError
            #just fake the write and wait for next round or unmount
            #mark dirty
            self.dirty[block+1]=True
            return 0
        except KeyError: pass

        key = _mkInodeKey(self.ino, block + 1) #0 is actually _1 ...

        if self.encrypt: nonce = str(random.randint(1,maxll))
        else: nonce = None
        
        cache = self.cacheFile(block+1)
        if cache:
            file = cache
            out = self.file_in_transit(file, md5.new(nonce).hexdigest(), nonce)
            o_hash, n_hash = self.filter_file(file, out, nonce)
            new_out = self.file_in_transit(file, o_hash, nonce)
            os.rename(out, new_out)
            log.debug("S3Inode.writeDnode: plain hash(%s), S3 hash(%s)" % (o_hash,n_hash))
            out = new_out
            if not lazy:
                if self._remove_lazy(block+1): 
                    """
                    something already in flight, we have to skip this round
                    """
                    try: os.unlink(out)
                    except OSError: pass
                    return 1 
                if self.send_file(bits, out, block+1):
                    log.error("S3Inode.writeDnode: %s upload failed" % (out, ))
                    return 1
                log.debug("S3Inode.writeDnode: %s uploaded" % (out,))
            else:
                new_out = self.file_in_transit(file, o_hash, nonce, lazy=True)
                try: 
                    try: 
                        last_lazy = self.last_lazy[block+1]
                        os.stat(last_lazy)
                        if self._remove_lazy(block+1):
                            try: os.unlink(out)
                            except OSError: pass
                            return 1
                        log.info("S3Inode.writeDnode: lazy transit(%s) already exist, remove it" % (last_lazy,))
                        raise KeyError
                    except OSError, e:
                        if e.errno == ENOENT: raise KeyError
                        else: 
                            log.error("S3Inode.writeDnode: lazy transit error(%s)" % (str(e),))
                except KeyError: 
                    os.rename(out, new_out)
                    self.last_lazy[block+1] = new_out
                    log.debug("S3Inode.writeDnode: lazy transit(%s) prepared from (%s)" % (new_out,out))
        else:
            if self._remove_lazy(block+1): return 1
            bits = S3Key.Key()
            bits.key = key
            data = ''.join(list_buf[:self.blocksize])
            o_hash = md5.new(data).hexdigest()
            old_md5, old_tag = self.getNodeHash(key)
            if o_hash != old_md5:
                bits.metadata['md5'] = o_hash
                bits.metadata['compress'] = str(self.compress)
                bits.metadata['mtime'] = str(self.mtime)
                data = self._filterout(data)
                if nonce: bits.metadata['nonce'] = nonce
                data = ''.join(self.xor(data, nonce))
                s3Link.set(bits, data)
            else:
                log.debug("S3Inode.writeDnode: cache matches S3 version")

        try: del self.dirty[block+1]
        except KeyError: pass
        return 0
            
    def update(self, flush=False):
        """
        Sync's the state of this inode back to S3
        """
        if self.nlink < 1: return 0#unclaimed inode
        if self.ro: return 1
        self.atime = self.ctime = self.mtime = int(time.mktime(time.gmtime()))

        if self.encrypt: nonce = str(random.randint(1,maxll))
        else: nonce = None

        key = _mkInodeKey(self.ino, 0)
        bits = S3Key.Key()
        bits.key = key
        if nonce: bits.metadata['nonce'] = nonce
        my_dict = self.__dict__
        for i in self._attributes: 
            self.data['meta'][i] = my_dict[i]
        bits.metadata['mtime'] = str(self.mtime)
        bits.metadata['md5'] = md5.new(self._data_pickle()).hexdigest()
        data= ''.join(self.xor(self._filterout(self._data_pickle()),nonce))
        if self.mode & S_IFDIR: self.size = _blocks_needed(len(data),1024)*1024

        #this is the actual update
        cache = self.cacheFile(0)
        self.cacheInode(bits) #update cache
        if flush is True or not LazyWrite: 
            if self._remove_lazy(0): 
                self.needs_flush = True
                self._dirtyList[self.ino] = self
                return 1
            self.needs_flush = False
            try: del self._dirtyList[self.ino]
            except KeyError: pass
            s3Link.set(bits, data)
            #if (self.mode & 0777) == 0777 and not (self.mode & S_IFLNK) and not (self.mode & S_IFDIR): 
            if (self.mode & 0777) == 0777 and (self.mode & S_IFREG) and (self.mode & S_IFLNK) != S_IFLNK:
                log.debug("S3Inode.update: map 0777 to public-read for key(%s)" %(key,))
                bits.set_acl("public-read")
        else:
            if flush and cache: #very lazy
                log.debug("S3Inode.update: lazy flush(%i)" %(self.ino, ))
                o_hash = bits.metadata['md5']
                out = self.file_in_transit(cache, o_hash, nonce)
                new_out = self.file_in_transit(cache, o_hash, nonce, lazy=True)
                try: 
                    try:
                        last_lazy = self.last_lazy[0]
                        os.stat(last_lazy) #pending one, just assume nothin is flushed
                        if self._remove_lazy(0): 
                            try: os.remove(out)
                            except OSError: pass
                            self.needs_flush = True
                            self._dirtyList[self.ino] = self
                            return 1
                        log.info("S3Inode.update: lazy transit(%s) already exist, remove it" % (last_lazy,))
                        raise KeyError
                    except OSError, e: 
                        if e.errno == ENOENT: raise KeyError
                        else: 
                            self.needs_flush = True
                            self._dirtyList[self.ino] = self
                            return 1
                except KeyError:
                    f = open(out,"wb")
                    f.write(data)
                    f.close()
                    try:
                        os.rename(out, new_out)
                        self.last_lazy[0] = new_out
                        self.needs_flush = False
                        try: del self._dirtyList[self.ino]
                        except KeyError: pass
                    except OSError, e: 
                        log.error("S3Inode.update: lazy update(%s)" %(str(e),))
            else:
                log.debug("S3Inode.update: lazy (%i)" %(self.ino, ))
                self.needs_flush = True
                self._dirtyList[self.ino] = self

        log.debug("S3Inode.update: key(%s), inode(%i)" %(key,self.ino))
        return 0

    def removeCache(self):
        blocks = _blocks_needed(self.size, self.blocksize)
        for x in xrange(blocks):
            cache = self.cacheFile(x+1)
            if cache:
                try: os.emove(cache)
                except OSError: pass

    def truncate(self, size):
        """
        trim the inode to size, thus need to release the excess blocks
        """
        if self.ro: return 1

        oldsize = self.size
        self.size = size
        newblocks = _blocks_needed(size, self.blocksize)
        oldblocks = _blocks_needed(oldsize,self.blocksize)
        log.debug("S3Inode.truncate: oldblock(%i), newblock(%i)" % (oldblocks, newblocks)) 
        if self.size == 0: newblocks = 0 #to save one last block
        for i in xrange(newblocks, oldblocks): 
            key = _mkInodeKey(self.ino, i+1)
            cache = self.cacheFile(i+1)
            if cache:
                try: os.unlink(cache)
                except OSError: pass
            self._remove_lazy(i)
            self._remove_node(key)

    def mark_dirty(self, block):
        """
        mark the block as dirty, which may need flush
        """
        self.dirty[block]=True

    def link(self, path, nlinks=1):
        """
        link path to this inode
        currently only increment the link count
        path can be:
            fullpath means that path(file or dir) link to this inode
            filename means the file entry is added to the directory of
            this inode
        """
        self.nlink += nlinks
        log.debug("S3Inode.link: link inode(%i) to path(%s) with nlinks(%i)" % (self.ino, path, nlinks))

        return 0

    def unlink(self, path, nlinks=1):
        """
        Unlink path from the inode
        path can be:
            fullpath means that path(file or dir) is unlink from this inode
            filename means the file entry is remove from the directory of
            this inode
        Delete this inode(and associated dnodes) when nlink < 1
        Otherwise, just update
        """
        log.debug("unlink path(%s) from inode(%i) with links(%i)" % (path,
                    self.ino, self.nlink))
        self.nlink-=nlinks
            
        if self.nlink<1:
            blocks = _blocks_needed(self.size,self.blocksize)
            for i in xrange(blocks+1):
                key = _mkInodeKey(self.ino, i)
                self._remove_lazy(i)
                self._remove_node(key)
                try:
                    cache = self.cacheFile(i)
                    if cache: os.unlink(cache)
                except OSError,e: pass
            self.size = 0
            try: del self._inodeCache[self.ino]
            except KeyError: pass
        else:
            log.debug("S3Inode.unlink: update inode(%s) with nlink(%i)" % (self.ino, self.nlink))

    def _remove_node(self, key, lazy=True):
        """
        remove a node from S3
        """
        if lazy:
            f = "%s/%s_%s_None_None_remove" % (CacheDir.rstrip("/"), s3Link.bucket.name, key.replace("/","_"))
            try: 
                x = open(f,"w")
                x.close()
            except IOError: pass
            log.debug("S3Inode._remove_node: inode(%s) deleted" % (f,))
        else:
            try:
                s3Link.remove(key)
                log.debug("S3Inode.unlink: deleting inode(%s):" % (key,))
            except KeyError:
                pass
        
class OpenFile(object):
    """
    Class holding any currently open files, includes cached instance of the
    last data block retrieved this is the class that does the file stream to
    underlying block storage device mapping like breaking a multi-G file into
    chunks of smaller file/bits stored in Amazon S3 or into smaller multiple
    mail message in gmail

    two seperate buffers(of blocksize) are held, one for writing another
    optional one for reading. reading will always read from the fresh writing
    buffer but if the reading are from another block, the writing buffer would 
    not be flushed or reloaded
    """

    def __init__(self, inode):
        self.tmpfile = None
        self.inode = inode
        self.needsReading = 1
        self.needsWriting = 0
        self.needsUpdate = 0
        self.blocksize = inode.blocksize
        self.currentOffset = -1
        self.lastBlockRead = [-1,-1]
        self.lastBlockBuffer = [[],[]]
        self.buffer = None
        self.lastWrite = 0
        self.lastFlush = 0

    def openCache(self, file, mode="rwb+"):
        """
        open cache file with mode, return the open handle
        """

        if self.tmpfile: self.closeCache()

        _ , name = os.path.split(file)
        try: os.utime(file, None)
        except OSError: pass
        try: 
            self.tmpfile = open(file, mode)
            fcntl.flock(self.tmpfile.fileno(), fcntl.LOCK_SH)
        except IOError, e:
            if e.errno == ENOENT: 
                self.tmpfile = open(file, "wb+")
                fcntl.flock(self.tmpfile.fileno(), fcntl.LOCK_SH)
            else: raise e
        global ActiveFiles
        try:
            ActiveFiles[name] += 1
        except KeyError:
            ActiveFiles[name] = 1

        return self.tmpfile

    def closeCache(self):
        """
        close cache file
        """
        try: file = self.tmpfile.name
        except AttributeError: return None

        _ , name = os.path.split(file)
        fcntl.flock(self.tmpfile.fileno(), fcntl.LOCK_UN)
        self.tmpfile.close()
        try: os.utime(file, None)
        except OSError: pass
        global ActiveFiles
        try: 
            ActiveFiles[name] -= 1
            if ActiveFiles[name] == 0: 
                del ActiveFiles[name]
        except KeyError: pass
        self.tmpfile = None

    def close(self):
        """
        Closes this file by committing any changes to underlying inode
        """
        self.flushBuffer()
        if self.needsUpdate:
            self.inode.truncate(self.inode.size) #remove excess dblocks
            self.inode.update()
        if Cache_Policy == CACHE_REMOVE_ON_CLOSE: self.inode.removeCache()
        self.currentOffset = -1
        self.lastBlockRead = [-1,-1]
        self.lastBlockBuffer = [[],[]]
        self.buffer = None
        return 0

    def truncate(self, size):
        """
        Truncate an open file to size
        """
        self.inode.size=size
        self.needsUpdate = 1

        block = _block_no(size, self.blocksize)

        #invalid read buffer
        self.lastBlockRead = [-1,-1] 
        self.lastBlockBuffer = [[],[]]

        if self.currentOffset != -1:
            currentBlock = _block_no(self.currentOffset, self.blocksize)
            newblock = _block_no(size, self.blocksize)
            if currentBlock > newblock: 
                #whatever is there would be discarded
                self.buffer = None
                self.currentOffset = -1
                self.needsWriting = 0
            elif currentBlock == newblock and self.currentOffset > size:
                #reposition to size
                self.currentOffset = size
                
    def flushBuffer(self, close_cache=True, lazy=None):
        """
        Write out our buffer to underlying dnode and/or close the tmpfile
        """
        if lazy==None: lazy = LazyWrite
        currentBlock = _block_no(self.currentOffset, self.blocksize)
        if currentBlock < 0: return 0

        if self.needsWriting:
            if self.tmpfile: path = self.tmpfile.name
            else: path = None
            self.closeCache()
            log.debug("OpenFile.flushBuffer: block(%i)" % (currentBlock,))
            r = self.inode.writeDnode(currentBlock, self.buffer, lazy=lazy)
            if not close_cache and path: self.openCache(path)
            if not r: self.needsWriting = 0
            self.lastFlush = time.time()
        return 0

    def readBlock(self, block):
        """
        read block from underlying(or current write buffer) and return the
        list buffer(done by inode), this only handle in-memory cached blocks
        not file backed blocks
        """
        if self.currentOffset != -1 and \
            _block_no(self.currentOffset,self.blocksize) == block: 
            # return the current buffer if that is the same block
            return self.buffer

        #search in cache
        for p,k in enumerate(self.lastBlockRead):
            if block == k: 
                log.debug("OpenFile.readBlock: block(%i) in cache" % (block,))
                return self.lastBlockBuffer[p]

        for p,k in enumerate(self.lastBlockRead):
            if k == -1 or abs(k - block) > 1: 
                log.debug("OpenFile.readBlock: block(%i) from underlying,cache(%s)" % (block,str(self.lastBlockRead)))
                self.lastBlockBuffer[p] = self.inode.readDnode(block)
                self.lastBlockRead[p] = block
                return self.lastBlockBuffer[p]

        log.debug("OpenFile.readBlock: block(%i) from underlying, cache(%s)" % (block,str(self.lastBlockRead)))
        self.lastBlockBuffer[0] = self.inode.readDnode(block)
        self.lastBlockRead[0] = block
        return self.lastBlockBuffer[0]

    def write(self, buf, off):
        """
        Write data to file from buf, offset by off bytes into the file
        """

        buflen = len(buf)
        blocksize = self.blocksize
        blocks = list(_blocks_spread(off, buflen, blocksize))
        wlen = 0
        for (b, o, s) in blocks:
            cache = self.inode.cacheFile(b+1)
            log.debug("OpenFile.write: block(%i), offset(%i), size(%i)" % (b, o, s))
            if cache:
                if not self.tmpfile or self.tmpfile.name != cache:
                    self.flushBuffer()
                    self.inode.readDnode(b)
                    self.openCache(cache)
                f = self.tmpfile
                f.seek(o)
                f.write(''.join(buf[wlen:wlen+s]))
            else:
                cb = _block_no(self.currentOffset, blocksize)
                log.debug("OpenFile.write: cb(%i), c_offset(%i)" % (cb, self.currentOffset))
                if cb != b:
                    self.flushBuffer()
                    self.buffer = self.inode.readDnode(b)
                self.buffer[o:o+s] = buf[wlen:wlen+s]
            wlen += s
            self.inode.mark_dirty(b)

        self.currentOffset = off + wlen
        self.needsWriting = 1
        self.needsUpdate = 1
        if off + wlen > self.inode.size:
            self.inode.size=wlen+off


        return wlen

    def read(self, readlen, off):
        """
        Read readlen bytes from an open file from position offset bytes into the files data
        """
        readlen = min(self.inode.size - off, readlen)
        buf = list('\0'*readlen)
        blocksize = self.blocksize
        blocks = list(_blocks_spread(off, readlen, blocksize))
        rlen = 0
        for (b, o, s) in blocks:
            cache = self.inode.cacheFile(b+1)
            log.debug("OpenFile.read: rlen(%i), block(%i), offset(%i), size(%i)" % (rlen, b, o, s))
            if cache:
                if not self.tmpfile or self.tmpfile.name != cache:
                    self.inode.readDnode(b)
                    self.openCache(cache)
                f = self.tmpfile
                f.seek(o)
                buf[rlen:rlen+s] = list(f.read(s))
            else:
                b_buf = self.readBlock(b)
                buf[rlen:rlen+s] = b_buf[o:o+s]
            rlen += s

        return buf[:rlen]

class S3LinkException(Exception): 
    def __init__(self): self.errno = EREMOTEIO

class S3Link(object):
    """
    this class is created to handle traffic to and from S3 mainly because the
    connection seems to be not stateful so sometimes it may fail and requires
    reconnection/retry
    """
    _bandwidth_counter = AtomicCounter()

    def __init__(self, bucketname, blocksize=1*1024*1024, aws_key=None,
                aws_secret=None, encryptionKey=None, compress=1, encrypt=1,
                fs_prefix="s3fs"):
        self.retry = 10
        self.bucketname = bucketname
        self.aws_key=aws_key
        self.aws_secret=aws_secret
        self.compress=compress
        self.encrypt=encrypt
        self.key_remover = None

        if encryptionKey and encryptionKey != "prompt":
            self.encryptionKey = md5.new(encryptionKey).digest()
            log.info("Mount option: encryption key supplied")
        else:
            log.info("Mount option: no encryption key specified, use default")
            self.encryptionKey = None
        """
        there should be a way to store this in the bucket, but we
        manually assigned them for now 
        fs_prefix is there so multiple s3fs can live within the same bucket
        """
        self.blocksize = blocksize
        self.inode_prefix = "inode"
        self.fs_prefix = fs_prefix
        log.info("Mount option: encrypt=%i, compress=%i, blocksize=%i, fs_prefix=%s" % \
                (self.encrypt, self.compress, self.blocksize, self.fs_prefix))

    def retry_wrapper(f):
        """
        this function wraps all S3 links so it can retry if fail
        """
        def _f(self, *argv, **kw):
            for x in xrange(self.retry):
                try: return f(self, *argv, **kw)
                except httplib.ResponseNotReady, e:
                    log.warning("S3Link: ResponseNotReady, try to reconnect(%s)", (str(e),))
                    self.connect()
                except httplib.CannotSendRequest, e:
                    log.warning("S3Link: CannotSendRequest, try to reconnect(%s)", (str(e),))
                    self.connect()
                except httplib.BadStatusLine, e:
                    log.warning("S3Link: BadStatusLine, try to reconnect(%s)", (str(e),))
                    self.connect()
                except httplib.IncompleteRead, e:
                    log.warning("S3Link: IncompleteRead, try to reconnect (%s)", (str(e),))
                    self.connect()
                except socket.error, e:
                    log.warning("S3Link: socket error, try to reconnect(%s)", (str(e),))
                    self.connect()
                except S3.S3ResponseError, e:
                    if e.status == 500: 
                        log.warning("S3Link: warning trancient AWS server error, would retry")
                    elif e.status == 404: raise KeyError
                    else: 
                        log.warning("S3Link: warning, error response from S3, try to connect(%s)" % (str(e),))
                        self.connect()
                except S3DataError, e:
                    log.warning("S3Link: content error(%s, would retry)" % (str(e),)) 
                except (ValueError, EOFError, NameError), e:
                    #there is a bug in boto which may result in NameError
                    log.warning("S3Link: some unknown error, would retry(%s)" % (str(e),)) 
                    self.connect()
                log.warning("S3Link: retrying function(%s), %i retry" % (f.func_name, x+1))

            log.warning("S3Link: operation failed after %i retry" % (self.retry,))
            raise S3LinkException

        return _f

    def get(self, bits, file=None):
        bits.bucket = self.bucket
        log.debug("S3Link.get(%s): retreiving %s from S3 to %s" % (str(self.bucket.connection),bits.key, str(file))) 
        try:
            if file: 
                s = file
                if type(file)==type(""):
                    bits.get_contents_to_filename(file)
                    try: bits.size
                    except AttributeError: raise KeyError
                    f = open(file,"rb")
                    hash = md5.new(f.read()).hexdigest()
                    l = f.tell()
                    f.close()
                    if l != int(bits.size): raise S3DataError("received data length not match")
                    self._bandwidth_counter.inc(l)
                else:
                    bits.get_contents_to_file(file)
                    try: bits.size
                    except AttributeError: raise KeyError
                    file.seek(0)
                    hash = md5.new(file.read()).hexdigest()
                    l = file.tell()
                    if l != int(bits.size): raise S3DataError("received data length not match")
                    self._bandwidth_counter.inc(l)
                log.info("S3Link.get(%s): retreived %s from S3 to %s(%i)" % (str(self.bucket.connection),bits.key, str(file), l)) 
                return (bits, file)
            else: 
                s = bits.get_contents_as_string()
                try: bits.size
                except AttributeError: raise KeyError
                log.debug("S3Link.get: data type(%s)" % (type(s), )) 
                hash = md5.new(s).hexdigest()
                if len(s) != int(bits.size): 
                    raise S3DataError("received data length not match")
                log.info("S3Link.get(%s): retreived %s from S3, len(%i)" % (str(self.bucket.connection),bits.key, len(s))) 
                self._bandwidth_counter.inc(len(s))
                return (bits, s)
        except AttributeError: raise S3DataError("received data is corrupted")
         
    get = retry_wrapper(get)

    def get_head(self, key):
        """
        the underlying boto call can return nothing even it is just network
        error, so we would put a retry here
        """
        log.debug("S3Link.get_head(%s): retreiving %s header from S3" % (str(self.bucket.connection), key)) 
        for x in xrange(3):
            r = self.bucket.lookup(key)
            if not r: raise KeyError
            else: return r
        #log.warning("S3Link.get_head: nothing returned for (%s), retry(%i)" % (key,x+1 )) 
        raise KeyError

        log.debug("S3Link.get_head: header retrieved(%s)" % (key, )) 
    get_head = retry_wrapper(get_head)

    def set_file(self, bits, file):
        log.debug("S3Link.set_setfile(%s): saving %s to S3 from %s" % (str(self.bucket.connection), bits.key, str(file))) 
        bits.bucket = self.bucket
        if type(file)==type(""):
            bits.set_contents_from_filename(file)
        else:
            bits.set_contents_from_file(file)
        self._bandwidth_counter.inc(bits.size)
    set_file = retry_wrapper(set_file)
        
    def set(self, bits, data):
        log.info("S3Link.set(%s): saving %s to S3, len(%i)" % (str(self.bucket.connection), bits.key, len(data))) 
        bits.bucket = self.bucket
        bits.set_contents_from_string(data)
        self._bandwidth_counter.inc(bits.size)
    set = retry_wrapper(set)

    def remove(self, key, background=False):
        if self.key_remover and background:
            log.info("S3Link.set: remove %s from S3, in the background" % (key, )) 
            self.key_remover.write("remove=%" % (key,))
        else: 
            log.debug("S3Link.set: remove %s from S3" % (key, )) 
            self.bucket.delete_key(key)
        log.debug("S3Link.set(%s): remove %s from S3" % (str(self.bucket.connection),key )) 
        self.bucket.delete_key(key)
    remove = retry_wrapper(remove)

    def connect(self):
        """
        connect to S3 service
        this is in a seperate call as it seems that python's httplib even
        though is supposed to be stateless(?) is stateful. It happens on my
        notebook that if I hibernate and wakeup, I can no longer use the same
        connection
        """

        connection = S3.S3Connection(self.aws_key, self.aws_secret)
        try:
            if self.bucketname: bucketname = self.bucketname
            else: self.bucketname = bucketname = _mkBucketName("s3fs", connection.aws_access_key_id)
            self.bucket = S3.Bucket(connection, bucketname)
            x = self.bucket.get_acl()
            if x: #force a retrieve to test the connection
                log.info("Connected to Amazon S3 using bucket %s" % (self.bucket.name,))

            if self.encryptionKey == None:
                self.encryptionKey = connection.aws_secret_access_key

        except S3.S3ResponseError, e:
            if e.status == 403: 
                log.error("access to Amonzon S3 denied, check username/password entry(%s,%s)" % (e.status,e.reason))
            elif e.status == 404:
                try:
                    self.bucket = connection.create_bucket(bucketname)
                    x = self.bucket.get_acl()
                    log.info("Connected to Amazon S3 using bucket %s" % (self.bucket.name,))
                    return
                except S3.S3ResponseError, e:
                    if e.status == 409:
                        log.error("access to Amonzon S3 denied, bucket name used(%s)" % (bucketname,))
                    else:
                        log.error("Amonzon S3 access error(%s,%s)" % (e.status,e.reason))
            elif e.status == 500: raise e
            else:
                log.error("Amonzon S3 access error(%s,%s)" % (e.status,e.reason))
            _terminate(255)
        except S3.S3CreateError, e:
            log.error("access to Amonzon S3 bucket(%s) failed, try to use other bucket name" % (bucketname,))
            _terminate(255)

    connect = retry_wrapper(connect)

class S3fs(Fuse):

    lastFullFlush = 0 

    def __init__(self, mountpoint, **kw):

        Fuse.__init__(self, mountpoint, **kw)
    
        log.info("Mountpoint: %s" % self.mountpoint)

        # do stuff to set up your filesystem here, if you want

        self.inodeCache = {}
        self.openfiles = {}
        self.pathCache = {}
        global DefaultBlockSize
        global UID
        global GID
        global CacheDir
        global Cache_Policy
        DefaultBlockSize = 1*1024*1024
        
        self.bucketname = None
        self.password = DefaultPassword
        self.username = DefaultUsername
        self.blocksize = DefaultBlockSize
    
        options_required = 1
        UID = os.getuid()
        GID = os.getgid()

        try: self.username = self.optdict['username']
        except KeyError: pass
        try: self.password = self.optdict['password']
        except KeyError: pass

        if self.optdict.has_key("blocksize"):
            self.blocksize = int(self.optdict['blocksize'])

        if self.optdict.has_key("bucket"):
            self.bucketname = self.optdict['bucket']

        try: encrypt = self.optdict["encrypt"]
        except KeyError: encrypt=1
        try: compress = self.optdict["compress"]
        except KeyError: compress=1
        try: enc_key = self.optdict["enc_key"]
        except KeyError: enc_key=None
        try: 
            CacheDir = os.path.expanduser(self.optdict["cache"])
            if not os.path.isdir(CacheDir): os.mkdir(CacheDir) 
        except (OSError, KeyError): CacheDir="/tmp"

        try:
            cache_policy = self.optdict['cache_policy']
            if cache_policy == "observer": 
                Cache_Policy = CACHE_OBSERVER
            elif cache_policy == "keep": 
                Cache_Policy = CACHE_KEEP
            elif cache_policy == "remove_on_umount": 
                Cache_Policy = CACHE_REMOVE_ON_UMOUNT
            elif cache_policy == "remove_on_close":
                Cache_Policy = CACHE_REMOVE_ON_CLOSE
        except KeyError: pass

        if self.optdict.has_key("allow_other"): self.allow_other = 1
        if self.optdict.has_key("kernel_cache"): self.kernel_cache = 1

        global s3Link

        s3Link = S3Link(bucketname=self.bucketname,
                        aws_key=self.username,
                        aws_secret=self.password,
                        compress=compress,
                        encrypt=encrypt,
                        encryptionKey=enc_key,
                        blocksize=self.blocksize)

        s3Link.connect()

        #thread.start_new_thread(self.mythread, ())
        pass

    def mythread(self):
    
        """
        The beauty of the FUSE python implementation is that with the python interp
        running in foreground, you can have threads
        """    
        log.debug("mythread: started")
        #while 1:
        #    time.sleep(120)
        #    print "mythread: ticking"
    
    def _remove_dentry(self, path):
        """
        remove a directory entry(in the parent name space)
        """
        parent, me = _splitpath(path)
        if me == "/": return 0 #I am root
        parentinode = self.getinode(parent)
        if parentinode and not parentinode.ro:
            try:
                del parentinode.data['content'][me]
                parentinode.unlink(me)
            except AttributeError: return 1
            except KeyError: pass
            log.debug("_remove_dentry: %s removed from %s" % (me,parent))
            if parentinode.update() == 0: return 0
        return 1

    def _add_dentry(self, path, ino):
        """
        add a directory entry (in the parent name space) with inode number(ino)
        """
        parent, me = _splitpath(path)
        if me == "/": 
            log.debug("_add_dentry: %s(%s) added to %s" % (me, ino, parent))
            return 0 #I am root
        parentinode = self.getinode(parent)
        if parentinode and not parentinode.ro:
            try:
                exist = parentinode.data['content'].has_key(me)
                parentinode.data['content'][me] = ino
                if not exist: parentinode.link(me)
            except AttributeError: return 1
            log.debug("_add_dentry: %s(%s) added to %s" % (me, ino, parent))
            if parentinode.update() == 0: return 0
        return 1

    def getattr(self, path):
        log.debug("S3fs.getattr: %s" % (path,))
        #st_mode (protection bits)
        #st_ino (inode number)
        #st_dev (device)
        #st_nlink (number of hard links)
        #st_uid (user ID of owner)
        #st_gid (group ID of owner)
        #st_size (size of file, in bytes)
        #st_atime (time of most recent access)
        #st_mtime (time of most recent content modification)
        #st_ctime (time of most recent content modification or metadata change).

        if path == "/"+TRIGGER: 
            self._fs_flush()
            return [0]*9
        if path == '/':
            inode=self.getinode(path)
            if not inode:
                log.debug("S3fs.getattr: No root, create it")
                inode = self._mkfileOrDir("/",None,S_IFDIR|S_IRUSR|S_IXUSR|S_IWUSR|S_IRGRP|S_IXGRP|S_IXOTH|S_IROTH,RootIno,1,2)
                inode.update(flush=True)
        else:
            try:
                f = self.openfiles[path]
                f = f['handle']
                inode = f.inode
            except KeyError:
                inode = self.getinode(path)
            
        if inode:
            adj = time.timezone
            statTuple = (inode.mode,inode.ino,inode.dev,inode.nlink,inode.uid,inode.gid,inode.size,
                         inode.atime - adj,inode.mtime - adj, inode.ctime - adj)
            log.debug("statsTuple "+str(statTuple))
            return statTuple
        else:
            e = OSError("No such file"+path)
            e.errno = ENOENT
            raise e
    
    def readlink(self, path):
        """
        return the path(symbolic link) of the requested object
        """
        log.debug("S3fs.readlink: path='%s'" % (path,))
        inode = self.getinode(path)
        if not (inode.mode & S_IFLNK):
            e = OSError("Not a link"+path)
            e.errno = EINVAL
            raise e
        try:
            slink = inode.data['content']['symlink']
            log.debug("about to follow link : %s" % (slink,))
            return slink
        except KeyError:
            e = OSError("Not a link "+path)
            e.errno = EINVAL
            raise e
    
    def getdir(self, path):
        inode = self.getinode(path)
        if not (inode.mode & S_IFDIR):
            e = OSError("Not a directory "+path)
            e.errno = EINVAL
            raise e

        entries = [ (x,0) for x in [".",".."] + inode.data['content'].keys() ]
        log.debug("getdir: path=%s(%s) " % (path,str(entries)))
        return entries
    
    def unlink(self, path):
        """
        unlink(remove) a path entry
        it is actually two operation in linux
        remove the directory entry and link to the underlying inode and remove
        that if there is no other reference to it
        """
        log.debug("unlink called on:"+path)

        inode = self.getinode(path) #load inode into cache
        if not self._remove_dentry(path): #remove parent entry
            try:
                inode.unlink(path) #remove inode
                inode.update()
            except AttributeError: pass

            try: del self.inodeCache[path]
            except KeyError: pass
            return 0
        else:
            log.error("unlink failed:"+path)
            e = OSError("unlink failed "+path)
            e.errno = EINVAL
            raise e

    def rmdir(self, path):
        """
        remove directory(from parent name space), no checking is done if it is
        not empty
        """
        log.debug("rmdir called on:"+path)
        if not self._remove_dentry(path):
            inode = self.getinode(path)
            try:
                inode.unlink(path, 2)
                inode.update()
            except AttributeError: pass

            try: del self.inodeCache[path]
            except KeyError: pass
            return 0
        else:
            log.error("rmdir failed:"+path)
            e = OSError("rmdir failed "+path)
            e.errno = EINVAL
            raise e

        
    def symlink(self, path, path1):
        """
        make a symbolic link from one path to another
        """
        log.debug("S3fs.symlink: path='%s', path1='%s'" % (path, path1))
        self._mkfileOrDir(path1,path,S_IFLNK|S_IRWXU|S_IRWXG|S_IRWXO,-1,0,1)
        return 0

    def rename(self, path, path1):
        """
        rename(move) from one path to another
        this actually involve 2 operations, add the new one then remove the old
        one
        """
        log.debug("rename from:"+path+" to:"+path1)
        inode = self.getinode(path)
        if (inode.mode & S_IFREG):
            self.link(path, path1)
            self.unlink(path)
        else:
            self._add_dentry(path1, inode.ino)
            self._remove_dentry(path)

        try: del self.inodeCache[path]
        except KeyError: pass
        return 0

    def link(self, path, path1):
        """
        create a hardlink from one path to another
        """
        log.debug("hard link: path='%s', path1='%s'" % (path, path1))
        inode = self.getinode(path)
        if not (inode.mode & S_IFREG):
            e = OSError("hard links only supported for regular files not directories:"+path)
            e.errno = EPERM
            raise e
        self._mkfileOrDir(path1,None,inode.mode,inode.ino,0,1)
        try: del self.inodeCache[path]
        except KeyError: pass
        return 0
    
    def chmod(self, path, mode):
        log.debug("chmod called with path:(%s), mode:0%o" % (path, mode))
        try:
            #we don't update if this is an open file
            f = self.openfiles[path]
            f = f['handle']
            f.inode.mode = (f.inode.mode & ~(S_ISUID|S_ISGID|S_ISVTX|S_IRWXU|S_IRWXG|S_IRWXO)) | mode
            f.needsUpdate = 1
        except KeyError:
            #plain chmod
            inode = self.getinode(path)
            inode.mode = (inode.mode & ~(S_ISUID|S_ISGID|S_ISVTX|S_IRWXU|S_IRWXG|S_IRWXO)) | mode
            inode.update()
        return 0

    def chown(self, path, user, group):
        log.debug("chown called with user:"+str(user)+" and group:"+str(group))
        try:
            #we don't update if this is an open file
            f = self.openfiles[path]
            f = f['handle']
            f.inode.uid = user
            f.inode.gid = group
            f.needsUpdate = 1
        except KeyError:
            #plain chmod
            inode = self.getinode(path)
            inode.uid = user
            inode.gid = group
            inode.update()
        return 0

    def truncate(self, path, size):
        log.debug("truncate "+path+" to size:"+str(size))
        oldsize = size
        try:
            #we don't update if this is an open file
            f = self.openfiles[path]
            f = f['handle']
            f.truncate(size)
        except KeyError:
            inode = self.getinode(path)
            inode.truncate(size) #remove excess nodes
            if oldsize != size: inode.update()
        return 0

    def mknod(self, path, mode, dev):
        """ Python has no os.mknod, so we can only do some things """
        log.debug("mknod:"+path)
        if S_ISREG(mode) | S_ISFIFO(mode) | S_ISSOCK(mode):
            self._mkfileOrDir(path,None,mode,-1,0,1)
        else:
            return -EINVAL

    def _mkfileOrDir(self, path, path2, mode, inodenumber, size, nlinks):
        """
        create a new entry(and associated inode if necessary)
        path is the directory entry to create
        path2 is used only for symlink
        inodenumber is the inode to link to(-1 means create new one instead of
        read and link)
        """
        #retrieve/create inode
        inode = S3Inode.GetInode(inodenumber)

        if inode.ino == -1 and inodenumber == RootIno: inode.ino = RootIno
        if inodenumber == -1 or inodenumber == RootIno:
            inode.mode = mode
            if path2 != None: inode.data['content']['symlink'] = path2

        inode.link(path, nlinks) #update link count
        if path=="/" or inode.update() == 0:
            log.debug("S3fs.mkfileOrDir: inode(%s) created for %s, nlink(%i)" %
                    (inode.ino, path, inode.nlink))
            if self._add_dentry(path, inode.ino):
                #add entry to parent directory failed, remove the created node
                log.error("S3fs.mkfileOrDir: cannot add inode(%s) dentry(%s)" %
                    (inode.ino, path))
                inode.unlink(path,nlinks)
                e = OSError("Couldnt create inode in _mkfileOrDir "+path)
                e.errno = ENOSPC
                raise e
            return inode
        else:
            e = OSError("Couldnt create inode in _mkfileOrDir "+path)
            e.errno = ENOSPC
            raise e

    def mkdir(self, path, mode):
        """
        create directory 
        """
        log.debug("mkdir path:"+path+" mode:"+str(mode))
        inode = self._mkfileOrDir(path, None, mode|S_IFDIR, -1, 1, 2)
        return 0
        
    def utime(self, path, times):
        log.debug("utime for path:"+path+" times:"+str(map(time.localtime,times)))
        try:
            f = self.openfiles[path]
            f = f['handle']
            f.inode.atime = times[0]
            f.inode.mtime = times[1]
            f.needsUpdate = 1
        except KeyError:
            inode = self.getinode(path)
            inode.atime = times[0]
            inode.mtime = times[1]
            inode.update()
        return 0

    def open(self, path, flags):
        log.debug("s3fs.open: %s(%i)" % (path, flags))
        try:
            f = self.openfiles[path]
            f['count'] += 1
            return 0
        except KeyError: pass
        try:
            inode = self.getinode(path)
            f = OpenFile(inode)
            self.openfiles[path] = dict(handle=f,count=1)
            return 0
        except:
            _logException("Error opening file "+path)
            e = OSError("Error opening file "+path)
            e.errno = EINVAL
            raise e

    def _fs_flush(self):
        now = time.time()
        if not self.lastFullFlush: self.lastFullFlush = now
        if now - self.lastFullFlush > FullFlushInterval:
            for (path, f) in self.openfiles.items():
                f = f['handle']
                if now - f.lastFlush > FullFlushInterval and f.needsWriting:
                    log.debug("S3fs._fs_flush: flushing dirty file(%s)" % (path,))
                    f.flushBuffer(close_cache=False, lazy=True)

            log.debug("S3fs._fs_flush: flushing inode")
            S3Inode.Flush()
            self.lastFullFlush = now

    def read(self, path, readlen, offset):
        try:
            log.debug("s3fs.read: %s" % path)
            log.debug("reading len:"+str(readlen)+" offset:"+str(offset))
            f = self.openfiles[path]
            f = f['handle']
            buf = f.read(readlen, offset)
            arr = array.array('c')
            arr.fromlist(buf)
            rets = arr.tostring()
            log.debug("s3fs.read: ret(%i)" % (len(rets)))

            return rets
        except:
            _logException("Error reading file "+path)
            e = OSError("Error reading file "+path)
            e.errno = EINVAL
            raise e
    
    def write(self, path, buf, off):

        try:
            f = self.openfiles[path]
            f = f['handle']
            written = f.write(buf, off)
            log.debug("s3fs.write: %s, off:%i, written:%i" % (path,off,written))
            return written
        except:
            _logException("Error writing file "+path)
            e = OSError("Error writing file "+path)
            e.errno = EINVAL
            raise e

    def release(self, path, flags):
        log.debug("s3fs.release: %s %s" % (path, flags))
        try:
            f = self.openfiles[path]
            f['count'] -= 1
            if f['count'] == 0:
                f = f['handle']
                del self.openfiles[path]
                r = f.close()
        except KeyError: pass

        return 0

    def statfs(self):
        """
        Should return a tuple with the following 6 elements:
            - blocksize - size of file blocks, in bytes
            - totalblocks - total number of blocks in the filesystem
            - freeblocks - number of free blocks
            - availblocks - number of blocks available to non-superuser
            - totalfiles - total number of file inodes
            - freefiles - nunber of free file inodes
    
        Feel free to set any of the above values to 0, which tells
        the kernel that the info is not available.
        """
        block_size = s3Link.blocksize
        blocks = 2**20
        blocks_free = 2**20
        blocks_avail = 2**20
        files = 2**20
        files_free = 2**20
        namelen = 256
        a = (block_size, blocks, blocks_free, blocks_avail, files, files_free, namelen)
        log.debug("S3fs.statfs: %s" % str(a))
        return a

    def fsync(self, path, isfsyncfile):
        """
        sync any possible dirty stuff of path to backend
        """
        log.debug("s3fs.fsync: path=%s, isfsyncfile=%s" % (path, isfsyncfile))
        f = self.openfiles[path]
        f = f['handle']
        f.flushBuffer()
        f.inode.update()
        return 0
    
    def getinode(self, path):
        """
        Map path to inode
        Return S3Inode object or None
        """
        def _flushCache(path):
            c = self.inodeCache
            k = c.keys()
            for x in k:
                if x.startswith(path): del c[x]
        try:
            ino = self.inodeCache[path]
            log.debug("s3fs.getinode: path(%s) served from cache(%i)" % (path,ino))
            inode = S3Inode.GetInode(ino)
            if inode.ino != ino: 
                #ah, error incosistent
                log.warning("s3fs.getinode: Inconsistency ino(%i) stored but inode not in fs" % (ino,))
                del self.inodeCache[path]
                _flushCache(path+"/")
                raise KeyError
        except KeyError: 
            #not in cache, just reload everything starting from
            #root if necessary

            inode = S3Inode.GetInode(RootIno)
            if inode.ino != RootIno: 
                log.warning("s3fs.getinode: Root entry not found")
                return None 
            c_path = ""
            for p in ( x for x in path.split('/') if len(x)):
                log.debug("s3fs.getinode: c_path(%s), p(%s)" % (c_path,p))
                c_path = c_path + "/" + p
                try: 
                    ino = self.inodeCache[c_path] 
                    log.debug("s3fs.getinode: path(%s) in cache(%i)" % (c_path,ino))
                    inode = S3Inode.GetInode(ino)
                    if ino != inode.ino:
                        log.warn("s3fs.getinode: Inconsistency ino(%i) cached but inode not in fs" % (ino, c_path))
                        del self.inodeCache[c_path]
                        _flushCache(c_path+"/")
                        raise KeyError
                except KeyError: # not in cache
                    log.debug("s3fs.getinode: path(%s) not in cache" % (c_path,))
                    try:
                        #try through parent info
                        ino = inode.data['content'][p]        
                        log.debug("s3fs.getinode: path(%s) loaded and cached(%i)" % (c_path,ino))
                    except KeyError:
                        #not in parent nothing else to do
                        log.debug("s3fs.getinode: path(%s) not in parent(%i)" % (p,inode.ino))
                        _flushCache(path+"/")
                        return None

                inode = S3Inode.GetInode(ino)
                if inode.ino != ino: 
                    p_path, _ = c_path.rsplit("/",1)
                    if p_path: 
                        try: del self.inodeCache[p_path]
                        except KeyError: pass
                    _flushCache(p_path+"/")
                    #ah, error incosistency
                    log.error("s3fs.getinode: Inconsistency ino(%i) stored (%s) but inode not in fs" % (ino,c_path))
                    return None
                else:
                    self.inodeCache[c_path] = ino

        #we are here means we have found(and reload all ancestor
        #inodes)
        log.debug("s3fs.getinode: path(%s) found (%i)" % (path,inode.ino))
        return inode

    def flush(self, path):
        log.debug("s3fs.flush: called(%s)" % (path,))
        return 0

    def umount(self):
        prefix = "%s_%s_%s" % (s3Link.bucket.name, s3Link.fs_prefix, s3Link.inode_prefix)
        for (path, f) in self.openfiles.items():
            log.debug("s3fs.umount: flushing %s" % (path,))
            f['handle'].close()

        if Cache_Policy == CACHE_REMOVE_ON_UMOUNT:
            for x in os.listdir(CacheDir):
                if x.startswith(prefix): 
                    f = "%s/%s" % (CacheDir, x)
                    try: os.remove(f)
                    except OSError: pass

        S3Inode.Flush(force=True)
        log.info(self.mountpoint + " Umounted")

# Setup logging
log = logging.getLogger('s3fs')
defaultLogLevel = logging.INFO
log.setLevel(defaultLogLevel)
defaultLogFormatter = logging.Formatter("%(asctime)s %(levelname)-10s %(message)s", "%x %X")
    
# log to stdout while parsing the config while
defaultLoggingHandler = logging.StreamHandler(sys.stdout)
_addLoggingHandlerHelper(defaultLoggingHandler)


def parseCommandLineArgs(args):
  usage = "usage: %prog none mountpoint [options]"

  parser = optparse.OptionParser(usage=usage)
  parser.add_option("-c", "--conf", dest="conf",
                    action="store", default="~/s3fs.conf",
                    help="config file to use, default to ~/s3fs.conf" )
  parser.add_option("-f", "--foreground", dest="foreground",
                    action="store_true", default=False,
                    help="Run in foreground(default no)" )
  parser.add_option("-k", "--prompt-for-enc-key", dest="promptForKey",
                    action="store_true", default=False,
                    help="Prompt for data encryption key" )
  parser.add_option("-a", "--allow_other", dest="allow_other",
                    action="store_true", default=False,
                    help="allow other to access this mount point" )
  parser.add_option("-n", "--kernel_cache", dest="kernel_cache",
                    action="store_true", default=False,
                    help="cached VFS" )
  parser.add_option("-p", "--prompt-for-password", dest="promptForPasswd",
                    action="store_true", default=False,
                    help="Prompt for the AWS secret" )
  parser.add_option("-o", "--options", dest="s3fsOptions",
                    help="Use those options", metavar="option1=value1,[option2=value2,...]",
                    default="")

  options, args = parser.parse_args(args)

  if len(args) != 2:
    parser.error("Wrong number of arguments")
  else:
    x,mountpoint = args
    
  odata = options.s3fsOptions

  namedOptions = {}
  if odata:
    for o in odata.split(","):
     try:
       k, v = o.split("=", 1)
       namedOptions[k] = v
     except:
       print "Ignored option :"+o

  if options.foreground: namedOptions['foreground']=1
  if options.allow_other: namedOptions['allow_other']=1
  if options.kernel_cache: namedOptions['kernel_cache']=1

  if options.promptForPasswd:
    namedOptions['password'] = get_secret("AWS secret key: ")
  if options.promptForKey:
    namedOptions['enc_key'] = get_secret("data encryption key: ")
    
  if options.conf: conf = options.conf
  else: conf = "~/s3fs.conf"
  return conf, mountpoint, namedOptions


def main(mountpoint, namedOptions):
    running = [True]
    server = S3fs(mountpoint, **namedOptions)
    server.flags = 0
    server.multithreaded = 0
    if not namedOptions.has_key('foreground'): daemonize()
    try: cache_age = int(namedOptions['cache_age'])
    except KeyError: cache_age = 120
    try: flush_freq = int(namedOptions['flush_freq'])
    except KeyError: flush_freq = 5
    global FullFlushFreq
    FullFlushFreq = flush_freq

    ReloadInTransit([False], CacheDir, "%s_%s" % (s3Link.bucketname,s3Link.fs_prefix), s3Link)
    #S3Inode.CacheFlush(CacheDir, _cachePrefix())
    km = fork_it(S3KeyRemover, running, CacheDir, "%s_%s" % (s3Link.bucketname,s3Link.fs_prefix), s3Link)
    cm = fork_it(ManageCache, running, CacheDir, s3Link.bucketname, cache_age)
    tm = fork_it(Timer, running, mountpoint, flush_freq)
    um = fork_it(ReloadInTransit, running, CacheDir, "%s_%s" % (s3Link.bucketname,s3Link.fs_prefix), s3Link)
    server.getattr("/") #create Root before entering loop
    log.info("main: Root successfully loaded")
    server.main()
    running[0] = False
    server.umount()
    os.kill(cm, signal.SIGTERM)
    os.kill(tm, signal.SIGTERM)
    os.kill(um, signal.SIGTERM)
    os.kill(km, signal.SIGTERM)
    os.waitpid(km,0)
    os.waitpid(cm,0)
    os.waitpid(tm,0)
    os.waitpid(um,0)

if __name__ == '__main__':


    conf, mountpoint, namedOptions = parseCommandLineArgs(sys.argv[1:])
    config = s3Config(["/etc/s3fs.conf", os.path.expanduser(conf)])
    for k,v in namedOptions.items(): config[k]=v
    """
    the fuse binding is doing very bad things by trying to grap the arguments
    and do it by itself which we want to override so we just zap them after we
    process it
    """
    sys.argc=0
    sys.argv={}
    try:
        if config['password'] == "prompt":
            config['password'] = get_secret("AWS secret key: ")
    except KeyError: pass

    try:
        if config['enc_key'] == "prompt":
            config['enc_key'] = get_secret("data encryption key: ")
    except KeyError: pass

    main(mountpoint,config)
