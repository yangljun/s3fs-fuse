#!/usr/bin/env python

import bitbucket,sys
import md5
import hmac
import random
import zlib
import cPickle
from stat import *

fs_prefix = "s3fs"
inode_prefix = "inode"
enc_key=None

_attributes = ['ino', 'mode', 'dev', 'nlink', 'uid', 'gid', 'size',
               'atime', 'mtime', 'ctime', 'blocksize', 'block',
               'compress', 'encrypt' ] 

def arc4_key_stream(key):
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

def xor(str, enc_key, nonce):
    """
    this function encrypt the str by xor it with a RC4 random stream which
    if used properly is highly effective and efficient, the essence is,
    the key must not be used twice, thus the nonce(random number) which
    must be stored with the data(somewhere) for proper decrypt
    """
    if not nonce: return str

    #derive key from the hmac on nonce using encryption key
    key = hmac.new(enc_key, nonce).digest()
    rand = random.Random(key).randrange #weaker stream
    arc4 = arc4_key_stream(key) #ARC4 stream

    """
    drop the first 1024 sequence, this ensure that even the content is of
    predictive pattern, the key cannot be attacked as in the case of
    WEP(google about WEP RC4 attack)
    """
    for x in xrange(1024): arc4.next() 

    #rand is used to remove known to increase the difficulty on the
    #attack of arc4
    return (chr(ord(elem)^rand(256)^arc4.next()) for elem in str)

def object_key(inode,block):
    return "%s_%s_%i_%i" % (fs_prefix, inode_prefix, inode, block)

def list_dir(bucket, me, dirbits):
    #for a in _attributes: print "%s: %s" % (a, root[a])
    try: nonce = dirbits['nonce']
    except KeyError: nonce=None

    dir = ''.join(xor(dirbits.data, enc_key, nonce))
    try: dir = zlib.decompress(dir)
    except zlib.error: pass
    dir = cPickle.loads(dir)

    for (x,i) in dir.items():
        dnode = "/" + object_key(i,1)
        inode = object_key(i,0)
        bits = bucket[inode]
        path = "%s/%s" % (me.rstrip("/"), x)
        mode = int(bits['mode'])
        if mode & S_IFDIR: 
            yield (path, "/"+inode)
            for (p,d) in list_dir(bucket, path, bits):
                yield (p, d)
        else: yield (path, dnode)

def find(bucket, path):
    root_key = object_key(1,0)
    try: 
        root = bucket[root_key]
        if path=="/": yield ("/"+fs_prefix+"_*", "/"+root_key)
        for (p, d) in list_dir(bucket, "/", root):
            if p.startswith(path): yield (p, d)
    except KeyError: yield ("","")

def zap(bucket, fsname=None):
    bucket.fetch_all_keys()
    keys = bucket.keys()
    if not fsname :
        for x in keys: del bucket[x]
    else:
        for x in keys: 
            if x.startswith(fsname): del bucket[x]
    
if __name__ == '__main__':
    connect = bitbucket.connect()

    try: bucketname = sys.argv[1]
    except IndexError: bucketname = ""

    #global fs_prefix
    try: fs_prefix = sys.argv[2]
    except IndexError: fs_prefix = "s3fs"

    try: enc_key = md5.new(sys.argv[3]).digest()
    except IndexError: enc_key = connect.aws_secret_access_key


    b = [ x for x in connect._buckets.keys() if x.endswith(bucketname) ]

    for x in b:
        bucket = connect.get_bucket(x)
        try:
            for (p, d) in find(bucket, "/"):
                if len(p): print x+p,x+d
        except cPickle.UnpicklingError, e:
            print "%s/%s_* may not be a s3fs volume or it is encrypted with special key" % (bucket.name, fs_prefix)
