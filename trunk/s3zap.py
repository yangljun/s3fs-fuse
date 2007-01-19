#!/usr/bin/env python

import bitbucket,sys

try:
    fsname = sys.argv[1]
except IndexError:
    fsname = "s3fs"

connect = bitbucket.connect()
print "Buckets available: " 
for x in connect._buckets.keys():
    print "  %s" % x
b = [ x for x in connect._buckets.keys() if x.endswith(fsname) ]
for x in b:
    print "zapping %s" % (x,)
    bucket = connect.get_bucket(x)
    bucket.fetch_all_keys()
    keys = bucket.keys()
    for x in keys: del bucket[x]
