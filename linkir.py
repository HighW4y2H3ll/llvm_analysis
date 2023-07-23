#!/usr/bin/env python3

import os
import time
import subprocess

llvm_path = "/home/hu/workspace/hu/llvm-project/install/bin"
linux_build = "/home/hu/workspace/hu/linux/build_llvm"
log = "./bcmerge.log"

outfd = open(log, 'w')
pool = [None] * 4

for root,_,files in os.walk(linux_build):
    bcfiles = []
    for f in files:
        if f.endswith('.mod'):
            with open(os.path.join(root, f), 'r') as fd:
                bcfiles = [os.path.join(linux_build, obj+".bc") for obj in fd.read().strip().split('\n')]
        elif f == ".built-in.a.cmd":
            with open(os.path.join(root, f), 'r') as fd:
                data = fd.read()
                cmd = data.split(';')[1].strip()
                assert(cmd.startswith("echo"))
                objs = cmd.split('|')[0].strip().split()[1:]
                bcfiles = []
                for obj in objs:
                    if os.path.basename(obj) == "built-in.a":
                        bcfiles.append(os.path.join(root, os.path.dirname(obj), f".{os.path.basename(obj)}.cmd.bcmerged"))
                    else:
                        bcfiles.append(os.path.join(root, obj+".bc"))
                if len(bcfiles) == 0:
                    for ff in files:
                        if ff.endswith('.bc') or ff.endswith('.bcmerged'):
                            bcfiles.append(os.path.join(root, ff))
        else:
            continue

        #cmd = [os.path.join(llvm_path, 'llvm-ar')] \
        #        + ['cDPrST', os.path.join(root, f+".bcmerged")] \
        #        + bcfiles
        cmd = [os.path.join(llvm_path, 'llvm-link')] \
                + ['-o', os.path.join(root, f+".bcmerged"), '--only-needed'] \
                + bcfiles
        print(cmd)

        if None in pool:
            pool[pool.index(None)] = subprocess.Popen(cmd)
        if None not in pool:
            while False not in map(lambda x: x.poll()==None, pool):
                time.sleep(1)
            for i in range(len(pool)):
                if pool[i].poll() != None:
                    pool[i] = None

map(lambda x: x.wait(), pool)
outfd.close()
