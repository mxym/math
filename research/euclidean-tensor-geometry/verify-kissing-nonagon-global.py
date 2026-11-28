#!/usr/bin/env python3
"""Replay the 0.161 nine-point certificate using the pinned exact engines."""
import sys,hashlib,runpy
from pathlib import Path
root=Path(__file__).resolve().parent
def pinned(n,h):
    p=root/n
    if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('different predecessor: '+n)
    return runpy.run_path(str(p))
def main():
    if not __debug__:raise RuntimeError('run without -O')
    a=pinned('verify-kissing-seven-heptagon-boxes.py','50c47966131b0324b1d31e4ca8ae6d926b12dc157022ea46aac5e49f94c0fe28')
    b=pinned('verify-kissing-nine-gram-cells.py','f18bcd13cb34be3e5dce6d2d5dcb7449c410368e91c2ded9c6ebe2d17de8b5cb')
    if sys.argv[1:]==['census']:b['census'](9,4);return
    gs=b['GRAPHS'][2]
    if len(gs)!=170:raise ValueError('bad census size')
    for j in (range(170)if len(sys.argv)==1 else [int(x)for x in sys.argv[1:]]):
        if not 0<=j<170:raise ValueError('bad class')
        if not a['solve'](gs[j],161000,32000):raise RuntimeError('unclosed class '+str(j))
        print('PASS9',j,flush=True)
if __name__=='__main__':main()
