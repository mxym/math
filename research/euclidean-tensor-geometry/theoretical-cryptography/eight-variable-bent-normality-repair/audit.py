#!/usr/bin/env python3
"""Independent audit: nauty for transporter COUNTS, explicit Boolean values for every witness.
Requires pynauty==2.8.8.1.  No C++ code, affine basis search, subspace list, or slope lookup is reused.
"""
import argparse
import hashlib
import io
from pathlib import Path
from collections import defaultdict, Counter
from functools import reduce
from operator import xor

DATA = {
  'raw': ('fc58fe0b3b11b67056ebb5f49c58aea8b338edb8d9cda9313d15494850dc7c80', 39952, 4085),
  'reduced': ('f276d07eedeee1a8db90e0f453317d36ae420a168eb739a255d726eff5f1aa79', 1309, 1309)
}
V = range(128)
PAR = [x.bit_count() % 2 for x in V]
MON = [sum(1 << x for x in V if (x & m) == m) for m in V]

def need(condition, message):
    if not condition:
        raise ValueError(message)

def read(path, mode):
    data = path.read_bytes()
    sha, n, k = DATA[mode]
    need(hashlib.sha256(data).hexdigest() == sha, 'wrong source bytes')
    result = []
    polynomials = [t[4:] for t in data.decode('ascii').splitlines() if t.startswith('anf=')]
    need(len(polynomials) == n, 'wrong source count')
    for p in polynomials:
        terms = [sum(1 << (ord(c)-97) for c in t) for t in p.split('+')]
        bits = reduce(xor, (MON[m] for m in terms), 0)
        v = bytes((bits >> x) & 1 for x in V)
        w = [1-2*y for y in v]
        for s in [1,2,4,8,16,32,64]:
            for b in range(0,128,2*s):
                for j in range(b,b+s):
                    u,z = w[j],w[j+s];w[j],w[j+s] = u+z,u-z
        if not set(w) <= {-16,0,16}: continue
        supp=bytes(int(z != 0) for z in w)
        need(sum(supp)==64, 'non-balanced support')
        result.append((v,supp))
    need(len(result)==k,'wrong near-bent count')
    return result

def classify(F, counts_only=False):
    import pynauty
    need(pynauty.__version__ == '2.8.8.1', 'use documented pynauty version')
    # All 128 points and all 254 affine hyperplanes. Colors 0 and 1 are distinct;
    # the third color marks all plane vertices. Blocks have common fixed sizes.
    adj={x:[] for x in range(382)}
    for u in range(1,128):
        for x in V:
            h=128+2*(u-1)+PAR[x&u]
            adj[x].append(h); adj[h].append(x)
    planes=set(range(128,382)); points=set(V)
    canon_ids={}; group_orders=[]; exact={}; sides=[[],[]]
    for _,s in F:
        for side in range(2):
            S=bytes(y^side for y in s)
            if S not in exact:
                one={x for x in V if S[x]}
                g=pynauty.Graph(382, adjacency_dict=adj,
                     vertex_coloring=[points-one,one,planes])
                cert=pynauty.certificate(g)
                if cert not in canon_ids:
                    canon_ids[cert]=len(canon_ids)
                    _, mant, expo, _, _=pynauty.autgrp(g)
                    need(expo==0 and 0 < mant < 2**53 and mant==int(mant),
                         'group order is outside the audited exact-integer range')
                    group_orders.append(int(mant))
                exact[S]=canon_ids[cert]
            sides[side].append(exact[S])
    source,target=sides
    if counts_only:
        A,B=Counter(source),Counter(target)
        return sum(A[c]*B[c] for c in A),sum(A[c]*B[c]*group_orders[c] for c in A)
    buckets=defaultdict(list)
    for j,c in enumerate(source):buckets[c].append(j)
    return {(i,j):group_orders[c] for i,c in enumerate(target) for j in buckets[c]}

def affine_check(row, F):
    i,j,b,*r=row
    need(0<=i<len(F) and 0<=j<len(F) and len(r)==12
         and all(0<=y<128 for y in (b,*r)), 'bad witness coordinates')
    cols=r[:7]; v1,v2,v3,lo,hi=r[7:]
    lower,ls=F[i]; upper,us=F[j]
    # Validate the bijection and every single membership (no hash filter here).
    I=[b]
    for c in cols:I += [x^c for x in I]
    need(len(set(I))==128 and all(us[x]!=ls[I[x]] for x in V), 'not a spectral alignment')
    D=(0,v1,v2,v1^v2,v3,v1^v3,v2^v3,v1^v2^v3)
    need(len(set(D))==8,'flat has small dimension')
    def tr(x):return sum(PAR[x&c] << k for k,c in enumerate(cols))
    low=[lower[lo^v] for v in D]
    high=[upper[tr(hi^v)]^PAR[b&(hi^v)] for v in D]
    vals=low+high
    # Four independent coordinates, the last selects the parallel high coset.
    mask=sum((vals[1<<k]^vals[0])<<k for k in range(4))
    need(all(vals[t]==(vals[0]^PAR[mask&t]) for t in range(16)),
         'formula is not affine on this four-flat')
    return i,j,tuple((b,*cols))

def audit(F, lines):
    expected=classify(F); total_expected=sum(expected.values())
    print('nauty: positive ordered pairs',len(expected),'affine transporters',total_expected,flush=True)
    last=None; seen=set(); rows=0
    def finish():
        if last is not None:
            need(last in expected and expected.pop(last)==len(seen),
                 'omitted/incorrect number of transporters for pair '+str(last))
    for line in lines:
        vals=list(map(int,line.split()))
        need(len(vals)==15,'bad field count')
        i,j,key=affine_check(vals,F); pair=i,j
        if pair!=last:
            finish(); seen=set();last=pair
        need(key not in seen,'duplicate transporter');seen.add(key);rows+=1
    finish()
    need(not expected and rows==total_expected, 'missing complete ordered pair(s)')
    print('PASS: all',rows,'distinct affine maps, supports, and sixteen-point affine restrictions verified.')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=DATA);p.add_argument('source',type=Path)
    p.add_argument('trace',type=Path)
    a=p.parse_args();F=read(a.source,a.mode)
    print('source verified:',len(F),'near-bents',flush=True)
    with a.trace.open('rb') as f:audit(F,f)
if __name__=='__main__':main()
