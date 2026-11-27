#!/usr/bin/env python3
"""Check or (with optional pynauty) reconstruct explicit EA lifts from the raw cover."""
import argparse, hashlib
from pathlib import Path
from audit import read, need, PAR, V

def check_lift(lo,hi,i,j,b,c,d,cols):
    need(0<=i<len(lo) and 0<=j<len(hi) and len(cols)==7 and c in (0,1)
         and all(0<=x<128 for x in [b,d,*cols]),'invalid EA lift fields')
    A=[d]
    for y in cols:A += [x^y for x in A]
    need(len(set(A))==128, 'singular EA input map')
    f=lo[i][0];g=hi[j][0]
    need(all(f[x]==(g[A[x]]^PAR[b&x]^c) for x in V),'false EA lift')

def check(lo,hi,lines):
    seen=set()
    for l in lines:
        vals=list(map(int,l.split()));need(len(vals)==12,'bad lift length')
        i,j,b,c,d,*cols=vals
        need(i not in seen,'duplicate raw index'); seen.add(i)
        check_lift(lo,hi,i,j,b,c,d,cols)
    need(seen==set(range(len(lo))),'missing raw or out-of-range record')
    print('PASS:',len(seen),'raw near-bent records each exactly mapped to a listed reduced representative.')

def generate(lo,hi,output):
    import pynauty as n
    need(n.__version__=='2.8.8.1','use documented pynauty version')
    N=766
    points=set(range(256));planes=set(range(256,N))
    adj={x:[x^128] if x<256 else [] for x in range(N)}
    # Incidence graph of full affine 8-space, with a matching on points that fixes
    # the unique vertical direction. A colored graph of f is thus preserved
    # precisely by the extended affine equivalences on seven variables.
    for u in range(1,256):
        for x in range(256):
            h=256+2*(u-1)+(u&x).bit_count()%2
            adj[x].append(h);adj[h].append(x)
    graph=n.Graph(N,adjacency_dict=adj)
    def canon(v):
        P={x+128*v[x] for x in V}
        graph.set_vertex_coloring([P,points-P,planes])
        label=n.canon_label(graph)
        # Convert the point portion of the canonical labeling to an exact
        # comparable key: the linear-dependency table from a greedy affine basis.
        # All 256 points are among the first 256 canonical positions.
        pp=[x for x in label if x<256]
        need(len(pp)==256,'lost points')
        ids={pp[0]:0};base=pp[0]
        for x in pp:
            if x not in ids:
                t=len(ids);ids.update({v^x^base:k+t for v,k in tuple(ids.items())})
        key=bytes(ids[x] for x in pp)
        return key,pp
    reps={};known={}
    for j,(v,_) in enumerate(hi):
        key,l=canon(v)
        need(key not in reps,'canonical class collision')
        reps[key]=(j,l);known[v]=(j,0,0,0,*[1<<k for k in range(7)])
    for i,(v,_) in enumerate(lo):
        if v in known: j,b,c,d,*cols=known[v]
        else:
            key,l=canon(v);need(key in reps,'missing representative')
            j,t=reps[key]
            p=dict(zip(l,t))
            need(all(p[x^128]==(p[x]^128) for x in range(256)),'not vertical affine')
            d=p[0]&127;c=p[0]>>7
            cols=[(p[1<<k]&127)^d for k in range(7)]
            b=sum(((p[1<<k]>>7)^c)<<k for k in range(7))
        check_lift(lo,hi,i,j,b,c,d,cols)
        print(i,j,b,c,d,*cols,file=output)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('raw',type=Path);p.add_argument('reduced',type=Path);p.add_argument('lifts',type=Path)
    p.add_argument('--generate',action='store_true')
    a=p.parse_args();lo=read(a.raw,'raw');hi=read(a.reduced,'reduced')
    if a.generate:
        with a.lifts.open('w') as f:generate(lo,hi,f)
    with a.lifts.open('r') as f:check(lo,hi,f)
if __name__=='__main__':main()
