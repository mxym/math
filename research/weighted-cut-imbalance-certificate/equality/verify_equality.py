#!/usr/bin/env python3
"""Recover/exhaust ALL tight auxiliary point-vector pairs from the published finite
cover; dependent exact replay of the indicated certificate, not a second independent verifier.
Pass the directory containing the #123 verifier and certificate as the sole argument.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import product
from functools import cache
from collections import Counter
import hashlib,sys,importlib.util,json
def need(b,why):
    if not b:raise ValueError(why)
def h256(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def go(root):
    cfile=root/'certificate.json';vfile=root/'verify.py'
    need(h256(cfile)=='353673afb1e06fdf1529ec8d81e518e688b4ded7d750f079f8499ccd154a0b9d','wrong certificate')
    need(h256(vfile)=='b2b974b2f92ce7505960a5455620bc41f1872381aded6bd56348d8588cd1d9bf','wrong verifier')
    spec=importlib.util.spec_from_file_location('original_be',vfile)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    d=json.loads(cfile.read_bytes())
    need(set(d)=={'bounds','cells','version'} and d['version']==1 and len(d['bounds'])==30,'schema')
    catalog={}
    for k,ds in enumerate(d['bounds'],2):
        rows=list(mod.rows(k))
        catalog[k]=[mod.make_plane(k,sel,rows) for sel in ds]
    need(sum(map(len,catalog.values()))==2286,'prefix choices')
    def P(k,j):
        need(type(k) is int and k in catalog and type(j) is int and 0<=j<len(catalog[k]),'indices')
        return catalog[k][j]
    lo,hi=Q(1,2),Q(2,3);poly=[(lo,Q(0)),(hi,Q(0)),(hi,hi),(lo,hi)]
    for j in range(13):
        p=Q(j,12);g=2*p*(1-p);poly=mod.clip(poly,(-g,1,g-p))
    expected={
       ((Q(2,3),Q(2,3)),(Q(2,3),)*3),
       ((Q(3,5),Q(2,5)),(Q(2,5),)*5),
       ((Q(3,5),Q(107,260)),(Q(107,260),)*3+(Q(199,520),)*2),
    }
    tight=set();stats=Counter()
    @cache
    def corner(z,H):
        y=[Q(0),z[1]]+[Q(mod.affine(P(k,i),z)) for k,i in enumerate(H,2)]+[Q(2)]
        a=mod.upper(y);b=(15*z[0]-6)/4
        need(0<b<=1 and len(a)==32 and sum(a)==2 and min(a)>=0 and all(x>=y for x,y in zip(a,a[1:])),'vector scale/order')
        need(all(sum(a[:k])>=v for k,v in enumerate(y)),'prefix')
        s=tuple(x for x in a if x);v2=sum(x*x for x in s)
        if v2<=b*b:
            need(len(s)>=2,'constant absolute-value branch')
            stats['strict-square']+=1
            return
        k=mod.khintchine(a)
        need(k<=b,'unexpected violation')
        if k==b:
            # Include the vector as well as parameters, not just the geometry.
            tight.add((z,s));stats['tight-exact']+=1
        else:stats['strict-exact']+=1
    mass=0
    def rec(t,v):
        nonlocal mass
        need(type(t) is list and len(t) in (1,3),'node')
        if len(t)==1:
            need(len(t[0])==30,'leaf witnesses')
            for z in v:corner(z,tuple(t[0]))
            stats['leaves']+=1;stats['incidences']+=len(v);mass+=mod.twice_area(v)
            return
        k,i,j=t[0];f=mod.differences(P(k,i),P(k,j))
        L=mod.clip(v,f);R=mod.clip(v,tuple(-q for q in f))
        l,r=mod.twice_area(L),mod.twice_area(R)
        need(l>0 and r>0 and l+r==mod.twice_area(v),'partition')
        stats['splits']+=1
        rec(t[1],L);rec(t[2],R)
    rec(d['cells'],poly)
    need(mass==mod.twice_area(poly)==Q(130792,765765),'total area')
    need(stats['splits']==956 and stats['leaves']==957 and stats['incidences']==3791,'cover count')
    need(tight==expected,('bad tight set',tight))
    for z,s in sorted(tight):
        sign=lambda t:(t>0)-(t<0)
        for e in product((-1,1),repeat=len(s)):
            need(sign(sum(a*b for a,b in zip(s,e)))==sign(sum(e))!=0,'not strict majority')
        print('corner',tuple(map(str,z)),'positive slopes',tuple(map(str,s)))
    print('check counts',dict(stats));print('three tight corner/vector types; PASS')
if __name__=='__main__':go(Path(sys.argv[1]) if len(sys.argv)==2 else Path(__file__).resolve().parent.parent/'general-public')
