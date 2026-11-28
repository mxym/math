#!/usr/bin/env python3
"""Independent Smale sextic audit; requires SymPy, node, neighboring pinned JS. No full shard replay."""
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
from fractions import Fraction as F
import json, time, re
from pathlib import Path
checker=Path(__file__).with_name('verify_smale_real_sextic.js').read_text()
E=S.symbols('a b c d'); B=S.symbols('B')
print(E,flush=True)
x=S.symbols('x'); e=[1,*E,B]; p=sum((-1)**j*e[j]*x**(5-j) for j in range(6)); h=sum((-1)**j*(60//(j+1))*e[j]*x**(5-j) for j in range(6))
r=S.resultant(p,h-60*p,x)
print(len(S.Poly(r,*E,B).terms()),flush=True)
terms=json.loads(re.search(r'const resTerms = (\[[^\n]+\]);',checker).group(1))
ans=B**4
for a,k,n,d in terms: ans+=S.Rational(n,d)*B**(4-k)*S.prod(z**u for z,u in zip(E,a))
assert S.expand(r-50**5*B*ans)==0
print('PASS independent symbolic resultant all 59 monomials; denominator 50^5 B^5.',flush=True)
from fractions import Fraction as F
import random, json, subprocess
from collections import Counter
from itertools import combinations
from math import prod
P=2**17
JS=re.sub(r"const shard = process\.argv\[3\][^\n]+","const shard=Number(process.argv[1]);",checker.split('const initial=')[0])+"\nconst input=JSON.parse(require('fs').readFileSync(0,'utf8'));console.log(JSON.stringify(input.map(v=>evalbox(v.concat(v)))));"
def add(z,t):return (z[0]+t[0],z[1]+t[1])
def mul(z,t):return (z[0]*t[0]-z[1]*t[1],z[0]*t[1]+z[1]*t[0])
def inv(z):
    d=n2(z);return (z[0]/d,-z[1]/d)
def n2(z):return z[0]**2+z[1]**2
def powz(z,k):
    a=(F(1),0)
    for _ in range(k):a=mul(a,z)
    return a
def arc(t):return ((1-t*t)/(1+t*t),2*t/(1+t*t))
def pair(z):return [z,(z[0],-z[1])]
def check(ids,sh,cut):
    p,q,r,s=(F(x,P) for x in ids)
    one=(F(1),0)
    if sh==0:w=[one,(p,0),(q,0)]+pair((r,s)); good=p<=q
    elif sh==1:w=pair(arc(s))+[(p,0),(q,0),(r,0)];good=p<=q<=r
    elif sh==2:w=[one]+pair((p,q))+pair((r,s));good=p<=r
    else:w=pair(arc(p))+pair((q,r))+[(s,0)];good=True
    good=good and all(n2(z)<=1 for z in w)
    if cut==1:assert not good;return
    if not good:return
    if not all(n2(z) for z in w):return
    e=[one]
    for z in w:
        e=[add(x,mul(z,y)) for x,y in zip(e+[(0,0)],[(0,0)]+e)]
    assert all(y==0 for x,y in e)
    E=[z[0] for z in e]
    hs=[]
    for z in w:
        h=(0,0); u=inv(z)
        for j,v in reversed(list(enumerate(E))):
            h=add(mul(h,u),((-1)**j*v/(j+1),0))
        hs.append(h)
    vals=list(map(n2,hs))
    assert min(vals)<=F(25,36)
    if cut==2:assert min(vals)<F(25,36)
    if cut==3:assert 7*sum(map(abs,E[1:5]))<=abs(E[5])
    if cut==4:assert prod(vals)<F(25,36)**5
rr=random.Random(124031)
for sh in range(4):
    pts=[]
    for i in range(850):
        ss=[rr.randrange(-16,17)*P//16 for k in range(4)]
        if sh==0:ss[0:2]=sorted(ss[0:2]);ss[3]=abs(ss[3])
        if sh==1:ss[0:3]=sorted(ss[0:3]);ss[3]=abs(ss[3])
        if sh==2:ss[1]=abs(ss[1]);ss[3]=abs(ss[3])
        if sh==3:ss[0]=abs(ss[0]);ss[2]=abs(ss[2])
        pts.append(ss)
    if sh==2 or sh==3:
        # Rational inner perturbations of 5th roots, including coincidences.
        base=([-106039,77042,40503,124656] if sh==2 else [95229,-106039,77042,P])
        for i in range(1200):
            d=[rr.randrange(-4500,4501) for _ in range(4)]
            pts.append([max(-P,min(P,x+y)) for x,y in zip(base,d)])
    cuts=json.loads(subprocess.check_output(['node','-e',JS,str(sh)],input=json.dumps(pts).encode()))
    for a,c in zip(pts,cuts):check(a,sh,c)
    print('PASS shard',sh,len(pts),dict(sorted(Counter(cuts).items())),flush=True)
