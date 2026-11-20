"""Separate polynomial-arithmetic/rank verifier; only standard Python."""
from itertools import combinations
from collections import Counter
from pathlib import Path
from math import comb

assert __debug__
def m(a,b):
    z=(b&1)*a
    if b&2:z^=(a<<1)
    if z&4:z^=7
    return z
def scale(a,v):return sum(m(a,(v>>(2*i))&3)<<(2*i) for i in range(6))
def conj(v):return sum(m(x,x)<<(2*i) for i in range(6) for x in [(v>>(2*i))&3])
def normal(x):
    assert 0<x<4096
    a=(x>>(2*((x.bit_length()-1)//2)))&3
    return scale(m(a,a),x)
def rank(S):
    rows={}
    for x in S:
        while x:
            i=(x.bit_length()-1)//2;a=(x>>(2*i))&3
            if i not in rows:
                rows[i]=scale(m(a,a),x);break
            x^=scale(a,rows[i])
    return len(rows)
def sg(a,b):
    z=0
    for i in range(6):z^=m((a>>(2*i))&3,(b>>(2*i))&3)
    return z
def mul64(x,y):
    # Coefficients over F4, followed by reduction modulo u^3+u+1.
    c=[0]*5
    for i in range(3):
        for j in range(3):c[i+j]^=m(x>>(2*i)&3,y>>(2*j)&3)
    for i in (4,3):c[i-2]^=c[i];c[i-3]^=c[i]
    return c[0]+4*c[1]+16*c[2]
def pw(x,k):
    z=1
    for _ in range(k):z=mul64(z,x)
    return z
assert all(pw(x,63)==1 for x in range(1,64))
reps=[list(map(int,l.split()))for l in Path('extrema21.txt').read_text().splitlines()]
assert len(reps)==2 and set(reps[0])=={normal(x+64*pw(x,61))for x in range(1,64)}
spectra=[]
for S in reps:
    assert len(S)==len(set(S))==21 and rank(S)==6
    assert all(rank(T)==4 for T in combinations(S,4))
    spectra.append(sorted(Counter(sum(not sg(h,x)for x in S)for h in range(1,4096)if normal(h)==h).items()))
assert [dict(x)[9]for x in spectra]==[63,72]
print('PASS independent rank tests and hyperplane spectra:',spectra)
# A 22-column parity-check matrix with no three dependent exists, giving d>=4.
S=reps[0]
x=next(x for x in range(1,4096)if normal(x)==x and all(rank([x,y,z])==3 for y,z in combinations(S,2)))
assert rank(S+[x])==6 and min(rank(T)for T in combinations(S+[x],4))==3
print('PASS optimum-code lower witness: first 21-set plus column',x)
def matrix_check(src,ff,mat,idx):
    assert len(src)==21 and ff in (0,1) and len(mat)==6 and rank(mat)==6
    a=[]
    for x in src:
        if ff:x=conj(x)
        y=0
        for i,p in enumerate(mat):y^=scale((x>>(2*i))&3,p)
        a.append(normal(y))
    assert set(a)==set(reps[idx])
cert=Counter();uses=Counter()
for l in Path('maps21b.txt').read_text().splitlines():
    a,b=l.split('|');i,*S=map(int,a.split());ff,*mat=map(int,b.split());matrix_check(S,ff,mat,i)
    cert[tuple(sorted(S))]+=1;uses[i]+=1
assert uses=={0:2,1:24}
l=Path('twist.txt').read_text();a,b=l.split('|');ff,*mat=map(int,b.split())
assert ff==1 and set(map(int,a.split()))==set(reps[1]);matrix_check(reps[1],ff,mat,1)
print('PASS 26 explicit collineations and nontrivial field automorphism stabilizer of second orbit.')
for n,val in [(21,1302),(22,6704)]:
    ms=[comb(n,t)*(4**(6-t)-1)//3 for t in range(4)]
    assert sum(x*y for x,y in zip(ms,[-28,22,-16,6]))==val
expected={9:[32,66,121,11],10:[22,18,28,26],11:[3]}
for name in ('plane','sec'):
    for n in (21,22):
        S=Counter();nodes=0
        for h,ks in expected.items():
            seen=set()
            p=Path(f'{name}_{h}_{n}.log')
            for l in p.read_text().splitlines():
                v=l.split()
                if v[0]=='FOUND':
                    a=tuple(sorted(map(int,v[1:])))
                    assert len(a)==n and len(set(a))==n and all(rank(T)==4 for T in combinations(a,4))
                    S[a]+=1
                else:
                    assert v[0]=='BRANCH' and len(v)==7
                    hn,nn,i,o,k,z=map(int,v[1:])
                    assert (hn,nn)==(h,n) and 1<=i<=len(ks) and k==ks[i-1] and 0<=o<k
                    assert (i,o)not in seen and z>=0
                    seen.add((i,o));nodes+=z
            assert seen=={(i,o)for i,k in enumerate(ks,1)for o in range(k)}
        assert S==(cert if n==21 else Counter())
        print('PASS',name,'n=',n,'327 complete branches,',sum(S.values()),'solutions,',nodes,'search nodes.')
