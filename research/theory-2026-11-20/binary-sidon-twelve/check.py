"""Dependency-free exact replay. Normal Python and python -O perform identical checks."""
from functools import lru_cache
from itertools import product,combinations
from pathlib import Path
from math import prod
import ast,json,sys
ROOT=Path(__file__).resolve().parent
def ck(b,s='check failed'):
    if not b:raise ValueError(s)
def dot(a,b):
    ck(len(a)==len(b));return sum(x*y for x,y in zip(a,b))
def slabs(d,n,m):
    Q=1<<d
    return (Q*(3*n*n-2*n)-n**4)-(n%2+(2*m-n)**2)*(Q*n-n*n)+(Q-1)*(n%2)*(2*m-n)**2<=0
def shapes(n):
    for m in range((n+1)//2,49):
        if not slabs(12,n,m):continue
        for a in range((m+1)//2,m+1):
            if not slabs(11,m,a):continue
            for b in range((n-m+1)//2,n-m+1):
                A=(a,m-a,b,n-m-b)
                if max(x+y for x,y in combinations(A,2))<=m:yield m,a,A
# Independently recover orbit reps ordered by the first independent vectors:
# all vectors in the current span or one new basis direction.
def codes(length):
    def extend(t,S):
        if len(t)==length:yield t;return
        for v in S:yield from extend(t+(v,),S)
        yield from extend(t+(len(S),),tuple(range(2*len(S))))
    return extend((),(0,))
@lru_cache(None)
def profiles(A,m,a):
    R=2*m-sum(A);V=set()
    for x in product(*(range(-R+(R-v)%2,R+1,2)for v in A)):
        if any(abs(sum(x[i]*(-1)**((i&j).bit_count()%2)for i in range(4)))>R for j in range(4)):continue
        if any(abs(x[i])+abs(x[j])>2*a-m for i,j in combinations(range(4),2)if A[i]+A[j]==m):continue
        V.add((tuple(map(abs,x)), -1 if prod(x)<0 else 1))
    return V
def data(A,u,k,ols,g,tag,expect):
    # expect: values when summed over all 1024 characters; otherwise one character.
    Q=1024
    z=[Q if expect else 1]
    for a,x in zip(A,u):z.append(Q*a if expect else x*x)
    for a,x in zip(A,u):z.append(Q*(3*a*a-2*a) if expect else x**4)
    for i,j in combinations(range(4),2):z.append(Q*A[i]*A[j] if expect else (u[i]*u[j])**2)
    z.append(0 if expect else k*prod(u))
    if g is None:return z
    M=1<<max(g,default=0).bit_length()
    for b in range(M):z.append(Q//M if expect else int(b==tag))
    for d in range(1,M):
        c=1-2*((tag&d).bit_count()%2)
        for x in u:z.extend([0,2*Q] if expect else [-c*x*x,c*x*x])
        z.append(2*Q if expect else c*sum(x*x for x in u))
    return z
def verify(n):
    inp=json.loads((ROOT/f'cert{n}.json').read_text());D={}
    for key,v in inp.items():
        m,a,A,g=ast.literal_eval(key);D[m,a,tuple(A),None if g is None else tuple(g)]=v
    used=nv=0;worst=-10**50;shape=0
    for m,a,A in shapes(n):
        shape+=1;idx=[i for i in range(4)if A[i]%2==0]
        for g in ([None]if(m,a,A,None) in D else codes(len(idx))):
            v=D.pop((m,a,A,g));used+=1;M=1 if g is None else 1<<max(g,default=0).bit_length()
            eq=16+(M if g is not None else 0)
            ck(all(type(x)==int for x in v));ck(all(x>=0 for x in v[eq:]),'negative inequality multiplier')
            r=data(A,A,1,idx,g,0,True);v0=data(A,A,1,idx,g,0,False)
            cost=dot(v,[x-y for x,y in zip(r,v0)]);ck(cost<0,'nonnegative RHS');worst=max(cost,worst)
            labels={tuple((b&t).bit_count()%2 for t in g):b for b in range(M)} if g is not None else {}
            for u,k in profiles(A,m,a):
                tag=0
                if g is not None:
                    p=tuple((A[i]-u[i])//2%2 for i in idx)
                    if p not in labels:continue
                    tag=labels[p]
                ck(dot(v,data(A,u,k,idx,g,tag,False))>=0,'negative column');nv+=1
    ck(not D,'extra keys');print(f'n={n}: {shape} quarter shapes, {used} witnesses; {nv} valid profile checks; largest RHS {worst}. PASS')
if __name__=='__main__':
    for n in map(int,sys.argv[1:]or['84']):verify(n)
