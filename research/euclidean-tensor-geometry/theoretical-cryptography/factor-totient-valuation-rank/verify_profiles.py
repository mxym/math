"""Exact checks on labeled finite inputs, not a factorization implementation."""
from fractions import Fraction as F
from itertools import combinations
from math import gcd, isqrt, prod

def prime(p): return p>1 and all(p%i for i in range(2,isqrt(p)+1))
def val(n,p):
    e=0
    while n%p==0:e+=1;n//=p
    return e
def rank(M):
    B=[[F(x) for x in row] for row in M];i=0
    for j in range(len(B[0])):
        s=next((s for s in range(i,len(B)) if B[s][j]),None)
        if s is None:continue
        B[i],B[s]=B[s],B[i];q=B[i][j];B[i]=[x/q for x in B[i]]
        for h in range(len(B)):
            if h!=i:
                z=B[h][j];B[h]=[a-z*b for a,b in zip(B[h],B[i])]
        i+=1
    return i
def det(M):
    if not M:return 1
    return sum((-1)**j*x*det([r[:j]+r[j+1:] for r in M[1:]]) for j,x in enumerate(M[0]))
def adj(M):
    return [[(-1)**(i+j)*det([r[:i]+r[i+1:] for r in M[:j]+M[j+1:]]) for j in range(len(M))] for i in range(len(M))]
def floor_root(x,d):
    l,h=0,1
    while h**d*x.denominator<=x.numerator:h*=2
    while h-l>1:
        m=(h+l)//2
        if m**d*x.denominator<=x.numerator:l=m
        else:h=m
    return l
def block(n,T,r):
    b,a=r.numerator,r.denominator
    nb,ta=n**b,T**a; J=gcd(nb,ta);w=(nb//J)*(ta//J)
    return n//gcd(n,pow(w,n.bit_length(),n))

roots5=(1013,1103,1451,1481,1511); large=[(p,2*p+1,6*p+1) for p in roots5]
small=[(19,191,229),(23,47,139),(29,59),(41,83)]
dsmall=[(1,2),(1,3),(2,),(3,)]
tests=[("five-full",large,[(1,2),(2,3),(3,4),(4,5),(5,1)],5),
       ("five-deficient",large,[(1,1),(1,2),(2,3),(3,4),(4,4)],4),
       ("four-cycle",large[:4],[(1,2),(2,3),(3,4),(4,1)],3),
       ("four-mixed",small,dsmall,3)]
raychecks=edges=dfs_visits=0;windows=[]
for name,trees,ex,expected in tests:
    ntrees=len(trees);S=[p for tr in trees for p in tr]; assert len(set(S))==len(S) and all(map(prime,S))
    intended={(tr[0],q) for tr in trees for q in tr[1:]}
    assert {(p,q) for p in S for q in S if (q-1)%p==0}==intended
    edges+=len(intended)
    A=(max(S)+min(S)-1)//min(S); assert A==(13 if name=="four-mixed" else 9)
    ep={p:e for tr,e0 in zip(trees,ex) for p,e in zip(tr,(1,)+tuple(e0))}
    N,T=prod(p**ep[p] for p in S),prod(p**(ep[p]-1)*(p-1) for p in S)
    groups={p:F(val(T,p),ep[p]) for p in S}
    assert all(groups[p]==F(ep[p]-1+sum(a==p for a,q in intended),ep[p]) for p in S)
    R=sorted(set(groups.values()))
    for r in {F(e-1+d,e) for e in range(1,8) for d in range(4)}:
        assert block(N,T,r)==prod(p**ep[p] for p in S if groups[p]==r)
        raychecks+=1
    M=[[sum(ep[p] for p in tr if groups[p]==r) for tr in trees] for r in R]
    assert all(sum(x!=0 for x in row)>1 for row in M) and rank(M)==expected
    if name=="five-deficient":
        assert all(sum(a*b for a,b in zip(row,(1,-2,2,-2,1)))==0 for row in M)
    if name=="four-cycle":
        assert all(sum(a*b for a,b in zip(row,(1,-1,1,-1)))==0 for row in M)
    if name=="five-full":
        leafrows=[i for i,r in enumerate(R) if r<1];A0=[M[i] for i in leafrows]
        M0=[[x//(1/(1-R[i])).numerator for x in M[i]] for i in leafrows]
        assert abs(det(M0))==2
        C={r:prod(((p-1)//tr[0])**ep[p] for tr in trees for p in tr[1:] if groups[p]==r) for r in R}
        h=[F(block(N,T,R[i]),C[R[i]]) for i in leafrows]
        delta=det(A0);ai=adj(A0)
        for i,tr in enumerate(trees):
            so=prod(v**((1 if delta>0 else -1)*w) for v,w in zip(h,ai[i]))
            m=floor_root(so,abs(delta));windows.append(m-tr[0])
            assert m**abs(delta)*so.denominator<=so.numerator<(m+1)**abs(delta)*so.denominator
            assert abs(m-tr[0])<=2 # descriptive property of this fixture only
    for tr in trees:
        for start in tr:
            seen=set();todo=[start]
            while todo:
                p=todo.pop()
                if p in seen:continue
                seen.add(p);u=gcd(N,p-1)
                if u>1:todo.append(u)
                todo.extend(m*p+1 for m in range(1,A+1) if N%(m*p+1)==0 and prime(m*p+1))
            assert seen==set(tr);dfs_visits+=1
    print(name,"nodes",len(S),"components",ntrees,"observed rank",expected)
print("checked profile blocks",raychecks,"true edges across fixtures",edges,"DFS starts",dfs_visits)
print("full-rank floor-center minus true root",*windows)
