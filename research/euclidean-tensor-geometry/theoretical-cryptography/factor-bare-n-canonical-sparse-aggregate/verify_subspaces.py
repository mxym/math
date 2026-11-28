"""Predetermined exact checks of gcd refinement and rational-span cube enumeration."""
from fractions import Fraction as F
from math import gcd,prod
from itertools import combinations,product

def atoms(ns):
    a=sorted({x for x in ns if x>1})
    while True:
        v=next(((x,y,gcd(x,y)) for x,y in combinations(a,2) if gcd(x,y)>1),None)
        if v is None:break
        x,y,g=v;old=prod(a)
        a=sorted((set(a)-{x,y})|({g,x//g,y//g}-{1}))
        assert prod(a)*g<=old
    return a

def coord(n,base):
    ex=[]
    for a in base:
        i=0
        while n%a==0:n//=a;i+=1
        ex.append(i)
    assert n==1
    return ex

def enc(q,base):
    a=coord(q.numerator,base);b=coord(q.denominator,base)
    return tuple(x-y for x,y in zip(a,b))

def rk(cols):
    if not cols:return 0
    t=list(map(lambda v:list(map(F,v)),cols));r=0
    for j in range(len(t[0])):
        p=next((i for i in range(r,len(t)) if t[i][j]),None)
        if p is None:continue
        t[r],t[p]=t[p],t[r];v=t[r][j];t[r]=[a/v for a in t[r]]
        for i in range(r+1,len(t)):t[i]=[a-t[i][j]*b for a,b in zip(t[i],t[r])]
        r+=1
    return r

def enum(cols,h,R):
    t=len(cols[0]);out={(0,)*t}
    for k in range(1,h+1):
        for A in combinations(cols,k):
            if rk(A)<k:continue
            I=next(ii for ii in combinations(range(t),k)
                   if rk([tuple(v[i] for i in ii) for v in A])==k)
            for z in product(range(-R,R+1),repeat=k):
                if k==1:
                    u=[F(z[0],A[0][I[0]])]
                else:
                    assert k==2
                    a,b=A[0][I[0]],A[1][I[0]]
                    c,d=A[0][I[1]],A[1][I[1]]
                    u=[F(d*z[0]-b*z[1],a*d-b*c),F(a*z[1]-c*z[0],a*d-b*c)]
                w=tuple(sum(u[j]*A[j][i] for j in range(k)) for i in range(t))
                if all(q.denominator==1 and abs(q)<=R for q in w):out.add(w)
    return out

def check(S):
    S=list(map(F,S));ns=[z for q in S for z in (q.numerator,q.denominator)]
    base=atoms(ns);V=[enc(q,base) for q in S]
    assert all(prod(F(a)**e for a,e in zip(base,v))==q for v,q in zip(V,S))
    R=1 if len(base)>3 else 2
    ans=[]
    for h in (0,1,2):
        got=enum(V,h,R)
        subs=sum([list(combinations(V,j)) for j in range(h+1)],[])
        ref={w for w in product(range(-R,R+1),repeat=len(base))
             if any(rk(t)==rk(t+(w,)) for t in subs)}
        assert got==ref;ans.append(len(got))
    return base,ans

for S in [[4,8,5],[F(15,14),F(33,26),F(77,65)],[6,35,210]]:
    base,n=check(S);print("atoms",base,"box counts h=0,1,2",n)
# 2=8/4 is in the saturated line of 4 but is not an integer power
# of any one of 4,8,5.
base=atoms([4,8,5]);V=[enc(F(z),base) for z in [4,8,5]]
assert enc(F(2),base) in enum(V,1,2)
assert all(all(F(z)**i!=2 for i in range(-12,13)) for z in [4,8,5])
print("saturated but not cyclic-word-of-one label",2)
