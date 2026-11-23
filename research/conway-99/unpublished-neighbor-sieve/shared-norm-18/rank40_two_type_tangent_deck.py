"""Exact rank-40 tangent-line deck on the two-type face. Standard library."""
from itertools import product

P=7
def q(x):
    return (sum(a*a for a in x[:3])+3*x[3]*x[3])%7
def ip(x,y):
    return (sum(a*b for a,b in zip(x[:3],y[:3]))+3*x[3]*y[3])%7
def neg(x):
    return tuple(-a%7 for a in x)
def opp(x):
    return min(x,neg(x))

pts=list(product(range(7),repeat=4))
H=[x for x in pts if q(x)==0 and any(x) and next(a for a in x if a)==1]
assert len(H)==50
def equations(radius):
    S=[x for x in pts if q(x)==radius and x==opp(x)]
    ix={x:i for i,x in enumerate(S)}
    assert len(ix)==175
    out=[]
    for j,h in enumerate(H):
        lines=set()
        for x in S:
            if ip(x,h):continue
            ell=sorted(ix[opp(tuple((a+k*b)%7 for a,b in zip(x,h)))]
                       for k in range(7))
            assert len(set(ell))==7
            lines.add(tuple(ell))
        assert len(lines)==4
        assert len(set().union(*map(set,lines)))==28
        for ell in sorted(lines):
            row=[0]*225
            for i in ell:row[i]=1
            row[175+j]=-1
            out.append(row)
    return out

def rref(rows,p):
    a=[[v%p for v in row] for row in rows]
    r=0;piv=[]
    for j in range(len(a[0])):
        h=next((h for h in range(r,len(a)) if a[h][j]),None)
        if h is None:continue
        a[h],a[r]=a[r],a[h]
        u=pow(a[r][j],-1,p)
        a[r]=[(u*v)%p for v in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][j]:
                v=a[i][j];a[i]=[(s-v*t)%p for s,t in zip(a[i],a[r])]
        r+=1;piv.append(j)
        if r==len(a):break
    return piv,a[:r]
def conditions(q0,p):
    piv,rr=rref(equations(q0),p)
    n=sum(j<175 for j in piv)
    out=[row[175:] for row in rr[n:]]
    assert all(not any(row[:175]) for row in rr[n:])
    assert p==7 and (n,len(out))==(124,1)
    return out

for radius in (4,3):
    assert conditions(radius,7)==[[1]*50]
    print("radius",radius,": 50 tangencies, 175 projective points; last row is sum L_H = 0 modulo 7")
assert (50*(1-373))%7==6
print("all-one compatible coclique counts contradict the rank-40 deck: residue 6")
