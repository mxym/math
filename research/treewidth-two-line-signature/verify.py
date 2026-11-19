#!/usr/bin/env python3
"""Rational two-port closure. Only one internal variable is eliminated per operation."""
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from collections import Counter
def check(p,m):
    if not p: raise ArithmeticError(m)
def sign(x): return int(x>0)-int(x<0)
Y=(F(0),F(2,3),F(2),F(4))
def full(C,a,b,d): return (C,2,(F(a),F(b),F(d)))
def line(C,x,y,h): return (C,1,(F(x),F(y),F(h)))
def orbit(A):
    C,dim,p=A
    if dim==2:
        a,b,d=p
        return {full(C,i,e,j) for i,j in ((a,d),(d,a)) for e in (b,-b)}
    if dim==0:return {A}
    a,b,h=p
    out=set()
    for x,y in [(a,b),(b,a)]:
        for z in (y,-y):
            u=x or z;out.add(line(C,x/u,z/u,h/u**2))
    return out
def table():
    S={full(i+j-1,Y[i],0,Y[j]) for i,j in combinations_with_replacement(range(4),2)}
    for tag in (0,1,3):
        S.add(full(tag,1,1,1+Y[tag]));S.add(line(tag,1,1,2+Y[tag]))
    S|={full(-1,F(-1,2),F(3,2),F(-1,2)),full(1,F(3,4),F(1,4),F(3,4))}
    return S,set.union(*(orbit(A) for A in S))
def zmat():return [[F(0)]*3 for _ in range(3)]
def add(M,L,A,i,j):
    C,k,p=A
    if k==2:
        a,b,d=p;M[i][i]+=a;M[j][j]+=d;M[i][j]+=b;M[j][i]+=b
    elif k==1:
        v,w,h=p; z=[F(0)]*3;z[i]=w;z[j]=-v;L.append(z)
        # Basis (v,w) is normalized by the first nonzero component.
        j0=i if v else j;M[j0][j0]+=h
    else:
        for t in (i,j):
            z=[F(0)]*3;z[t]=1;L.append(z)
    return C
def reduce(C,M,L,forget=False):
    a,b,d=M[0][0],M[0][1],M[1][1]; g,h,k=M[0][2],M[1][2],M[2][2]
    if forget:
        row=next((r for r in L if r[2]),None)
        if row:
            u,v=-row[0]/row[2],-row[1]/row[2]
            a+=2*g*u+k*u*u; b+=g*v+h*u+k*u*v; d+=2*h*v+k*v*v
            R=[(r+s*u,t+s*v) for r,t,s in L]
        else:
            R=[(r,t) for r,t,s in L]
            if k:
                a-=g*g/k;b-=g*h/k;d-=h*h/k;C-=2*sign(k)
            else:R.append((g,h))
    else:
        check(not g and not h and not k and all(not s for r,t,s in L),'unused coordinate')
        R=[(r,t) for r,t,s in L]
    R=[(r,t) for r,t in R if r or t]
    if not R:return full(C,a,b,d)
    p,q=R[0];x,y=q,-p
    if any(r*x+t*y for r,t in R):return (C,0,())
    u=x or y;x,y=x/u,y/u
    return line(C,x,y,a*x*x+2*b*x*y+d*y*y)
def val(A,x,y):
    C,k,p=A
    if k==2:
        a,b,d=p;return a*x*x+2*b*x*y+d*y*y
    if k==1:return p[2]*(x*x if p[0] else y*y)
    return 0
def dom(A,B):
    """Sufficient for A <= B for every host and every boundary map (not a heuristic)."""
    c,k,p=A;d,l,q=B;m=min(k,l)
    if k==l==1 and p[:2]!=q[:2]:m=0
    budget=c-d-2*(k+l-2*m)
    if budget<0:return False
    if not m:return True
    if m==1:
        x,y=(p if k==1 else q)[:2]
        return budget>=4*int(val(A,x,y)>val(B,x,y))
    a,b,d=(i-j for i,j in zip(p,q));det=a*d-b*b
    npos=(2*int(a+d>0) if det>0 else int(det<0 or a+d>0))
    return budget>=4*npos
def combine(A,B,series):
    M,L=zmat(),[]
    if series:
        C=add(M,L,A,0,2)+add(M,L,B,2,1);M[2][2]-=2
    else:C=add(M,L,A,0,1)+add(M,L,B,0,1)+3
    return reduce(C,M,L,series)
def decoration(A,c,i):
    M,L=zmat(),[];C=add(M,L,A,0,1)+c;M[i][i]+=Y[c];return reduce(C,M,L)
def close(A):
    M,L=zmat(),[];C=add(M,L,A,0,2);M[2][2]-=2
    return reduce(C,M,L,True) # terminal 1 is a completely unused dummy
def main():
    proto,pool=table();pool=sorted(pool)
    check(len(proto)==18 and len(pool)==36,'state-table size')
    checks=Counter()
    def seek(o,targets,key):
        check(any(dom(o,b) for b in targets),(key,o));checks[key]+=1
    check(full(0,1,1,1) in pool,'base edge')
    for a,b in product(pool,repeat=2):
        for series in (True,False):seek(combine(a,b,series),pool,'series' if series else 'parallel')
    for a,c,i in product(pool,range(4),range(2)):seek(decoration(a,c,i),pool,'decorate')
    one=[full(c,y,0,0) for c,y in enumerate(Y)]
    for a in pool:seek(close(a),one,'forget')
    end=[2*sign(y-2)-c for c,y in enumerate(Y)]
    check(end==[-2,-3,-2,-1],'root')
    print('PASS representatives=18 orientations=36; base=ordinary edge')
    for key in ['series','parallel','decorate','forget']:print('PASS',key,checks[key])
    print('PASS terminal root budgets',end,'maximum',max(end))
if __name__=='__main__':main()
