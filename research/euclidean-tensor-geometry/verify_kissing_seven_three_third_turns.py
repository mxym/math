#!/usr/bin/env python3
"""Six-to-seven-dimensional independent C3 action: exact finite parts."""
from fractions import Fraction as Q
from math import isqrt
from itertools import combinations,combinations_with_replacement,product
if not __debug__:raise RuntimeError("Run without -O or -OO.")
D=16;S=10000
def coslo(j):
    # Angle j*pi/(3D), 0<=j<=D. cos decreases on this interval and
    # the alternating Taylor polynomial ending in degree 10 is a lower bound.
    if j==D:return S//2
    u=Q(355*j,113*3*D);term=tot=Q(1)
    for k in range(1,6):
        term*= -u*u/((2*k)*(2*k-1));tot+=term
    return (S*tot).__floor__()
COS=tuple(coslo(i)for i in range(D+1))
SQ=tuple(isqrt(i*S*S//D)for i in range(2*D+1))
def info(v,w):
    A,B,l,r=v
    if A+B>D:return None
    x,y=SQ[D+A],SQ[D+B];z=SQ[max(0,D-A-B-2*w)]
    if 2*(x*COS[l+w]+y*COS[r+w])>3*S*S:return None
    return x,y,z
def compatible(v,u,w):
    x,y,z=info(v,w);X,Y,Z=info(u,w)
    def c(i):
        t=v[i]+u[i]
        return COS[min(D,t+2*w,2*D-t)]
    return 2*(x*X*c(2)+y*Y*c(3)+z*Z*S)<=3*S**3
w=4;boxes=[v for v in product(range(0,D,w),repeat=4)if info(v,w)!=None]
pairs=[(v,u)for v,u in combinations_with_replacement(boxes,2)if compatible(v,u,w)]
history=[len(pairs)]
while pairs and w>1:
    w//=2
    def child(u):
        q=[tuple(a+b for a,b in zip(u,ds))for ds in product((0,w),repeat=4)]
        return [v for v in q if info(v,w)!=None]
    subs={v:child(v)for pair in pairs for v in pair};new=[]
    for a,b in pairs:
        p=combinations_with_replacement(subs[a],2)if a==b else product(subs[a],subs[b])
        new.extend((v,u)for v,u in p if compatible(v,u,w))
    pairs=new;history.append(len(pairs))
assert history==[163,16,0]
print('Continuous one-triple compatibility: surviving box pairs',history)
# With i incident edges at positive height and j at negative height, the
# following are the proven per-axis bounds on the number of triangle POINTS.
def axis(i,j):
    if i>j:return axis(j,i)
    if j==2:return 9 if i==0 else 6
    if (i,j)==(1,1):return 9
    return 12
P=[(0,1),(1,2),(2,0)];masks=[{e for i,e in enumerate(P)if k>>i&1}for k in range(8)]
for plus,minus in product(masks,repeat=2):
    tot=len(plus)+len(minus)
    if tot<4:continue
    assert plus and minus
    q=sum(axis(sum(i in e for e in plus),sum(i in e for e in minus))for i in range(3))
    assert 54+9*tot+q<119 if tot<6 else 54+9*tot+q==126
assert Q(5,12)<Q(1,2) and 3*119**2>194**2
# The same-sign height cutoff at 5/12: 5/12+sqrt(119)/24>sqrt(3)/2,
# e.g. sqrt(119)>109/10 while sqrt(3)<26/15.
assert 109**2<119*100 and 26**2>3*15**2
assert Q(5,12)+Q(109,240)>Q(26,30)

# Eisenstein phases in scales sqrt(3)*x. A root or twisted layer is encoded as
# three coordinates a+b*omega followed by one real integer height.
def neg(v):return tuple(-x for x in v)
def rot(p):return -p[1],p[0]-p[1]
A=[(1,0)];A.extend([rot(A[0]),rot(rot(A[0]))]);zero=(0,0)
T={sum(u,())+(0,)for u in product(A,repeat=3)}
eq=T|{neg(v)for v in T};Z=(2,1)
for i in range(3):
    for s in range(3):
        z=(0,0)*i+Z+(0,0)*(2-i)+(0,);eq.update((z,neg(z)));Z=rot(Z)
assert len(eq)==72
def layer(sign,h):
    out=set()
    for i,j in P:
        for a,b in product(A,repeat=2):
            k=[zero]*3;k[i]=a;k[j]=neg(b)
            v=sum(k,());out.add(tuple(sign*z for z in v)+(h,))
    return out
def dot6(x,y):
    return 2*x[-1]*y[-1]+sum(2*a*c-a*d-b*c+2*b*d for a,b,c,d in zip(x[:6:2],x[1:6:2],y[:6:2],y[1:6:2]))
for s in [-1,1]:
    U=eq|layer(1,1)|layer(s,-1)
    assert len(U)==126 and all(dot6(v,v)==6 for v in U)
    vals={dot6(v,w)for v,w in combinations(U,2)}
    assert max(vals)==3 and sum(neg(v)in U for v in U)==(126 if s==-1 else 72)
    if s==-1:
        assert vals=={-6,-3,0,3}
        for v,w in product(U,repeat=2):
            u=dot6(v,w);assert u%3==0 and tuple(a-u//3*b for a,b in zip(v,w))in U
    print('126-point layer choice',s,'distinct scaled products',sorted(vals),'paired axes',sum(neg(v)in U for v in U)//2)
