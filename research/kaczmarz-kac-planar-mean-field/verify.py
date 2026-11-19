"""Finite consistency checks in rational arithmetic; not a substitute for the proof."""
from fractions import Fraction as Q
from itertools import product
from math import gcd

def check(x,message):
    if not x: raise ArithmeticError(message)

def direction(p):
    d=gcd(abs(p[0]),abs(p[1]));return tuple(x//d for x in p)
def sgn(x):return int(x>0)-int(x<0)
def dot(x,y):return x[0]*y[0]+x[1]*y[1]
dirs=sorted({direction((i,j)) for i,j in product(range(-5,6),repeat=2) if i or j})
cnt=0
for a,b in product(dirs,repeat=2):
    P=tuple(dot(b,b)*i-dot(a,b)*j for i,j in zip(a,b))
    if P==(0,0):continue  # ties have zero measure for independent densities
    out=direction(P);orth=((-b[1],b[0]),(b[1],-b[0]))
    check([x for x in orth if dot(a,x)>0]==[out],'projection direction')
    nb=tuple(-i for i in b);check(tuple(dot(nb,nb)*i-dot(a,nb)*j for i,j in zip(a,nb))==P,'pivot negation')
    cnt+=1
print('nonparallel exact planar updates and negative-pivot symmetry:',cnt)

# A monotone quarter-equivariant cumulative-mass map with flat intervals.
# coordinates are turns; four segments in each quarter, slopes 0,1,0,3.
def H(x):
    k=x//Q(1,4);y=x-k*Q(1,4);z=k*Q(1,4)
    return z+sum(v*max(Q(0),min(Q(1,16),y-j*Q(1,16))) for j,v in enumerate([0,1,0,3]))
def pos(x,y):
    t=(y-x)%1
    return t<Q(1,4) or t>Q(3,4)
supp=[Q(2*j+1,192) for j in range(96) if (j//6)%4 in (1,3)]
tested=0
for x,y in product(supp,repeat=2):
    if (y-x)%1 in (Q(1,4),Q(3,4)): continue
    check(H(x+Q(1,4))==H(x)+Q(1,4) and pos(x,y)==pos(H(x),H(y)),'CDF folding')
    tested+=1
print('half-circle membership after nonuniform CDF with gaps:',tested)

# For u=c+A cos x+B cos(3x), L-c*pi=2A cos x-2B cos(3x)/3.
# Work with rational points on the unit circle.
def formula(C,S,A,B):
    cs3=4*C**3-3*C; sn3=3*S-4*S**3
    L0=2*A*C-Q(2,3)*B*cs3
    # a(x+w)=2(u_odd)(x+w)
    return 2*(-A*S+B*sn3)*L0
count=0
for k in range(1,14):
    p=Q(k,17); C=(1-p*p)/(1+p*p); S=2*p/(1+p*p)
    for A,B in product([Q(1,100),Q(-1,77),Q(2,99)],repeat=2):
        sin4=4*S*C*(C*C-S*S)
        check(formula(C,S,A,B)+formula(-S,C,A,B)==Q(16,3)*A*B*sin4,'written PDE limit')
        count+=1
print('first/third-harmonic nonlinear term in the printed equation:',count)

# All retained nonzero absolute Fourier multipliers divided by 2/pi.
ms=[Q(abs((0,1,0,-1)[j%4]),j) for j in range(1,501)]
check(ms[0]==1 and max(ms[1:])==Q(1,3),'sign kernel multipliers')
print('sign-kernel multiplier comparisons:',len(ms))
