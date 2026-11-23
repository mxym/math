from fractions import Fraction as Q
from math import comb, factorial as fac, isqrt

def ck(x, label):
    if not x:
        raise ValueError(label)

def add(p,q):
    return [ (p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(max(len(p),len(q))) ]
def mul(p,q):
    r=[Q(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):
            r[i+j]+=a*b
    return r
def sc(p,a):
    return [a*x for x in p]
def po(p,n):
    r=[Q(1)]
    for _ in range(n):
        r=mul(r,p)
    return r
def der(p,n=1):
    for _ in range(n):
        p=[i*p[i] for i in range(1,len(p))]
    return p or [Q(0)]
def val(p,x):
    v=Q(0)
    for a in reversed(p): v=v*x+a
    return v
def integ(p):
    return sum(x/Q(i+1) for i,x in enumerate(p))
def bern(p):
    D=len(p)-1
    return max(abs(sum(p[j]*Q(comb(i,j),comb(D,j)) for j in range(i+1))) for i in range(D+1))
def l1(p,n=512):
    return sum(abs(val(p,Q(2*i+1,2*n))) for i in range(n))/n+bern(der(p))/(4*n)
def ceilroot(x,scale=10**12):
    if x<=0: return Q(0)
    n=isqrt(x.numerator*scale**2//x.denominator)
    return Q(n+1,scale)
def floorroot(x,scale=10**12):
    n=isqrt(x.numerator*scale**2//x.denominator)
    return Q(n,scale)
def upperpow(x,p,q,scale=10**14):
    trg=(x**p).numerator*scale**q//(x**p).denominator
    u=1
    while u**q<=trg: u*=2
    l=0
    while l+1<u:
        m=(l+u)//2
        if m**q<=trg: l=m
        else: u=m
    return Q(u,scale)
def loglo(x,n=52):
    z=(x-1)/(x+1)
    return 2*sum(z**(2*j+1)/(2*j+1) for j in range(n))
def atans(x,n):
    return sum((-1)**j*x**(2*j+1)/(2*j+1) for j in range(n))
pilo=Q('3.141592653589'); pihi=Q('3.141592653590')
pil=16*atans(Q(1,5),12)-4*atans(Q(1,239),11)
pih=16*atans(Q(1,5),11)-4*atans(Q(1,239),12)
ck(pilo<pil<pih<pihi, 'Machin pi')

A=Q(23,5); nu=Q(51,40); C2=Q(9,4)
def j1up(v):
    return sum((-1)**k*v**(2*k+1)/(2**(2*k)*(2*k+1)*fac(2*k+1)) for k in range(7))
def j2up(v):
    return sum((-1)**(k+1)*v**(2*k)/(2*k*fac(2*k)) for k in range(1,42))
J1p=[Q(0)]*13
for k in range(7):
    J1p[2*k]=Q((-1)**k,2**(2*k)*fac(2*k+1))
v=2*pihi
# Exact monotonicity for the upper primitive on [2*pi_lo,2*pi_hi].
ck(val(J1p,v)-sum(abs(z)*7**i for i,z in enumerate(der(J1p)))*2*(pihi-pilo)>0,'terminal sine polynomial')
ck(1<loglo(A) and Q(1,4)<loglo(C2), 'v<=1')
ck(1<loglo(3) and Q(1,2)<loglo(Q(48,25)), 'small phase constants')
for k in range(1000,6284):
    # the last interval uses the first-period endpoint; j1up is increasing
    # up to the slightly higher rational pihi*2 on this terminal interval.
    lo=Q(k,1000); hi=min(Q(k+1,1000),2*pihi)
    ck(hi>=lo and j1up(hi)-nu*loglo(lo)<loglo(A), ('J1',k))
for k in range(315):
    lo=Q(k,100); hi=Q(k+1,100)
    ck(lo**2/2-hi**4/96-4*hi/pilo>-1, ('primitive',k))
ck(j1up(2*pihi)-nu*loglo(2*pilo)+1/(2*pilo)<loglo(A), 'J1 tail')
for k in range(100,2000):
    lo=Q(k,100); hi=Q(k+1,100)
    ck(j2up(hi)-loglo(lo)<loglo(C2), ('J2', k))
ck(sum(Q(1,i) for i in range(1,1001))-9*loglo(2)-loglo(Q(125,64))<Q('.578'), 'Euler constant')
ck(Q('0.678')<loglo(2), 'J2 tail')

b=Q(1,5000); k=Q(9,2); c=k*b; d=c+Q(1,10**8); w=20*b
v0=1-c-b
E=Q(3,5)
F=[Q(1),Q(-2),Q(-16),Q(64),Q(-80),Q(32)]
B=[Q(0),Q(0),Q(0),Q(10),Q(-15),Q(6)]
left=mul(po([Q(1),Q(-1)],4),
         [sum(F[j]*(-E)**j*comb(i-j+3,3) for j in range(i+1)) for i in range(4)])
f=lambda p:add(sc(po(p,3),16),sc(po(p,5),-32))
taper=f([d,w])
C0=l1(left)*E+Q(1,2)
C4=l1(der(left,4))/E**3+Q(480)+(l1(der(mul(taper,B),4))+60*(val(taper,0)+val(taper,1)))/w**3
ck(C0<Q('1.203') and C4<Q('7316.488'), (float(C0),float(C4)))
C0=Q('1.203'); C4=Q('7316.488')

m0=-32*b+288*b*b-Q(2720,3)*b**3+Q(3040,3)*b**4
# rho factorial and the Buchstab factorial error at 1/(2b)=2500.
# On t in [1/2,infty), |F'(t)| <= 600(1+t^4).
# Bound rho(t/b) on each interval kb<=t<(k+1)b.
kb=2500
ck(Q(3000*(kb+2)**4,fac(kb-1))/b < Q(1,10**12), 'ordinary error')
# e0^0 integral and e0/s integral. On taper for latter, use s>=d.
base=16*d**4/4-32*d**6/6
base_s=16*d**3/3-32*d**5/5
taper_mass=w*integ(mul(taper,add([Q(1)],sc(B,-1))))
BD=(base+taper_mass)/b**2
UD=2/b*(base_s+taper_mass/d)+Q(2,3)*BD
BV=(2/(pilo*v0))*(C0*b**5/80+C4*upperpow(b,69,40)*(A/(40*(nu+2))+4*A*A/((k-1)*(3-2*nu))))
BX=(2/(pilo*floorroot(v0)))*(C0*C2*b**5/60+C4*b*b*(C2/30+Q(8,3)*C2*ceilroot(32/(k-1))))
debit=-2*m0+m0*m0+Q('3.446')*(BD+BV)+(BD+2*BV)*UD+Q('0.8')/b*BX**2+Q(1,10**8)
ck(debit<Q('.456'), 'combined debit')
print("BV",float(BV),"BX",float(BX),"BD",float(BD),"UD",float(UD),"debit",float(debit))
