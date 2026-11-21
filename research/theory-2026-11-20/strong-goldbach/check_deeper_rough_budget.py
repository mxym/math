"""Exact upper bounds for the two disjoint deeper rough triprime charges."""
from fractions import Fraction as F
from math import comb,factorial

def f(x): return F(str(x))
def ck(ok, message):
    if not ok: raise RuntimeError(message)

def lnr(a,b):
    a,b=f(a),f(b)
    t=(b-a)/(b+a)
    base=2*sum((t**(2*k+1)/(2*k+1) for k in range(12)),F(0))
    return base,base+2*t**25/(25*(1-t*t))

def cube_r5(K=200, slabs=5):
    """Rational upper for rank-five added-adjustment coefficient."""
    UNIT=10000
    A=1100
    SCALE=10**12
    DEN=6*K**3*SCALE*72   # simplex-cell volume, reciprocal numerator, and 3*4!
    REC=SCALE*(K*UNIT)**4
    value=F(0)
    for h in range(slabs):
        p0=3110+100*h//slabs
        p1=3110+100*(h+1)//slabs
        Slo=UNIT-p1-4*A
        Shi=UNIT-p0-4*A
        z=(5000-p0-A)*K
        d=[K*A+Slo*i for i in range(K+1)]
        small=[i*Shi<=z for i in range(K+1)]
        subtotal=0
        for i in range((K-1)//3+1):
            for j in range(i,(K-i-1)//2+1):
                dd=d[i]*d[j]
                base=small[i]+small[j]-1
                for k in range(j,K-i-j):
                    s=K-i-j-k
                    l=max(0,s-3)
                    weight=base+small[k]+small[l]
                    if weight<=0: continue
                    volume=(1 if s==1 else 5 if s==2 else 6)
                    multiplicity=(1 if i==k else 3 if (i==j or j==k) else 6)
                    denom=dd*d[k]*d[l]
                    subtotal+=weight*volume*multiplicity*((REC+denom-1)//denom)
        value+=F(p1-p0,p0)*F(Shi,UNIT)**3*F(subtotal,DEN)
    return value

hE=lnr(".311",".321")
hQ=lnr(".297",".298")
I2=lnr(".679",".689")
h2=lnr(".164",".16524")
h3=lnr(".16525",".167")
h2n=lnr(".16512",".16524")
h3n=lnr(".16525",".16545")
hs=lnr(".138",".139")
hsn=lnr(".1384",".1386")
ha=lnr(".068",".069")
han=lnr(".0684",".0686")
d=f(".017")
W=lambda t: (1-t)*(1-2*t)**2
ratio_den=40*d*hQ[0]*hE[0]**2*(1-hE[1])

def hk(a,k):
    u=f(".689")
    if u<=k*a: return F(0)
    return hE[1]*(u-k*a)**(k-1)/(factorial(k-1)*factorial(k)*a**(k-1)*(u-(k-1)*a))

def rank_cap(a,k):
    if k==4: return F(3)
    if k%2:
        return min(F(2**(k-1)),
                   2*sum(comb(k,j)*max(F(0),f(".189")-j*a) for j in range(1,k+1,2)))
    return min(F(2**(k-1)),sum(comb(k,j) for j in range(1,k+1,2) if j*a<f(".189")))

b5=cube_r5()
ck(b5<=f(".002546403"),"rank-five rational integral")
ab=f(".110")
an=f(".055")
broad=h2[1]*h3[1]*(I2[1]+3*b5+sum(rank_cap(ab,k)*hk(ab,k) for k in (5,6)))/ratio_den
narrow= f("7.3")*hsn[1]/hs[0]*W(f(".1384"))/W(f(".139"))*han[1]/ha[0]*h2n[1]*h3n[1] \
    *(I2[1]+sum(rank_cap(an,k)*hk(an,k) for k in range(4,13)))/ratio_den
ck(broad<f(".799905"),"broad deep rough fraction")
ck(narrow<f(".140376"),"narrow deep rough fraction")
ck(broad+narrow<f(".942"),"combined single reserve")
ck(7*ab>f(".689") and 13*an>f(".689"),"rank limits")
ck(4*(f(".5")-f(".321"))>1-f(".321"),"rank five j>=1")
print("Certified B5 upper:",float(b5))
print("Exact rational upper fractions:",float(broad),float(narrow),float(broad+narrow))
