from fractions import Fraction as F
from math import isqrt, factorial as fac
def ce(n,d):return (n+d-1)//d
def require(ok,why):
    if not ok: raise ArithmeticError(why)
P=1000;A=105;B=150;sc=10**14
def fo(n):
    z=abs(P-2*n)
    return 2*z**3*P**2-z**5
f=list(map(fo,range(P+1)))
def lo(i,j):
    return 0 if 2*i<=P<=2*j else min(f[i],f[j])
def hi(i,j):return max(f[i],f[j])
def rank4(A,B):
    total=0
    cap=[]
    for i in range(A,B):
        m=0
        for j in range(i,(P-i)//3+1):
            fij=lo(i+j,i+j+2)
            hij=hi(i,i+1)+hi(j,j+1)
            for k in range(j,(P-i-j)//2+1):
                up=P-i-j-k
                w=max(up-3,k)
                u=hij+hi(k,k+1)+hi(w,up)-P**5-fij-lo(i+k,i+k+2)-lo(j+k,j+k+2)
                if u<=0:continue
                total+=ce(u*sc,P**4*i*j*k*w)
                m=max(m,u)
        cap.append(F(m,P**5))
    return F(total,sc),cap
n4,c4=rank4(A,B)
print("binned rank4 ordinary upper and cap",float(n4),float(max(c4)),flush=True)
def sqrthi(n,d=1):
    return F(isqrt(n*10**12//d)+1,10**6)
def n3_bound(a):
    w0=F('.754');w1=1-2*a
    return F(56,6)*(w1-w0)**3
def n6_bound(a):
    # b4 max via u_1...u_4≥a; u5u6≥1/36 on .1-rough
    return (96*72*sqrthi(1,2)/(a) +3840*sqrthi(12)) * (1-6*a)**5/(720*120)
a,b=F(A,P), F(B,P)
m={3:n3_bound(a),4:n4,5:F(1920)*((1-5*a)**4-(1-5*b)**4)/(120*24),6:n6_bound(a),8:F('1.2')*(1-8*a)**7/(fac(8)*fac(7)*a**8)}
cp_3=F('.055'); cp_6=F('.915'); cp_8=F('1.2')
# Exact differentiated-box pointwise constants.
cap6=192*sqrthi(8)*F(4,6)**3/4**4+3840*sqrthi(12)/6**6
cap8=768*sqrthi(8)*F(4,8)**3/4**4+7680*sqrthi(12)*F(6,8)**5/6**6
require(cap6<cp_6 and cap8<cp_8 and max(c4)<F('.218'),"pointwise signs and caps")
w=F('.754')
require(2*w*w-F('1.8')*w+F('.82')<F('.6') and
        16*w*((1-w)/2)**2*F('.3')<cp_3,"true negative triprime guard")

print("m3..8",[(i,float(v)) for i,v in m.items()],flush=True)
# Uniform upper for A_lin(s)=s e^-gamma F_lin(s) on 3≤s≤4.
R=1000
tab=[0]*3001
for j in range(3*R,4*R):
    v=F(j+1,R)-2
    u=(v-1)/(v+1)
    L=2*sum(u**(2*t+1)/(2*t+1) for t in range(12))+2*u**25/(25*(1-u*u))
    x=2*L/(j-R)
    tab.append(tab[-1]+ce(x.numerator*sc,x.denominator))
u={r:F(0) for r in m}
for i in range(A,B):
    t,th=F(i,P),F(i+1,P)
    # Any element on this band has actual least prime ≥ t and < th.
    d=F('.499')-th;s=d/t
    if s>4:raise ArithmeticError("ratio")
    n=max(3*R,ce(s.numerator*R,s.denominator))
    z= (2+F(tab[n],sc))/d
    facw=z*(th-t)/t
    vals={3:cp_3,4:c4[i-A],5:1920*th*((1-th)/4)**4,6:cp_6,8:cp_8}
    for r in vals:u[r]+=vals[r]*facw
print("U by rank",[(i,float(v)) for i,v in u.items()])
cross=sum(min(m[r]*u[s],m[s]*u[r]) for r in m for s in m)
loss=4*sum(m.values())+cross
print("sum,mix,total,remaining",float(sum(m.values())),float(cross),float(loss),float(F('.515')-loss))
require(sum(m.values())<F('.077983212') and cross<F('.102732633')
        and loss<F('.414666'),"band ordinary, paired and complete bound")
# These are the previously certified same-score rank-four/five/six
# negative mass bounds on .150-rough and the genuine s>=3 receiver.
m_hi=sum(map(F,('.004093559','.002604167','.000030484')))
U_hi=F('.915')*F(40,9)
both=loss+4*m_hi+2*(u[6]*m_hi+U_hi*m[8])+U_hi*m_hi
require(both<F('.493039'),"entire all-opponent negative union above .105")
require(F('.575485')-both>F('.082'),"complete negative union and positive block")
print("higher rough source, full negative-union cost and remaining credit:",
      float(m_hi),float(both),float(F('.575485')-both))
