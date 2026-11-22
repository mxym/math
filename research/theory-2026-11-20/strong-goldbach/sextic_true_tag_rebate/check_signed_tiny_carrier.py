from fractions import Fraction as Q
from math import comb, factorial as fac

def req(ok,msg):
    if not ok:
        raise ArithmeticError(msg)
def logup(x):
    a=(x-1)/(x+1)
    return 2*sum(a**(2*j+1)/(2*j+1) for j in range(12)) + 2*a**25/(25*(1-a*a))

g0,g1=Q(26,1000),Q(48,1000)
V=Q(62,100); n=21
req(logup(g1/g0)<V and (n-1)*g1<1<=n*g1,"actual geometric bank boundary")
ks=[Q(0)]+[(g1**i-g0**i)/i for i in range(1,6)]
mom=[Q(1)]
for i in range(1,6):
    mom.append(sum(comb(i-1,j-1)*ks[j]*mom[i-j] for j in range(1,i+1)))
T=78*mom[1]-576*mom[2]+1504*mom[3]-1680*mom[4]+672*mom[5]
def tail(v,power=0,j=n):
    # successive ratio <= v/(j+1)*((j+1)/j)^power
    R=v/(j+1)*Q(j+1,j)**power
    req(R<1,"positive tail ratio")
    return j**power*v**j/fac(j)/(1-R)
E1=sum(c*g1**j*tail(V,j) for j,c in enumerate([1,78,576,1504,1680,672]))
E2=43*tail(2*V)
E3=tail(2*V)/(g0*V)
req(E1+E2+E3<Q(1,10000),"true ordinary geometric errors")
req(T-E1-E2-E3>Q(1098,1000),"signed raw geometric bank")
narrow=Q(167,1000)
m_delta_lo=Q(141,1000)
req(2*narrow-m_delta_lo<Q(194,1000),"absolute marked source charge")
req(T-E1-E2-E3-Q(194,1000)>Q(90,100),"negative source reserve")
ell=78-1152*Q(2,1000)
req(ell*Q(90,100)>68 and ell**2>5700,"positive sector constants")
bb=Q(3,10000)
alpha=Q(24,1000)+5*bb
req(alpha<g0 and Q(875,1000)+Q(3,2)*g1+2*alpha<1,"real one-sided C.1")
req(Q(875,1000)+Q(7,2)*alpha<1,"real double marked C.1")
print("ordinary geometric bank signed surplus:",float(T),"tail bounds",float(E1+E2+E3))
print("two signed constants:",float(ell*Q(90,100)),float(ell**2))
