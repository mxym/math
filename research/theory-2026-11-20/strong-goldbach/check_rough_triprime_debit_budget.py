"""Exact normalization ratios and strict dispersion rails for the rough debit."""
from fractions import Fraction as F

def f(s): return F(str(s))
def ck(test, reason):
    if not test:
        raise RuntimeError(reason)

def ln_ratio(a,b):
    a,b=f(a),f(b)
    t=(b-a)/(b+a)
    lo=2*sum((t**(2*k+1)/F(2*k+1) for k in range(12)), F(0))
    hi=lo+2*t**25/(25*(1-t*t))
    return lo,hi

h2=ln_ratio(".164",".16524")
h3=ln_ratio(".16525",".167")
h2n=ln_ratio(".16512",".16524")
h3n=ln_ratio(".16525",".16545")
I2=ln_ratio(".679",".689")
hE=ln_ratio(".311",".321")
hQ=ln_ratio(".297",".298")
l2=ln_ratio("1","2")
d=f(".017")
B5_hi=hE[1]*l2[1]**3/(24*f(".138"))
den_lo=40*d*hQ[0]*hE[0]**2*(1-hE[1])
rough=h2[1]*h3[1]*(I2[1]+3*B5_hi)/den_lo
narrow=3*f("2.1")*h2n[1]*h3n[1]*(I2[1]+3*B5_hi)/den_lo
ck(rough<f(".866"),"broad rough added debit")
ck(narrow<f(".061"),"narrow rough prior debit")
ck(rough+narrow<f(".927"),"one total budget")
e0,e1,q1,q2lo,q2hi,q3,theta=map(f,(".311",".321",".30424",".16525",".201",".069",".21875"))
rails=(q1-e0,2*e1+q2hi+2*q3, theta+e1+q1+5*q2hi+2*q3,
       2*theta*(e1+q3-q2lo)+e1+q1+5*q2hi+2*q3)
ck(rails==tuple(map(f,("-.00676",".981","1.98699","1.866568125"))),"strict four dispersion rails")
ck(5*f(".138")>1-e0,"at most four cofactor primes")
ck(1-e0-3*f(".138")<f(".276"),"individual rank-five length")
ck(f("2")/3+(3*f(".0686")+2*f(".4958"))/f(".8614")<f("2.1"),"old adjusted coefficient")
print("Exact rational upper fractions:", float(rough),float(narrow),float(rough+narrow))
