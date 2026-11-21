"""Exact rational rails, Fourier envelope, and budget for the smooth full-height debit."""
from fractions import Fraction as F
from math import factorial

def f(x): return F(str(x))
def require(v, label):
    if not v: raise RuntimeError(label)

def ln_bounds(a,b):
    a,b=f(a),f(b)
    t=(b-a)/(b+a)
    base=2*sum((t**(2*k+1)/(2*k+1) for k in range(12)),F(0))
    return base,base+2*t**25/(25*(1-t*t))

def i_upper(s):
    return sum(((-1)**k*s**(2*k+1)/((2**(2*k))*(2*k+1)*factorial(2*k+1))
                for k in range(7)),F(0))
def exp_upper(t):
    require(0<=t<=5,"Taylor input")
    base=sum((t**j/factorial(j) for j in range(31)),F(0))
    return base+t**31/factorial(31)/(1-t/32)

for k in range(500):
    left,right=F(k,100),F(k+1,100)
    require(exp_upper(i_upper(right)) < 4+f("1.42")*left**2,"Fourier exp envelope on grid")
require(exp_upper(i_upper(F(5))) < f("1.42")*25,"Fourier exp envelope monotone tail")
beta=f(".310")
A=(F(22,7)/beta)**2
require(A<103 and (1+beta)*(12+2*103)<f("285.59"),"smooth unperturbed Fourier moment")
require(8/f(".679")<12 and 2*f("1.42")*f(".689")<2,"profile Fourier envelope")
e0,e1,th=f(".311"),f(".321"),F(7,32)
def rails(q1,q2lo,q2hi,q3):
    return (q1-e0,2*e1+q2hi+2*q3,th+e1+q1+5*q2hi+2*q3,
            2*th*(e1+q3-q2lo)+e1+q1+5*q2hi+2*q3)
require(rails(f(".310"),f(".138"),f(".189"),f(".069"))
        ==tuple(map(f,("-.001",".969","1.93275","1.82425"))),"broader high Q rails")
require(rails(f(".30424"),f(".16525"),f(".201"),f(".069"))
        ==tuple(map(f,("-.00676",".981","1.98699","1.866568125"))),"upper chart rails")
he=ln_bounds(".311",".321")
hq=ln_bounds(".297",".310")
h2=ln_bounds(".164",".16524");h3=ln_bounds(".16525",".167")
h2n=ln_bounds(".16512",".16524");h3n=ln_bounds(".16525",".16545")
hs=ln_bounds(".138",".139");hsn=ln_bounds(".1384",".1386")
ha=ln_bounds(".068",".069");han=ln_bounds(".0684",".0686")
W=lambda t:(1-t)*(1-2*t)**2
d=f(".017")
hcredit=he[0]*(1-he[1]+he[0]**2/2)
den=40*d*hq[0]*hcredit
base=f("286")*he[1]/den
broad=base*h2[1]*h3[1]*W(f(".138"))/W(f(".139"))
narrow=base*f("7.3")*h2n[1]*h3n[1]*(hsn[1]/hs[0])*(han[1]/ha[0])*W(f(".1384"))/W(f(".139"))
require(broad<f(".810"),"full broad increment")
require(narrow<f(".003"),"full narrow corrected")
require(broad+narrow<f(".813"),"single total new reserve")
print("500 strict exponential cells; exact new reserves",float(broad),float(narrow),float(broad+narrow))
