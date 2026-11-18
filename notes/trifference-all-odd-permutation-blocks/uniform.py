from cert import fourier, sizes,pperm,need
from math import factorial, log2
from fractions import Fraction as F
def gap_ok(q,n,f):
    # -log2(F/b^n)/(2n)>1/350
    need(0<f<1,'valid failure probability')
    ratio=f/F(3*q-2,q*q)**n
    # No floating point enters the decision.
    return ratio.denominator**350>2**(2*n)*ratio.numerator**350
if __name__=='__main__':
    for q in range(4,20):
        n=q+2;s=q*factorial(n)//6
        b=fourier(q,n); f=F(b,s**3)
        need(gap_ok(q,n,f),'small q')
        rat=f/F(3*q-2,q*q)**n
        print(q,n,b,f,-log2(rat)/(2*n),flush=True)
    for q in range(20,256):
        need(gap_ok(q,q,pperm(q)),'permutations finite')
    need(17**12>2*16**12 and 258**30<2**256 and F(3*256-2,256)/F(11,4)>F(17,16),'analytic tail endpoints')
    print('PASS through q=255 and analytic tail endpoints')
