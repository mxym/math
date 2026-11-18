"""Exact rational stress tests of the independent two-projection reduction, stdlib only."""
from fractions import Fraction as F
from math import gcd

def require(value, msg):
    if not value:
        raise ArithmeticError(msg)

def grid():
    n=end=eq=0
    uset={F(i,j) for j in range(1,6) for i in range(j+1,14)}
    xset={F(i,j) for j in range(2,48) for i in range(1,j) if gcd(i,j)==1}
    for q in sorted(uset):
        # Homogeneity: sqrt(l)=1, sqrt(u)=q.
        l=F(1); u=q*q; d=u-l; b=q-1; K=d+2*b
        for x in [F(0),F(1)]:
            c1=l+d*x; c2=l+d*(1-x)
            w1=l+2*b*x; w2=l+2*b*(1-x)
            require(c1>=w1 and c2>=w2,'one-dimensional projection limit')
            end+=1
        for x in sorted(xset):
            y=1-x; c1=l+d*x; c2=l+d*y
            w1=l+2*b*x; w2=l+2*b*y
            # I_+ and I_- intersect exactly if 2|C12| <= radius_+ + radius_-.
            rplus2=(c1+w1)*(c2-w2)
            rminus2=(c1-w1)*(c2+w2)
            target2=4*d*d*x*y
            need=target2-rplus2-rminus2
            cmp=4*rplus2*rminus2-need*need
            require(need<=0 or cmp>=0,'intervals have empty intersection')
            require(need>=0 and cmp==0 if x==F(1,2) else need<0 or cmp>0,
                    'contact set mismatch')
            fac=b*b*x*y
            require(rplus2==fac*(K+2*l/x) and rminus2==fac*(K+2*l/y),
                    'radius normalization')
            n+=1;eq+=x==F(1,2)
    print('Exact 2x2 interval comparisons:',n,'; central equalities:',eq,'; endpoints:',end)

def crossings():
    # Sign test: for rational s, square only when s-(m-2)e>=0; thus no extraneous root.
    # Independent expected sign: s_*'s test 2(r+1)s <=r+2, equivalent to
    # (2s-1)*sqrt(m) <= 2(1-s). Negative left is dealt with first.
    n=ties=0
    for m in range(2,76):
        vals={F(i,j) for j in range(1,47) for i in range(j+1)}
        for s in vals:
            e=(1-s)/m;a=s-(m-2)*e
            accepted=a<=0 or a*a<=4*e*(e+s)
            t=2*s-1
            expected=t<=0 or m*t*t<=4*(1-s)*(1-s)
            require(accepted==expected,'crossing quadrant')
            eq=a>=0 and a*a==4*e*(e+s)
            require(eq==(t>=0 and m*t*t==4*(1-s)*(1-s)),'crossing equality')
            ties+=eq;n+=1
    print('Exact crossing signs:',n,'; rational ties:',ties)

if __name__=='__main__':
    grid();crossings()
