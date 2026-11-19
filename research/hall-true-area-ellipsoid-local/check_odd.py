"""Exact beta-moment sign/normalization checks in odd ambient dimensions."""
from fractions import Fraction as R
from math import prod,comb
def times(a,b):
    out=[R(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
def expect(a,m):
    # c^2 ~ Beta(m,m); beta ratio simplifies as m is integral.
    return sum(x*prod(R(m+j,m+R(k,2)+j) for j in range(m)) for k,x in enumerate(a))
def main():
    for d in range(3,24,2):
        m=(d-1)//2
        f=[R(0)]*(d-2)
        for i in range(m):f[2*i]=R((-1)**i*comb(m-1,i))
        norm=2*sum(x/R(i+1) for i,x in enumerate(f)); f=[x/norm for x in f]
        F=[R(1,2)]+[x/R(i+1) for i,x in enumerate(f)]
        P2=[1,0,-R(4*d,d-1),0,R(4*d,d-1)]
        if expect(P2,m)!=0: raise ArithmeticError(('P2 centering',d))
        A=R(3,(d-1)*(d+2))
        metric=-A*(d-2)*expect([0]+f,m)
        cross=A*expect(times([0,1,0,-1],f),m)
        pairs=R(9,2*d*(d+2))*expect(times(P2,F),m)
        H=metric+cross+pairs
        if not(pairs<0<cross<-metric and H<0):raise ArithmeticError((d,metric,cross,pairs))
        if d==3 and (metric,cross,pairs,H)!=(R(-1,10),R(1,25),R(-1,350),R(-11,175)):
            raise ArithmeticError(('dimension three',H))
        print('d=',d,'coefficient / tr(H^2) =',H)
    print('PASS: eleven odd dimensions using exact beta moments.')
if __name__=='__main__': main()
