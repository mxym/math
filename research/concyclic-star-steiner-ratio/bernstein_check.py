"""Exact alternate polynomial positivity certificate for FINITE.md (5),(6).
Ascending power coefficients f(t). For f(A+(B-A)s)=sum a_j s^j,
degree-d Bernstein coefficient k is sum_{j<=k} a_j C(k,j)/C(d,j).
"""
from fractions import Fraction as F
from math import comb
from itertools import zip_longest
T=[0,1]
def add(*pol):return [sum(x) for x in zip_longest(*pol,fillvalue=0)]
def mult(p,q):return [sum((p[i]*q[k-i] for i in range(max(0,k-len(q)+1),min(k,len(p)-1)+1)),F(0)) for k in range(len(p)+len(q)-1)]
def scale(k,p):return [k*x for x in p]
def power(p,n):
    r=[1]
    for _ in range(n):r=mult(r,p)
    return r
def certificate(P,end,pieces,expected):
    d=len(P)-1; low=None
    for i in range(pieces):
        A=end*i/pieces; H=end/pieces
        a=[sum(P[m]*comb(m,j)*A**(m-j)*H**j for m in range(j,d+1)) for j in range(d+1)]
        for k in range(d+1):
            b=sum(a[j]*F(comb(k,j),comb(d,j)) for j in range(k+1))
            if b<=0:raise ValueError((P,i,k,b))
            low=b if low is None else min(low,b)
    if low!=expected:raise ValueError(('binding mismatch',low,expected))
    print('degree',d,'cells',pieces,'minimum positive Bernstein coefficient',low)
def main():
    L=F(31415,10000);u=F(83,200);q=F(4,5);V=[F(118,100),-F(11,10)]
    plus=[1,1];minus=[1,-1];T2=[0,0,1]
    P=add(mult(plus,add(scale(L/4,T2),[-F(108,1000)])),scale(L**3/96,power(minus,5)))
    K=add(scale(3,power(V,3)),scale(6*u,power(V,2)),scale(4*u*u,V),[2*u**3])
    Kpos=add(scale(5,mult(add(V,[2*u]),minus)),scale(-1,mult(plus,K)))
    tang=scale(2,add(V,[-F(675,1000)],scale(-1/(1+q*q),add(V,[-q]))))
    G=add(mult(plus,add(scale(L/4,T2),[-F(1723,10000)])),mult(power(minus,2),tang))
    certificate(P,F(1),8,F(107097934049,104857600000000))
    certificate(Kpos,F(47,100),1,F(697643389,4000000000))
    certificate(G,F(47,100),4,F(6102076921,5248000000000))
if __name__=='__main__':main()
