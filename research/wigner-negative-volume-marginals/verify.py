"""Exact finite-state and constant checks; the continuous bounds are in PROOF.md."""
from fractions import Fraction as F
from math import comb, factorial
from itertools import product
def check(x, label):
    if not x:
        raise ArithmeticError(label)
    print('PASS:',label)
m=64;r=F(1,2);a=r**m/factorial(m)
s=[F(comb(m,i),2**m) for i in range(m+1)]
v=[int(i==0) for i in range(m+1)];d=[x-a*j for x,j in zip(s,v)];z=[j-x for x,j in zip(s,v)]
def Lcoeff(j,k):
    return F((-1)**(j+k)*2**k*comb(j,k),factorial(k)) if k<=j else F(0)
check(all(sum(s[j]*Lcoeff(j,k) for j in range(m+1))==(F(1,factorial(m)) if k==m else 0) for k in range(m+1)), 'all 65 coefficients for radial binomial mixture')
q=[[(d[i]*d[j]-4*a*a*z[i]*z[j])/(1-a)**2 for j in range(m+1)] for i in range(m+1)]
check(all(x>0 for row in q for x in row),'4,225 exact positive probabilities')
check(sum(sum(row) for row in q)==1 and [sum(row) for row in q]==[x/(1-a) for x in d] and all(q[i][j]==q[j][i] for i,j in product(range(m+1),repeat=2)),'both marginals and trace')
check(q[0][0]!=d[0]**2/(1-a)**2,'nonproduct')
check(a<min(F(2)**(-m-2),F(1,16)) and 4*(1-a)**2>3,'negative-negative rectangle constants')
check(F(512,m**2)==F(1,8) and 32*a/r<F(1,8),'positive and mixed rectangle constants')
check(-F(1,2)+F(1,8)+F(1,8)==-F(1,4),'strict total normalized deficit bound')
