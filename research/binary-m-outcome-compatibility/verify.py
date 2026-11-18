#!/usr/bin/env python3
"""Exact checks of the scalar SOS, the sharp crossing, and singular complex examples.
The dimension-independent matrix reductions are in PROOF.md. No numerical SDP.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product

# Sparse integer polynomials in independent indeterminates. Canonical monomials
# are sorted tuples of variable names, including () for constants.
class P(dict):
    def __init__(self, z=0):
        if isinstance(z, int): z = {():z}
        if isinstance(z, str): z = {(z,):1}
        super().__init__((k,v) for k,v in z.items() if v)
    def __add__(self,q):
        t=defaultdict(int,self)
        for k,v in P(q).items(): t[k]+=v
        return P(t)
    __radd__=__add__
    def __neg__(self): return P({k:-v for k,v in self.items()})
    def __sub__(self,q): return self+(-P(q))
    def __rsub__(self,q): return (-self)+q
    def __mul__(self,q):
        t=defaultdict(int)
        for k,v in self.items():
            for i,j in P(q).items(): t[tuple(sorted(k+i))]+=v*j
        return P(t)
    __rmul__=__mul__
    def __pow__(self,n):
        z=P(1)
        for _ in range(n): z=z*self
        return z

def ck(condition, name):
    if not condition: raise ArithmeticError(name)

a,c,x,y,h,r=map(P,('a','c','x','y','h','r'))
e=a*a; s=c*c-e; b=a*(c-a)
# Twice the variational trace lower bound in one eigenvector, multiplied
# by h/r_i (r_i>0). Each square below has nonnegative coefficient for
# 0<=x,y<=1, h>0; no numerical sample or polynomial sign oracle is used.
objective=(e+s*x)*h*h+e+s*y-2*h*(e+b*(x+y))
sos=((1-x)*(1-y)*(a*(h-1))**2 + x*(1-y)*(c*h-a)**2
     +(1-x)*y*(a*h-c)**2+x*y*(c*c*(h-1)**2+2*h*(c-a)**2))
ck(objective==sos,'common-baseline scalar sum of squares')
# At the claimed fixed point take D=2r(r+1)>0, m=r^2 and use
# e=1/D, e+s=(r+1)^2/D, sqrt(e(e+s))=(r+1)/D.
D=2*r*(r+1); m=r*r; s_num=r*(r+2); c_num=(r+1)**2
ck(D-s_num==m,'e=(1-s)/m')
ck(c_num==1+s_num,'e+s')
ck((m-2)+2*(r+1)==s_num,'f(s)=s')
ck(D==2*r*(r+1) and s_num==r*(r+1)+r,'s=1/2+1/[2(1+r)]')
# General sharp-witness normalization: (m-1)a^2+c^2 represents total
# identity mass before a simultaneous positive rescaling.
ck(((m-1)*a*a+c*c)-(c-a)**2==(m-2)*a*a+2*a*c,'f=1-(c-a)^2')
print('PASS: four-corner scalar sum of squares and symbolic crossing for all m=r^2 (r=sqrt(m)).')

# A family of genuinely complex POVMs on C^3. Let v_j=(1,i^j,i^(2j))/2
# be the columns of the first three rows of the unitary 4-point Fourier
# matrix. Take B_j=l v_j v_j^*+(1-l)D_j, D_0,D_1,D_2 the coordinate
# projectors, D_3=0. Sum B_j=I. For 0<l<=1 the effects couple supp T
# to ker T when T=diag(p,-q,0), which therefore is not an invariant block.
# For C=a^2 I+s B_j, sqrt(C) T sqrt(C) has one positive and one negative
# eigenvalue and a zero: its trace is p C11-q C22 and the product of its
# nonzero eigenvalues is -p q det C[1:2,1:2] (AB/BA nonzero spectrum).
# We compare the squares of both nonnegative sides of PROOF.md (4).
tests=0; equal=0
for l,p,q,(aa,cc),j in product((Q(1,9),Q(2,5),Q(7,8),Q(1)),(1,2,5),(1,3,7),
                                ((1,2),(1,3),(2,5),(3,4)),range(4)):
    u=l/4+(1-l)*(j==0); v=l/4+(1-l)*(j==1); abs_z2=(l/4)**2
    ee=aa*aa; ss=cc*cc-ee; bb=aa*(cc-aa)
    U=ee+ss*u; V=ee+ss*v; det=U*V-ss*ss*abs_z2
    ck(det>0,'positive compressed C')
    norm2=(p*U-q*V)**2+4*p*q*det
    rhs=ee*(p+q)+2*bb*(p*u+q*v)
    ck(rhs>=0 and norm2>=rhs**2,'singular Hermitian test')
    tests+=1; equal+=int(norm2==rhs**2)
print(f'PASS: {tests} exact flagged single-effect comparisons with a singular witness and non-invariant support ({equal} equalities).')
