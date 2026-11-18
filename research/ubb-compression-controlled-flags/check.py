"""Exact finite illustrations; not proofs of the topology or the general theorem."""
from fractions import Fraction as F
from itertools import permutations
from math import factorial

def ck(x):
    if not x:
        raise ArithmeticError("certificate failed")

def mat_id(n):
    return [[F(i==j) for j in range(n)] for i in range(n)]

def trans(x):
    return [list(row) for row in zip(*x)]

def mul(x,y):
    return [[sum(a*b for a,b in zip(row,col)) for col in trans(y)] for row in x]

def norm2(x):
    return sum(a*a for row in x for a in row)

# Two rational orthogonals of order 7 with the same three complement blocks.
d=6; n=7
X=mat_id(n)
X[5][5]=X[6][6]=F(3,5); X[5][6]=F(4,5);X[6][5]=-F(4,5)
Y=[r[:] for r in X]
Y[0],Y[1]=Y[1],Y[0]
ck(mul(trans(X),X)==mat_id(n)==mul(trans(Y),Y))
A=[row[:d] for row in X[:d]];B=[row[:d] for row in Y[:d]]
ck(mul(A,trans(A))==mul(B,trans(B)))
ck(mul(trans(A),A)==mul(trans(B),B))
ck(norm2(A)==F(134,25)>=d-(n-d))
# Exact universal bound specialized to d=6 (one must square amplitude for fidelity).
ck(F(d-(n-d),d)==F(5,6)); ck(F(5,6)**2==F(25,36))

# The limiting gate-flag Jacobian on each complex tangent line acts by
# multiplication by i(c_i-c_j)(h_j-h_i), with positive real determinant.
for d in range(2,8):
    count=0
    for h in permutations(range(d)):
        real_det=1
        for i in range(d):
            for j in range(i+1,d):
                real_det*=((i-j)*(h[j]-h[i]))**2
        ck(real_det>0);count+=1
    ck(count==factorial(d))
print("PASS: rational block marginals, norm, amplitude/fidelity convention and all limiting flag Jacobians through d=7.")
