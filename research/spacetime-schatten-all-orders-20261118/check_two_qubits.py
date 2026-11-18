"""Independent matrix-unit reconstruction in a 4-dimensional system.
Python standard library only. Runs even with -O.
"""
from fractions import Fraction as F
from itertools import product
def needed(t,name):
    if not t: raise ArithmeticError(str(name))
def zeros(n):return [[F(0) for _ in range(n)] for _ in range(n)]
def mul(A,B):return [[sum(a*b for a,b in zip(r,c)) for c in zip(*B)] for r in A]
def tr(A):return sum(A[i][i] for i in range(len(A)))
def tp(A):return list(zip(*A))
def lift(i,j):
    A=zeros(4)
    for e in (0,1):A[2*i+e][2*j+e]=1
    return A
U=zeros(4);U[0][0]=U[3][2]=1; U[1][1],U[1][3]=F(7,25),F(24,25);U[2][1],U[2][3]=-F(24,25),F(7,25)
needed(mul(tp(U),U)==[[int(i==j) for j in range(4)] for i in range(4)],'unitary')
for x in (F(0),F(1),F(1,8)):
    rho=zeros(4);rho[0][0]=1-x
    for i,j in product((0,1), repeat=2):
        rho[2*i+1][2*j+1]=x*(4,3)[i]*(4,3)[j]/25
    # Each test state is a convex combination of normalized product projectors.
    needed(tr(rho)==1,'trace')
    expected=[[[112,84],[384,288]],[[288,216],[-84,-63]]]
    # Row and column spacetime indices are ordered 2*i+j = 2*initial+final.
    T=zeros(4)
    for a,b,c,d in product((0,1),repeat=4):
        val=tr(mul(mul(mul(mul(rho,lift(a,b)),tp(U)),lift(c,d)),U))
        T[2*b+d][2*a+c]=val
        needed(val==((1-x)*int((a,b,c,d)==(0,0,0,0))
                     +x*int(c==d)*F(expected[c][b][a],625)),('correlation',x,a,b,c,d))
    needed(tr(T)==1,'T trace')
    R=[[sum(T[2*i+j][2*k+j] for j in (0,1)) for k in (0,1)] for i in (0,1)]
    S=[[sum(T[2*j+i][2*j+k] for j in (0,1)) for k in (0,1)] for i in (0,1)]
    needed(R[0][0]==S[0][0]==1-x*F(9,25) and R[0][1]==12*x/25 and S[1][0]==0,'marginals')
    frob=sum(abs(v)**2 for row in T for v in row)
    needed(frob==1-F(1026,625)*x*(1-x),'squared Frobenius')
    if x==F(1,8):
        needed(frob<(1-F(18,25)*x)**2,'strict example at p=2')
    print('Exact unitary, tensor-order correlators and marginals for x =',x)
needed(F(63,625)-F(7,512)>F(1,12),'uniform margin constant')
print('Explicit p=2 witness and the uniform numerical constant certified.')
