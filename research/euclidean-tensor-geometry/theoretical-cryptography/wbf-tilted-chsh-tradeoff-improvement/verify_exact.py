#!/usr/bin/env python3
"""Exact rational Pauli expansion plus independent radical probabilities."""
from fractions import Fraction as F
from itertools import product

I = [[1, 0], [0, 1]]
X = [[0, 1], [1, 0]]
Z = [[1, 0], [0, -1]]
J = [[0, 1], [-1, 0]]  # ZX, so J tensor J = -Y tensor Y.

def add(*L):
    return [[sum(col) for col in zip(*row)] for row in zip(*L)]

def scale(t, A):
    return [[t * a for a in row] for row in A]

def mul(A, B):
    return [[sum(a * b for a, b in zip(row, col)) for col in zip(*B)]
            for row in A]

def kron(A, B):
    return [[a * b for a in row for b in sub]
            for row in A for sub in B]

II, IZ, IX, ZI, ZZ, ZX, XX, JJ = [kron(A, B) for A, B in
    [(I,I),(I,Z),(I,X),(Z,I),(Z,Z),(Z,X),(X,X),(J,J)]]

def circle(a):
    return ((1-a*a)/(1+a*a), 2*a/(1+a*a))

settings_a = [circle(F(i,5)) for i in range(13)]
settings_b = [circle(F(i,12)) for i in range(13)]
for (g,h),(c,d),t in product(settings_a,settings_b,[F(0), F(3,2), F(39,20)]):
    M = add(scale(t,ZI),scale(2*c,ZZ),scale(2*d*g,ZX),scale(2*d*h,XX))
    residual = add(scale(4*t*c,IZ),scale(4*t*d*g,IX),scale(8*c*d*h,JJ))
    assert mul(M,M) == add(scale(t*t+4,II),residual)
    u,k = c*c,h*h
    f = t*t*(c*c+d*d*g*g)+4*c*c*d*d*h*h
    assert mul(residual,residual) == scale(16*f,II)
    assert f == t*t+k*(1-u)*(4*u-t*t)
    ustar,G = (4+t*t)/8,(4-t*t)**2/16
    assert t*t+G-f == (1-k)*G+4*k*(u-ustar)**2
print("exact Bell-square, anticommutation and deficit: 507 rational profiles PASS")

Mstar = add(scale(48,ZI),scale(50,ZZ),scale(14,XX))
V = [[7,0,0,1], [1,0,0,-7], [0,7,1,0], [0,1,-7,0]]
# Independent exact diagonalization, including the odd parity signs.
assert [mul(Mstar,[[z] for z in v]) for v in V] == [
    [[700],[0],[0],[100]],
    [[0],[0],[0],[0]],
    [[0],[0],[0],[0]],
    [[0],[-100],[700],[0]],
]
assert mul(V,list(map(list,zip(*V)))) == scale(50,II)
print("exact ideal spectrum: 100,0,0,-100 before division by sqrt(674)")

# Radical arithmetic represents a+b/sqrt(674), not floating point.
class R:
    def __init__(self,a=0,b=0): self.a,self.b = F(a),F(b)
    def __add__(self,v):
        if not isinstance(v,R): v=R(v)
        return R(self.a+v.a,self.b+v.b)
    __radd__ = __add__
    def __neg__(self): return R(-self.a,-self.b)
    def __sub__(self,v): return self+(-v)
    def __mul__(self,v):
        if not isinstance(v,R): v=R(v)
        return R(self.a*v.a+self.b*v.b/674,self.a*v.b+self.b*v.a)
    __rmul__=__mul__
    def __eq__(self,v):
        if not isinstance(v,R): v=R(v)
        return self.a==v.a and self.b==v.b
    def ispos(self):
        if self.a>=0 and self.b>=0: return self.a>0 or self.b>0
        if self.a<=0 and self.b<=0: return False
        return (self.a*self.a*674>self.b*self.b) if self.a>0 else (
              self.b*self.b>self.a*self.a*674)

psi=[7,0,0,1]
def outcome(x,y,a,b):
    Ea=scale(F(1,2),add(I,scale(a,[Z,X][x])))
    Bb=add(scale(R(0,25),Z),scale(R(0,7*(-1)**y),X))
    Eb=scale(F(1,2),add(I,scale(b,Bb)))
    P=kron(Ea,Eb)
    return sum(P[i][j]*F(psi[i]*psi[j],50) for i,j in product(range(4),repeat=2))

beta=R()
N=0
for x,y in product([0,1],repeat=2):
    diag=[]
    for a,b in product([1,-1],repeat=2):
        prob=outcome(x,y,a,b)
        assert prob.ispos()
        l=R(4*(-1)**(x*y)*a*b,96*int(x==0)*a)
        beta+=l*prob*F(1,4)
        diag.append(prob)
        N+=1
    assert sum(diag)==1
    if x==1: assert diag[0]+diag[1]==F(1,2)
    if y==0:
        collision=sum(p*p for p in diag)
        expected=F(1201,1250)*F(1299,1348) if x==0 else (
             1+F(576,674)+F(2401,674*625))/4
        assert collision==expected
assert beta==R(0,100)
pstar=outcome(0,0,1,1)
assert pstar==R(F(49,100),F(49,4))
assert (pstar-R(F(24,25))).ispos()
assert (R(4,96)-beta).ispos()  # an actually attainable accepted type
print(f"exact ideal probabilities: {N} positive; score, both collisions, n=256 accepted type PASS")

t2=F(2304,674)
assert (4-t2)**2/16>F(1,64)
assert F(625,674)>F(3,4)**2 and F(49,674)>F(1,4)**2
assert F(9)<F(10000,674)<F(16) and (4+t2)**2/16<4
assert 3+8+32==43 and 6**2 > F(1+86,3)
assert F(1,2)+F(22,1024)<F(17,32) and 17**10<2**41
assert F(24,25)-F(22,1024)>F(15,16)
assert F(1,8)*F(7,8)>F(1,16) and F(3,8)**2>F(1,8)
gamma,tau=F(1,2**8),F(1,2**40)
assert 1-F(3,2)*gamma>F(1,2)
assert (gamma*tau)**2 * 2**109/1152 > 4
assert 32*16*8*2==8192
print("exact robustness, entropy and Pinsker constants: PASS")
