"""Exact preliminaries used by phase4.cpp. No complex floating arithmetic."""
from fractions import Fraction as F
from math import isqrt, lcm
from orbits4 import canonical4

def must(b,msg):
    if not b: raise ArithmeticError(msg)
def mul(x,y):
    return x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def inv(x):
    return (x[0],-x[1])
def pw(x,j):
    y=(F(1),F(0))
    for _ in range(abs(j)): y=mul(y,x if j>=0 else inv(x))
    return y
def phase(e,f,u):
    return mul(mul(pw((F(3,5),F(4,5)),e),pw((F(5,13),F(12,13)),f)),pw((F(0),F(1)),u))

def scope():
    B=16*lcm(*range(1,17))
    out={(int(phase(e,f,u)[0]*B),int(phase(e,f,u)[1]*B)) for e in (-1,0,1) for f in (-1,0,1) for u in range(4)}
    must(len(out)==36 and all(a*a+b*b==B*B for a,b in out),'alphabet injection')
    quadrant={(x,y) for x,y in out if x>=0 and y>=0}
    for x in range(B+1):
        r=B*B-x*x;y=isqrt(r)
        if y*y==r:must((x,y) in quadrant,'missing point')
    alphabet={phase(e,f,u) for e in (-1,0,1) for f in (-1,0,1) for u in range(4)}
    for e in range(-2,3):
        for f in range(-2,3):
            for u in range(4):
                must((phase(e,f,u) in alphabet)==(abs(e)<=1 and abs(f)<=1),'width test')
    expected=[
        [0,1,2,4,8],[0,1,2,3,4,8],[0,1,2,4,8,15],
        [0,1,2,3,4,5,8],[0,1,2,3,4,8,12],
        [0,1,2,3,4,5,6,8],[0,1,2,3,4,5,8,9],[0,1,2,3,4,5,8,10]]
    must([sorted(S) for h in range(5,9) for S in canonical4(h)]==expected,'orbit list')
    for h in range(5,9):
        T={F(h*t,2*j) for j in range(h,17) for t in range(j%2,j+1,2) if h*t<=2*j}
        must({(a,b) for a in T for b in T if a*a+b*b==1}=={(F(0),F(1)),(F(1),F(0))},'unique pair')
    print('circle, width, eight affine support orbits and unique-pair tests pass; denominator',B)
if __name__=='__main__':scope()
