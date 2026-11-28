"""Finite exact checks of the common affine slice; no user-supplied inputs."""
from fractions import Fraction as Q
from itertools import product
from math import prod

def factors_small(x):
    assert x == int(x) and 1 <= x <= 10**13
    x = int(x)
    d = 2
    out = set()
    while d*d <= x:
        while x % d == 0:
            out.add(d)
            x //= d
        d += 1
    if x > 1:
        out.add(x)
    return out

# Tree xy=A, yz=B: z=B*x/A. The determinant eliminating y
# from x*y-A and z*y-B gives A*z-B*x (up to fixed sign).
count = 0
for A, B in product((2, 3, 6, 15), (5, 7, 14, 35)):
    for i,j,h in product(range(1,5), repeat=3):
        vals = set()
        for t in (Q(1,2), Q(1), Q(3), Q(7), Q(11,3)):
            x,y,z = t, A/t, B*t/A
            assert x*y == A and y*z == B
            assert A*z-B*x == 0
            vals.add(x**i * y**j * z**h)
        assert (len(vals)==1) == (i+h==j)
        if i+h==j:
            val, = vals
            assert val == A**i * B**h
            assert factors_small(val) <= factors_small(A*B)
        count += 1

assert (Q(3)*5*7, Q(3)*5**2*7) == (105,525)
assert [Q(1),Q(15),Q(7,3)] == [Q(1),15/Q(1),35*Q(1)/15]

# (t-j)y=b has one missing affine fibre; add a spurious y^m multiple
# to the eliminant only (not to an input equation) and strip it.
strips=0
for j,b,m in product(range(1,6), range(1,7), range(1,5)):
    for t in range(1,9):
        coeff=[0]*m+[-b,t-j]  # ascending in y, fixed formal degree
        while coeff[0]==0: coeff.pop(0)
        assert coeff==[-b,t-j]
        if t==j:
            assert coeff[0]!=0 and coeff[1]==0
        else:
            assert coeff[1]*Q(b,t-j)+coeff[0]==0
        strips+=1
    a=next(t for t in (1,2,3) if t!=j)
    assert (a-j)*Q(b,a-j)==b

# A length-dependent high-height coefficient can itself be a constant
# product; its representation size, not an integer difficulty claim, is tested.
for L in range(5,81):
    c=2**(L-1)+3
    assert c.bit_length()==L
    for t in [Q(2), Q(7,3), Q(11,5)]:
        assert t*(Q(c)/t)==c

print("PASS slice/formal-fibre checks: %d weighted trees; %d bad-slice/zero-stripping evaluations; 76 large-height lengths." % (count,strips))
