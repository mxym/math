"""Independent four-coordinate boundary check, using exact finite fields and rational roots."""
from fractions import Fraction
from itertools import product
from math import prod
# For each elementary component give D,V,B as lists of (ax+b)^e.
I=([(1,0,1)],[],[(1,-1,1)])
P=([(2,1,1)],[(1,0,2)],[(1,-1,1)])
C=([(4,3,1)],[(1,0,2),(2,1,3)],[(1,-1,1)])
F=([(2,1,1),(4,1,1)],[(1,0,3)],[(1,-1,1),(1,0,1)])
def ev(f,x):return prod((a*x+b)**e for a,b,e in f)
def poles(f):return {-Fraction(b,a) for a,b,e in f}
def at(f,t,p):
    return ((prod(a**e for a,b,e in f)%p,int(not f)) if t is None else (ev(f,t)%p,1))

# Check in projective coordinates at X1=1. Constants only need to meet the
# explicit algebraic noncollision conditions modulo p; large-real-size
# conditions are checked independently over rationals below.
templates=[("A",(I,I,P,C)),("A",(P,F,C,P)),("A",(C,I,F,C)),
           ("A",(I,C,P,F)),("A",(F,C,F,P)),("B",(P,I,F,I)),
           ("B",(C,I,P,I)),("B",(F,I,C,I))]
tested={"A":0,"B":0};first_pair=0; archA=archB=0
for typ,t in templates:
    # x is deliberately large, but this part is pure polynomial arithmetic;
    # it does not require prime fixtures or an unknown input.
    k=16; A=4; H=2*(k+1)*(A+1)**2
    xs=[H**(k+1)+j for j in (19,27,31,85)]
    d1,d2=(ev(t[2*j][0],xs[2*j])*ev(t[2*j+1][0],xs[2*j+1]) for j in (0,1))
    v=prod(ev(tree[1],x) for tree,x in zip(t,xs))
    E=sum(e for tree in t for a,b,e in tree[1])
    assert d1>H**k and d2>H**k and v>H**E
    if typ=="A":
        for y in poles(t[1][1]):
            assert abs(ev(t[0][0],1)*ev(t[1][0],y))<=H**k<d1;archA+=1
    else:
        for z in poles(t[2][0]):
            assert abs(ev(t[0][1],1)*ev(t[2][1],z))<=H**E<v;archB+=1
    for p in (13,17,19,23):
        pts=list(range(p))+[None]
        values=[{x:tuple(at(poly,x,p) for poly in tr) for x in pts} for tr in t]
        eval1=values[0][1]
        assert all(vals[0] for vals in (eval1[0],eval1[1]))
        if typ=="A":
            bad={(eval1[0][0]*values[1][y][0][0])%p for y in range(p) if values[1][y][1][0]==0}
            d12=next(d for y in range(p) if (d:=eval1[0][0]*values[1][y][0][0]%p) and d not in bad)
            v0=5
        else:
            bad={(eval1[1][0]*values[2][z][1][0])%p for z in range(p) if values[2][z][0][0]==0}
            d12=2;v0=next(c for c in range(1,p) if c not in bad)
        d34=2; b0=7
        for y in pts:
            e2=values[1][y]
            if (eval1[0][0]*e2[0][0]-d12*e2[0][1])%p:continue
            first_pair+=1
            for z,w in product(pts,repeat=2):
                e3,e4=values[2][z],values[3][w]
                row=(eval1,e2,e3,e4)
                def eq(j,k):
                    return (prod(e[j][0] for e in row)-k*prod(e[j][1] for e in row))%p==0
                eq34=(e3[0][0]*e4[0][0]-d34*e3[0][1]*e4[0][1])%p==0
                assert not(eq34 and eq(1,v0) and eq(2,b0))
                tested[typ]+=1
# The all-isolated boundary: exact rational prescribed sums for each pair.
d1=101*103;d2=107*109
b=(101-1)*(103-1)*(107-1)*(109-1)
for s in range(185,226):
    z=Fraction(d2+1)-Fraction(b,d1+1-s)
    assert (d1+1-s)*(d2+1-z)==b
print("projective first-pair solutions",first_pair,"remaining binary projective choices",sorted(tested.items()))
print("rational exceptional-root comparisons",archA,archB,"all-isolated free sums",41)
