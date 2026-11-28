"""Fixed degree normalization and exact two-sided-center checks."""
from fractions import Fraction as Fr
from math import prod,gcd,isqrt

def data(tree,n,values):
    # tree entry: (parent index, degree at parent, degree at child, parentside
    # leading coefficient, childside leading coefficient). Edges in traversal order.
    alpha=[Fr(1)]; powers=[{}]
    for i,a,b,c,d in tree:
        h=Fr(a,b);alpha.append(alpha[i]*h)
        s={k:v*h for k,v in powers[i].items()}
        s[c]=s.get(c,0)+Fr(1,b);s[d]=s.get(d,0)-Fr(1,b)
        powers.append(s)
    return alpha,powers,prod(vals**e for vals,e in zip(values,n))

def floorcent(D,num,den):
    lo=0;hi=1
    def small(z):return den*z**D<=D**D*num
    while small(hi):hi*=2
    while hi-lo>1:
        m=(lo+hi)//2
        if small(m):lo=m
        else:hi=m
    return lo

def check(a,b):
    trees,n,vals=zip(a,b)
    K=sum(map(len,n));x,y=vals[0][0],vals[1][0]
    W=prod(d for t in trees for i,c,d,u,v in t)
    blocks=[];scale=Fr(1);N=1
    for tree,weights,values in (a,b):
        al,pows,block=data(tree,weights,values)
        N*=block
        bs=sum(v*w*W for v,w in zip(al,weights))
        assert bs.denominator==1;blocks.append(int(bs))
        for n0,s in zip(weights,pows):
            for u,v in s.items():
                exp=v*W*n0;assert exp.denominator==1;scale*=Fr(u)**int(exp)
    P=Fr(N**W)/scale;D=sum(blocks)
    S=blocks[0]*x+blocks[1]*y;J=floorcent(D,P.numerator,P.denominator)
    assert (Fr(J,D))**D<=P<(Fr(J+1,D))**D
    return N,W,blocks,scale,S,J

def prime(n):return n>=2 and all(n%p for p in range(2,isqrt(n)+1))

# Large fully certified fixture; all variables exceed the rigorous P0 cutoff.
x=1000000321;y=1000009009;q=6*x*x+1;s=2*y**3+2*y*y+1
assert prime(x) and prime(y)
for t,v in [(x,q),(y,s)]:
    assert (v-1)%(t*t)==0 and (t*t)**2>v and pow(2,v-1,v)==1
    assert gcd(pow(2,(v-1)//t,v)-1,v)==1   # Pocklington, F=t^2.
nodes=[x,q,y,s]
edges={(i,j,h) for i in nodes for j in nodes if i!=j
       for h,f in enumerate([lambda a:6*a*a+1,lambda a:2*a**3+2*a*a+1]) if f(i)==j}
assert edges=={(x,q,0),(y,s,1)}
N,W,ab,C,S,J=check(([(0,2,1,6,1)],[2,1],[x,q]), ([(0,3,1,2,1)],[1,2],[y,s]))
assert (W,ab,C,S,J)==(1,[4,7],24,11000064347,11000064348)
P0=16*(8*4**2*N.bit_length()*3**4+2)
assert x>P0 and (y-x)**2<x
print("certified large case N bits, cutoff, gap, degrees, S minus floor",N.bit_length(),P0,y-x,ab,S-J)

# Reciprocal degree ratio, degree denominators and a truly algebraic leading scale.
N,W,ab,C,S,J=check(([(0,2,2,2,1)],[2,1],[29,41]), ([(0,2,1,4,1)],[1,2],[31,3907]))
assert (W,ab,C,S)==(2,[6,10],512,484)
N,W,ab,C,S,J=check(([(0,1,2,10,1),(1,2,1,2,1)],[1,1,1],[5,7,101]), ([],[1],[11]))
assert (W,ab,C)==(2,[5,2],4000)
print("fractional-degree mixed path W, weights, scale",W,ab,C)

# Synthetic large positive integer edges exercise signed lower coefficients and
# varying multiplicities independently of primality or an infinitude assertion.
count=0;sides=set()
for j in range(6):
    x=10**11+23*j;y=x+29123
    for r0 in (2,3):
        for s0 in (2,3):
            for h1,h2 in [(-1,-1),(-1,1),(1,-1),(1,1)]:
                v=3*x**r0+h1*2*x**(r0-1)+1
                w=7*y**s0+h2*6*y**(s0-1)+1
                n=[1+j%3,2];m=[2,1+j%2]
                N,W,ab,C,S,J=check(([(0,r0,1,3,1)],n,[x,v]), ([(0,s0,1,7,1)],m,[y,w]))
                E=8*16*N.bit_length()*max(r0,s0)**4
                assert x>16*(E+2) and (y-x)**2<x and abs(S-J)<=sum(ab)*(2+3*E)+1
                count+=1;sides.add((S>J)-(S<J))
print("signed synthetic packets / signs of S minus floor",count,sorted(sides))
