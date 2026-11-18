"""Exact checks. Python standard library only; python -O is supported."""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import permutations, product
from math import comb

def require(truth, label):
    if not truth:
        raise ArithmeticError(label)

def mm(x, y):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*y)] for row in x]

def charpoly(matrix):
    """Leibniz expansion of det(xI-M); coefficients in ascending order."""
    n=len(matrix)
    acc=[0]*(n+1)
    for p in permutations(range(n)):
        coeff=[(-1)**sum(p[j]>p[k] for j in range(n) for k in range(j+1,n))]
        for i,j in enumerate(p):
            fac0=-matrix[i][j];fac1=int(i==j)
            nxt=[0]*(len(coeff)+1)
            for k,c in enumerate(coeff):
                nxt[k]+=c*fac0;nxt[k+1]+=c*fac1
            coeff=nxt
        acc=[a+b for a,b in zip(acc,coeff)]
    return acc

def roots(poly, candidates):
    out=Counter()
    for x in candidates:
        while len(poly)>1:
            quot=list(reversed(poly))
            for j in range(1,len(quot)):
                quot[j]+=x*quot[j-1]
            if quot[-1] != 0: break
            out[x]+=1
            poly=quot[:-1][::-1]
    require(poly==[1], ('unexpected roots',poly))
    return out

def block_result(d, sign):
    """Build blocks from the channel's matrix units and the initial state.
    Matrix whose spectrum is reported is 2*d*(d+sign)*R. Blocks are
    organized by multisets of input-register and output-register indices."""
    sector=defaultdict(list)
    for t in product(range(d),repeat=3): sector[tuple(sorted(t))].append(t)
    k=d*(d+sign); found=Counter()
    for ts in sector.values():
        # k*rho on the two input registers tensor identity on output
        W=[[int(w==z)+sign*int(w==(z[1],z[0],z[2])) for z in ts] for w in ts]
        # J[row,column] = <output row|Tr_1(|input col><input row|)|output col>
        J=[[int(i==l and j==o and n==a) for l,n,o in ts] for i,j,a in ts]
        U,V=mm(W,J),mm(J,W)
        P=[[x+y for x,y in zip(r,t)] for r,t in zip(U,V)]
        found+=roots(charpoly(P),[-4,-3,-1,0,1,3,4])
    expected=Counter()
    for mu,multi in [(2+2*sign,comb(d+2,3)),(-2+2*sign,comb(d,3)),
                     (2-sign,d*(d*d-1)//3),(-2-sign,d*(d*d-1)//3)]:
        expected[mu]+=multi
    require(found==expected,('spectrum',d,sign,found,expected))
    require(sum(x*m for x,m in found.items())==2*k,('trace',d,sign))
    # I = log d - log 2 + (1/k) sum mu log |mu| for mu=x/2.
    code={4:(1,0),3:(-1,1),1:(-1,0)}   # coefficients of log 2 and log 3
    u,v=Q(-1),Q(0)
    for x,m in found.items():
        if x:
            a,b=code[abs(x)];w=Q(x*m,2*k);u+=w*a;v+=w*b
    require((u,v)==(Q(2,3)*(sign*d-1),Q(1-sign*d,2)),('I formula',d,sign,u,v))
    return found

for d in range(2,8):
    plus=block_result(d,1); minus=block_result(d,-1)
    print(f'd={d}: both signed spectra, unit traces and log coefficients verified')
require(27**3>4*16**3,'(27/16)^3>4')
require(63>9*6 and 65>9*6,'d=64 two-sided witness')
require(257>9*24,'d=256 square-channel upper witness')
print('Exact finite-violation integer certificates verified.')
