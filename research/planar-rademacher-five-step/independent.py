"""Exact witness counts and exhaustive parity-certificate check. Standard library."""
from collections import Counter
from fractions import Fraction as F
from itertools import product,combinations,combinations_with_replacement
from math import prod

def check(b,msg):
    if not b: raise ArithmeticError(msg)

def norm2(V,e):
    return sum(sum(x*s for x,s in zip(col,e))**2 for col in zip(*V))

def dk(e,s):
    # Dvorak-Klein section 7; s is the square of their first coordinate.
    a,b,c,d,h=e
    return s*(a+b)**2+F((a-b+c)**2,9)+F((a-b-c+d+h)**2,25)-(2*s+F(8,15))

def par(e,J):
    return prod(e[i] for i in J)

def parity(n,sz):
    cube=list(product((-1,1),repeat=n)); reps=[e for e in cube if e[0]==1]
    cand=list(combinations(range(n),4))
    for J in cand:
        for y in (-1,1):
            layer=[e for e in cube if par(e,J)==y]
            check(2*len(layer)==2**n,'not half')
            for i,j in combinations(range(n),2):
                check(sum(e[i]*e[j] for e in layer)==0,'moment')
    ctr=0
    for a in combinations_with_replacement(reps,sz):
        check(any(len({par(e,J) for e in a})==1 for J in cand),'no uniform parity')
        ctr+=1
    return ctr

def main():
    V=((0,1),(1,-1),(1,-1),(1,-1),(2,1))
    W=((16,0),(-16,0),(-16,0),(-9,15),(-9,-15))
    all5=list(product((-1,1),repeat=5))
    hist=Counter(norm2(V,e) for e in all5)
    check(hist=={2:6,10:20,26:4,34:2},'witness histogram')
    check(sum(a*a+b*b for a,b in V)==12,'trace')
    check(sum(a*a+b*b for a,b in W)==1380,'dual trace')
    C=Counter()
    for d in all5:
        e=(-d[3],-d[0],d[1],d[2],d[4])
        D=dk(d,F(7,30)); D2=dk(d,F(2,9)); C[D]+=1
        check((norm2(V,e)>=12)==(D<=0),'witness/old sign relation')
        check(D2-D==F(-1,45)*d[0]*d[1],'deformation')
        check(F(norm2(W,d)-1380,3600)==-D2,'rank-two completion')
    check(min(map(abs,C))==F(1,25),'old margin')
    check(parity(4,1)==8,'n4 totals')
    check(parity(5,2)==136,'n5 totals')
    print('PASS: 32 exact norms; rank-two sign equivalence and deformed DK dual; 8 one-class and 136 two-class parity certificates; all conditional quadratic moments zero.')
if __name__=='__main__': main()
