"""Independent exact controls; the asymptotic estimates themselves are analytic."""
from itertools import combinations_with_replacement as multi
from fractions import Fraction as Fr
from math import gcd, prod
from pathlib import Path
from functools import cache
def ck(ok, context):
    if not ok:
        raise ValueError(context)
@cache
def factors(n):
    r = []
    j = 2
    while j*j <= n:
        e = 0
        while n%j == 0:
            n//=j; e+=1
        if e: r.append((j,e))
        j+=1
    if n>1: r.append((n,1))
    return tuple(r)
def subsets(tup):
    pairs=[(0,1)]
    for x in tup:
        pairs = pairs+[(a+x,-v) for a,v in pairs]
    return pairs
def K(xs):
    tot=sum(xs)
    return sum(v*max(0,tot-2*a)**2 for a,v in subsets(xs))
def basic_shapes():
    tested=0
    for rank in range(2,9):
        for xs in multi(range(1,8),rank):
            y=K(xs); tested+=1
            if rank==2: ck(y==4*prod(xs),('even base',xs,y))
            elif rank%2==0: ck(y==0,('even',xs,y))
            elif rank==3: ck(y>=0,('three',xs,y))
            elif rank==5: ck(y<=0,('five',xs,y))
    # Constrain both actual leg exponents to the same total, each with
    # >=two factors. Values are log masses; a vanishingly thin PNT box
    # preserves any strict sign.
    signs={}
    for a in multi(range(1,12),2):
        if sum(a)!=12: continue
        for b in multi(range(1,9),5):
            if sum(b)!=12: continue
            y=K(a+b)
            if y: signs.setdefault((1 if y>0 else -1),(a,b,y))
    ck(set(signs)=={1,-1},signs)
    print('integer log profiles:',tested,'rank-7 witnesses:',signs)
def prime_leg():
    cnt=0
    for r in range(1,8):
        for t in multi(range(1,7),r):
            m=sum(t)
            for p in [m-1,m,m+1]:
                if p<=0: continue
                full=sum(v*(m+p-2*a)**2 for a,v in subsets(t))
                formula={1:4*m*p,2:8*prod(t)}.get(r,0)
                ck(full==formula,('full finite difference',p,t,full))
                ck(K((p,)+t)==full-(1+(-1)**r)*max(0,m-p)**2,('complement',p,t))
                cnt+=1
    print('prime-leg controls:',cnt)
def local_eulers():
    tests=0
    for p in [2,3,5,7,11,13,17,19]:
        for N in range(2,64,2):
            for t in (Fr(0),Fr(2,7),Fr(1),Fr(5,4)):
                w=[(1-t if n*(N-n)%p==0 else 1) for n in range(p*p)]
                sf=[int(n*(N-n)%(p*p)!=0) for n in range(p*p)]
                plain=Fr(sum(w),p*p); masked=Fr(sum(a*b for a,b in zip(w,sf)),p*p)
                ck(plain==1-(1 if N%p==0 else 2)*t/p,(p,N,t,'plain'))
                goal=1-Fr(1,p) if N%p==0 else 1-2*t/p-2*(1-t)/(p*p)
                ck(masked==goal,(p,N,t,masked,goal))
                if t==1: ck(plain==masked,('same pole',p,N))
                tests+=1
    print('local Euler evaluations:',tests)
def assignment():
    tests=0
    for N in range(4,300,2):
        for n in range((N+2)//3,2*N//3+1):
            gs=tuple(p for p,e in factors(n*(N-n)) if N%p==0)
            aa=tuple(p for p,e in factors(n) if N%p)
            bb=tuple(p for p,e in factors(N-n) if N%p)
            fr=tuple(p for p,e in factors(n*(N-n)))
            ck(sorted(gs+aa+bb)==sorted(fr),('root partition',n,N))
            ck(gcd(n,N)==1 or any(e>=2 for p,e in factors(n*(N-n))),('unit',n,N))
            tests+=1
    print('physical CRT inputs:',tests)
def rails():
    eps=Fr(1,100000)
    lhs=(Fr(1,2)+Fr(7,20))*(1+2*eps)+Fr(55,100)/4+2*eps+4*eps
    ck(lhs<Fr(99,100),('BC first',lhs))
    lhs2=(Fr(1,2)+Fr(3,8))*(1+2*eps)+Fr(55,100)/8+2*eps+4*eps
    ck(lhs2<Fr(99,100),('BC second',lhs2))
    ck((Fr(1,100)-4*eps)/2>Fr(48,10000), 'Type II')
    b=Path(__file__).with_name('Proof.md').read_bytes()
    ck(not any(c<32 and c!=10 for c in b),'unwanted control byte')
    ck(b.count(b'$$')==34,'math block pairing')
    print('exponent and source integrity controls passed')
if __name__=='__main__':
    basic_shapes(); prime_leg(); local_eulers(); assignment(); rails()
