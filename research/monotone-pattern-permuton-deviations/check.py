"""Exact finite checks for two-axis encodings and the Mallows comparison. Stdlib only."""
from itertools import groupby, permutations, product
from fractions import Fraction as Q
from collections import defaultdict, Counter
from math import factorial

def must(b,msg):
    if not b:raise ArithmeticError(msg)
def inv(w):return sum(x>y for j,x in enumerate(w) for y in w[j+1:])
def asc(w):return sum(x<y for j,x in enumerate(w) for y in w[j+1:])
def height(p):
    h=[]
    for j,x in enumerate(p):h.append(1+max((h[i] for i in range(j) if p[i]>x),default=0))
    return tuple(h)
def decode(u,v):
    positions={c:iter([i for i,x in enumerate(v) if x==c]) for c in set(u)}
    return tuple(next(positions[c]) for c in u)
def encode(p):
    h=height(p)
    return h,tuple(h[p.index(i)] for i in range(len(p)))
def qfact(n,q):
    s=Q(1)
    for j in range(1,n+1):s*=sum(q**i for i in range(j))
    return s
def qmult(ns,q):
    s=qfact(sum(ns),q)
    for n in ns:s/=qfact(n,q)
    return s
cases=can=contents=ineq=0
for d in (2,3):
    for n in range(1,7):
        wp=defaultdict(list)
        for w in product(range(1,d+1),repeat=n): wp[tuple(w.count(i) for i in range(1,d+1))].append(w)
        accepted={p for p in permutations(range(n)) if max(height(p))<=d}
        cur=set()
        for ns,ws in wp.items():
            ws_a=[(w,asc(w)) for w in ws]
            # Check q products at rational q and verify both factors by exact enumeration.
            for q in (Q(2),Q(3,2)):
                plus=sum(q**a for w,a in ws_a)
                minus=sum(q**(-a) for w,a in ws_a)
                must(plus*minus==qmult(ns,q)*qmult(ns,1/q),'Gaussian product')
                contents+=1
            for u,au in ws_a:
                for v,av in ws_a:
                    p=decode(u,v);v0=inv(p)
                    must(p in accepted and v0>=au-av,'signed inversion bound')
                    red=encode(p)
                    if (u,v)==red:
                        must(au-av==v0 and p not in cur,'canonical equality/uniqueness')
                        cur.add(p);can+=1
                    else:ineq+=v0>au-av
                    cases+=1
        must(cur==accepted,'missed an uncoloured avoiding permutation')
# Exhaustive within-bin interleavings on a three-layer shifted diagonal template:
# equal original abscissae for distinct colours, +/- (colour-1)*3 integer shift,
# bins twice as wide as the original point spacing and narrower than witness gap.
def axis_options(points,side):
    inner=defaultdict(list)
    for col,i in points:
        raw=i+(col-1)*3*(1 if side==0 else -1)
        inner[raw//2].append(col)
    return [sum(seq,()) for seq in product(*(sorted(set(permutations(inner[b]))) for b in sorted(inner)))]
sample=[(c,j) for c in range(1,4) for j in (0,2,4,6)]
xs=axis_options(sample,0);ys=axis_options(sample,1)
out=set()
for u in xs:
    for v in ys:
        p=decode(u,v)
        must(encode(p)==(u,v),'lost a northwest witness in fine boxes')
        out.add(p)
must(len(out)==len(xs)*len(ys)>1,'weighted rather than uncoloured lower count')
# d=2 comparison to BDFKM Thm 7: put s=exp(beta/2), t=exp(beta*x).
# The first colour gives upper curve with exponentiated ordinate U(t); the
# second is inverse U^{-1}, which is BDFKM's expression, not two identical graphs.
curves=0
for s in (Q(3,2),Q(2),Q(4),Q(9)):
    for i in range(21):
        t=1+(s*s-1)*i/20
        lo=s*(t+s)/(1+s+s*s-t)
        up=((1+s+s*s)*lo-s*s)/(lo+s)
        must(up==t and 1<=lo<=t<=s*s,'d=2 ordered quantile curve formula')
        curves+=1
print('two-axis word pairs:',cases,'; canonical permutations:',can,'; strict signed gaps:',ineq)
print('rational Gaussian multinomial products:',contents)
print('stable box reorderings:',len(out),'(horizontal',len(xs),'x vertical',len(ys),')')
print('exact d=2 formula checks:',curves)
print('PASS')
