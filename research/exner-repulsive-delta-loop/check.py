"""Exact ancillary checks of the equal-strength proof. Only the analytic proof covers all gaps."""
from fractions import Fraction as F
from itertools import combinations_with_replacement

def need(pred, msg):
    if not pred: raise ValueError(msg)

def add(t, u):
    need(1-t*u > 0, "tangent pole or wrong branch")
    return (t+u)/(1-t*u)

count = equal = unequal = 0
for t in [F(1,4), F(1,2), F(1), F(2)]:
    # k=1, tan(g/2)=t, alpha=2*t. Gap half-angles
    # arctan(t) + j*arctan(h); sum j=0 preserves circumference.
    for h in [F(1,64), F(1,32), F(1,16)]:
        vals = {0:t}
        for sign in [-1,1]:
            a = t
            for j in range(1,4):
                a=add(a,sign*h)
                need(a>0,'angle outside the positive branch')
                vals[j*sign]=a
        for n in range(2,8):
            for js in combinations_with_replacement(range(-3,4),n):
                if sum(js): continue
                gap=2*n*t-2*sum(vals[j] for j in js)
                need((gap == 0 if all(j==0 for j in js) else gap<0),
                     ('Rayleigh form difference',n,t,h,js,gap))
                count+=1
                if gap: unequal+=1
                else: equal+=1
# With g=pi/2, N=3, k=1 and alpha=2, include the other cases.
# Entries are cyclic gaps divided by pi; the endpoint derivative jump of
# sin(pi*s/l) extended by zero has magnitude pi/l rather than zero.
for lengths,bound in [([F(1),F(1,4),F(1,4)],F(1)),
                      ([F(7,6),F(1,6),F(1,6)], F(36,49))]:
    need(sum(lengths)==F(3,2),'circumference')
    ell=max(lengths)
    need(1/ell**2==bound and bound<=1,'Dirichlet quotient')
    need(1/ell>0,'nonzero endpoint jump')
need(count == equal+unequal and count>100,'coverage')
print(f"PASS: {count} rational tangent identities ({unequal} unequal, {equal} equal); threshold and above-threshold gap quotients 1 and 36/49.")
