#!/usr/bin/env python3
"""Independent audit. No imports from the candidate's artifacts. Standard library only."""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json

# Polynomials in n, represented by exponent -> exact rational coefficient.
def add(p,q):
    ans=dict(p)
    for i,x in q.items(): ans[i]=ans.get(i,F(0))+x
    return {i:x for i,x in ans.items() if x}
def neg(p): return {i:-x for i,x in p.items()}
def sub(p,q): return add(p,neg(q))
def mul(p,q):
    ans={}
    for i,x in p.items():
        for j,y in q.items(): ans[i+j]=ans.get(i+j,F(0))+x*y
    return {i:x for i,x in ans.items() if x}
def power(p,k):
    out={0:F(1)}
    for _ in range(k): out=mul(out,p)
    return out
def div(p,d): return {i:x/F(d) for i,x in p.items()}
def atom(c): return {0:F(c)} if c else {}
def linear(c): return add({1:F(1)},atom(c))
def evaluate(p,x): return sum(v*x**i for i,v in p.items())

def binomial_poly(k):
    p=atom(1)
    for j in range(k): p=mul(p,linear(-j))
    return div(p,factorial(k))

def transform_sparse(a,n):
    return {k:a.get(k,0)**2-a.get(k-1,0)*a.get(k+1,0) for k in range(n+1)}
def transform_list(a):
    padded=[0]+a+[0]
    return [v*v-left*right for left,v,right in zip(padded,padded[1:],padded[2:])]
def transform_trim(a): return [a[k]**2-a[k-1]*a[k+1] for k in range(1,len(a)-1)]
def row(n): return [0,n-1]+[comb(n,k) for k in range(2,n+1)]

def inclusion_exclusion_cycle(n):
    # Generic graph edge-subset inclusion-exclusion, with disjoint-set components.
    edges=[(i,(i+1)%n) for i in range(n)]
    coeff=[0]*(n+1)
    for mask in range(1<<n):
        par=list(range(n)); comps=n
        def root(i):
            while par[i]!=i:
                par[i]=par[par[i]]; i=par[i]
            return i
        for e,(u,v) in enumerate(edges):
            if mask&(1<<e):
                ru,rv=root(u),root(v)
                if ru!=rv: par[ru]=rv; comps-=1
        coeff[comps]+=(-1)**mask.bit_count()
    return coeff

out={}
for n,depth in [(12,5),(17,3)]:
    signed=inclusion_exclusion_cycle(n)
    a=row(n)
    assert [abs(x) for x in signed]==a
    sequence=[a]
    for r in range(depth):
        sparse=transform_sparse(dict(enumerate(a)),n)
        a=transform_list(a)
        assert list(sparse.values())==a
        sequence.append(a)
    out[f'C{n}']={'signed_chromatic':signed,'iterates':sequence}
assert out['C17']['iterates'][2][1:4]==[65536,22491136,8150077440]
assert out['C17']['iterates'][3][2]==-28272276537344==-30464**3
assert out['C12']['iterates'][5][2]==-249621701601023742801969101519201265582387397744
assert all(x>=0 for a in out['C12']['iterates'][:5] for x in a)

# Exact symbolic identities, rather than evaluations at finitely many integers.
a={0:{},1:linear(-1),**{k:binomial_poly(k) for k in range(2,6)}}
b={k:sub(power(a[k],2),mul(a.get(k-1,{}),a.get(k+1,{}))) for k in range(5)}
c={k:sub(power(b[k],2),mul(b[k-1],b[k+1])) for k in range(1,4)}
d2=sub(power(c[2],2),mul(c[1],c[3]))
n=linear(0); m=linear(-1)
expected_b={
 1:power(m,2),
 2:div(mul(mul(n,power(m,2)),linear(4)),12),
 3:div(mul(mul(mul(power(n,2),linear(-2)),power(m,2)),linear(1)),144),
 4:div(mul(mul(mul(mul(power(n,2),linear(-3)),power(linear(-2),2)),power(m,2)),linear(1)),2880)}
expected_c={
 1:power(m,4),
 2:div(mul(mul(power(n,2),power(m,4)),linear(2)),16),
 3:div(mul(mul(mul(mul(power(n,3),power(linear(-2),2)),power(m,4)),linear(1)),{2:F(1),1:F(1),0:F(18)}),51840)}
assert all(b[k]==v for k,v in expected_b.items())
assert all(c[k]==v for k,v in expected_c.items())
Q={4:F(2),3:F(-12),2:F(-327),1:F(-412),0:F(36)}
expected_d=neg(div(mul(mul(mul(power(n,3),power(m,8)),linear(4)),Q),103680))
assert d2==expected_d
shift={}
for i,v in Q.items(): shift=add(shift,mul(atom(v),power(linear(17),i)))
assert shift=={4:F(2),3:F(124),2:F(2529),1:F(17370),0:F(6615)}
assert evaluate(d2,17)==-28272276537344
out['symbolic_d2']={str(k):str(v) for k,v in sorted(d2.items())}
out['Q_shifted_at_17']={str(k):str(v) for k,v in sorted(shift.items())}

# Endpoint-deleting interpretation, using only actual degree-indexed coefficients.
for n,zeros,depth in [(17,1,3),(12,3,5)]:
    a=[0]*zeros+row(n)
    for _ in range(depth): a=transform_trim(a)
    # Surviving list index 0 has original degree depth.
    assert a[2+zeros-depth]==out[f'C{n}']['iterates'][depth][2]
    out[f'trim_C{n}_plus_{zeros}_isolates']={'original_negative_degree':2+zeros,'depth':depth,'value':a[2+zeros-depth]}

# Classification positive certificates, separately computed from scratch.
expected_positive={3:(0,3),4:(1,28),5:(2,25825),6:(2,90846),7:(2,271656),8:(3,711608924160),9:(3,4029124698225),10:(3,19225238518750),11:(3,79738750726206)}
positive={}
for n,(depth,minimum) in expected_positive.items():
    a=row(n); history=[a]
    for _ in range(depth): a=transform_list(a); history.append(a)
    assert all(x>=0 for r in history for x in r)
    z=[0]+a+[0]
    slack=[z[k]**2-3*z[k-1]*z[k+1] for k in range(1,len(z)-1)]
    assert all(s>=0 for s in slack)
    assert min(slack[2:n])==minimum
    positive[n]={'depth':depth,'minimum_interior_slack':minimum,'certifying_sequence':a,'all_slacks':slack}
out['positive_certificates']=positive
negative={13:-3618341131654935620812800,14:-199158562975246657489530096,15:-2734560032125157358883149375,16:-25982668618402950000000000000}
for n,want in negative.items():
    a=row(n)
    for j in range(4):
        assert all(v>=0 for v in a)
        a=transform_list(a)
    assert a[2]==want
out['negative_fourth_iterates']=negative
Path(__file__).with_name('independent_exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: independent graph edge-subset inclusion-exclusion for C12 and C17')
print('PASS: two independent integer implementations of each full iterate')
print('PASS: C17 L^3[2] =',out['C17']['iterates'][3][2])
print('PASS: exact rational-polynomial identities for every b/c entry and general L^3[2]')
print('PASS: Q(n) has all-positive coefficients after n=u+17')
print('PASS: endpoint-deleting C17 + K1 and C12 + 3K1 certificates')
print('PASS: all classification certificates C3..C16; infinite tail by symbolic identity')
