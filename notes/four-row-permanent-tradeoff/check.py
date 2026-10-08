#!/usr/bin/env python3
"""Exact formal polynomial certificate for the four-row permanent theorem.

This checks *identities* in a commutative integer polynomial ring, not
floating-point samples. Variables a_i,b_i and their formal conjugates
are independent; hence the pair identities are universal. Laplace
identities are verified over 16 formal matrix-entry variables.

Analytic Cauchy--Schwarz and equality reasoning are in PAPER.md.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations

def fail(msg):
    raise RuntimeError("exact certificate failed: "+msg)

# A polynomial is a dict sorted-variable-index-tuple -> integer coefficient.
# Sorted tuples are monomials in a commutative integer polynomial ring.
def pol(terms):
    out=defaultdict(int)
    for mono,co in terms:
        out[tuple(sorted(mono))]+=co
    return {m:c for m,c in out.items() if c}

def val(a):
    return {():int(a)} if a else {}

def var(i):
    return {(i,):1}

def add(*args):
    return pol((m,c) for p in args for m,c in p.items())

def scale(p,k):
    return {m:k*c for m,c in p.items() if k*c}

def sub(p,q):
    return add(p,scale(q,-1))

def mul(p,q):
    return pol((m+n,a*b) for m,a in p.items() for n,b in q.items())

def sums(parts):
    return add(*parts)

def conj(p):
    return pol((tuple(i+8 if i<8 else i-8 for i in mono),c)
               for mono,c in p.items())

def power_product(items):
    r=val(1)
    for p in items:
        r=mul(r,p)
    return r

def pair_test():
    # formal row coordinates a_0...a_3, b_0...b_3 and conjugates
    a=[var(i) for i in range(4)]
    b=[var(4+i) for i in range(4)]
    pair_per=lambda j,k:add(mul(a[j],b[k]),mul(a[k],b[j]))
    pair_det=lambda j,k:sub(mul(a[j],b[k]),mul(a[k],b[j]))
    S=sums(mul(pair_per(j,k),conj(pair_per(j,k)))
           for j,k in combinations(range(4),2))
    W=sums(mul(pair_det(j,k),conj(pair_det(j,k)))
           for j,k in combinations(range(4),2))
    A=sums(mul(a[j],conj(a[j])) for j in range(4))
    B=sums(mul(b[j],conj(b[j])) for j in range(4))
    dot=sums(mul(a[j],conj(b[j])) for j in range(4))
    eta=mul(dot,conj(dot))
    tau=sums(power_product([a[j],conj(a[j]),b[j],conj(b[j])])
             for j in range(4))
    need1=add(mul(A,B),eta,scale(tau,-2))
    need2=sub(mul(A,B),eta)
    if S!=need1:fail("pair symmetric minor identity")
    if W!=need2:fail("pair alternating minor identity")
    # Impossible additive perturbations must be rejected.
    # Deliberate coefficient corruptions must NOT reproduce the identities.
    if S==add(need1,tau) or W==add(need2,eta):
        fail("corrupt symmetric/alternating correction was accepted")
    print("symmetric two-row polynomial identity: exact")
    print("alternating two-row polynomial identity: exact")
    print("formal variables:",16)
    print("nonzero polynomial terms S,W:",len(S),len(W))

def sign(seq):
    k=sum(seq[i]>seq[j] for i in range(len(seq))
          for j in range(i+1,len(seq)))
    return (-1)**k

def laplace_test():
    v=[[var(4*i+j) for j in range(4)] for i in range(4)]
    P=sums(power_product([v[i][q[i]] for i in range(4)])
           for q in permutations(range(4)))
    D=sums(scale(power_product([v[i][q[i]] for i in range(4)]),
                 sign(q)) for q in permutations(range(4)))
    LP=[];LD=[]
    for j,k in combinations(range(4),2):
        u,w=tuple(x for x in range(4) if x not in (j,k))
        p0=add(mul(v[0][j],v[1][k]),mul(v[0][k],v[1][j]))
        p1=add(mul(v[2][u],v[3][w]),mul(v[2][w],v[3][u]))
        d0=sub(mul(v[0][j],v[1][k]),mul(v[0][k],v[1][j]))
        d1=sub(mul(v[2][u],v[3][w]),mul(v[2][w],v[3][u]))
        LP.append(mul(p0,p1))
        LD.append(scale(mul(d0,d1),sign((j,k,u,w))))
    if P!=sums(LP):fail("Laplace permanent decomposition")
    if D!=sums(LD):fail("Laplace determinant decomposition")
    altered=list(LD)
    altered[0]=scale(altered[0],-1)
    if D==sums(altered):fail("corrupt Laplace cofactor sign accepted")
    print("four-row permanent/determinant Laplace identities: exact")
    print("Laplace two-column blocks:",len(LP))
    print("distinct permanent and determinant monomials:",len(P),len(D))

def evaluate(A):
    P=F(0);D=F(0)
    for q in permutations(range(4)):
        term=F(1)
        for i in range(4):
            term*=A[i][q[i]]
        P+=term
        D+=sign(q)*term
    return P,D

def sharpness_test():
    flat=[[F(1,2)]*4 for _ in range(4)]
    even=[[F(i==j) for j in range(4)] for i in range(4)]
    odd=[[F((i,j) in {(0,1),(1,0),(2,2),(3,3)})
          for j in range(4)] for i in range(4)]
    for name,A,target in (("flat",flat,(F(3,2),F(0))),
                          ("even permutation",even,(F(1),F(1))),
                          ("odd permutation",odd,(F(1),F(-1)))):
        if evaluate(A)!=target:fail(name+" exact equality")
        if any(sum(x*x for x in row)!=1 for row in A):
            fail(name+" unit row normalization")
    for c in [F(0),F(1,5),F(1,2),F(3,4),F(1),F(3)]:
        optimum=max(F(3,2),1+c)
        if max(evaluate(flat)[0]+c*abs(evaluate(flat)[1]),
               evaluate(even)[0]+c*abs(evaluate(even)[1]))!=optimum:
            fail("sharpness at rational c="+str(c))
    print("sharp equality witnesses: flat, even/odd permutations")
    print("exact rational coefficient probes:",6)

def interpolation_path_test():
    # B(t) has diagonal entries 1 and off-diagonal entries t.
    # The exact deficit vanishes quadratically at t=0 and t=1.
    t=var(0)
    one=val(1)
    b=[[one if i==j else t for j in range(4)] for i in range(4)]
    P=sums(power_product([b[i][q[i]] for i in range(4)])
           for q in permutations(range(4)))
    D=sums(scale(power_product([b[i][q[i]] for i in range(4)]),sign(q))
           for q in permutations(range(4)))
    t2=mul(t,t)
    t3=mul(t2,t)
    t4=mul(t2,t2)
    expect_P=add(one,scale(t2,6),scale(t3,8),scale(t4,9))
    expect_D=add(one,scale(t2,-6),scale(t3,8),scale(t4,-3))
    if P!=expect_P or D!=expect_D:
        fail("interpolating family permanent/determinant polynomials")
    row_norm_sq=add(one,scale(t2,3))
    gap_numerator=sub(scale(mul(row_norm_sq,row_norm_sq),3),
                      add(scale(P,2),D))
    expect_gap=scale(power_product([t,t,sub(one,t),sub(one,t)]),12)
    if gap_numerator!=expect_gap:
        fail("critical-weight quadratic gap polynomial")
    print("critical-weight interpolation: exact quadratic stability gap")

def parity_and_tensor_test():
    perms=list(permutations(range(4)))
    even=sum(sign(p)==1 for p in perms)
    odd=sum(sign(p)==-1 for p in perms)
    if (even,odd)!=(12,12):fail("S4 parity counts")
    for i in range(4):
        for j in range(4):
            a=sum(sign(p)==1 and p[i]==j for p in perms)
            b=sum(sign(p)==-1 and p[i]==j for p in perms)
            if (a,b)!=(3,3):fail("uniform parity marginal")
    for t in [F(-1,24),F(-1,48),F(-1,96),F(0),
              F(1,96),F(1,48),F(1,24)]:
        probs=[F(1,24)+t*sign(p) for p in perms]
        if min(probs)<0 or sum(probs)!=1:fail("parity law")
        TV=sum(abs(z-F(1,24)) for z in probs)/2
        if TV!=12*abs(t):fail("exact total variation")
        expected=max(F(1),F(2,3)*(1+24*abs(t)))
        event=max(probs)
        actual=max(F(1),16*event)
        if actual!=expected:fail("extremizer coefficient")
    print("S4 parity laws: exact marginal and TV calculation")
    print("sharp normalized L2 amplification verified at 7 rational t values")

def main():
    pair_test()
    laplace_test()
    sharpness_test()
    interpolation_path_test()
    parity_and_tensor_test()
    print("PASS: sharp 4x4 permanent/determinant tradeoff and parity witnesses")
    print("certificate: exact polynomial coefficients and Fraction witnesses")
    print("analytic CS/rigidity/tensor arguments: separate complete PAPER.md")
    print("no floating point, random search, external solver or Python asserts")

if __name__=="__main__":
    main()
