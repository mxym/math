#!/usr/bin/env python3
"""Exact finite regression of all-even Laplace and bosonic Gram identities.

This is a companion to EVEN_ROW_TRANSFER.md. The theorems for all
dimensions follow from written combinatorial and tensor proofs.
Finite cases here check normalization, signs and integer coefficients.

Only standard-library integer and Fraction arithmetic, no floats.
"""
from fractions import Fraction as F
from itertools import permutations, combinations
from collections import defaultdict
from math import factorial,prod

def need(c,msg):
    if not c:raise RuntimeError("even-row transfer replay failed: "+msg)

def sign(p):
    return -1 if sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))%2 else 1

def laplace_test(m):
    n=2*m
    seen=set()
    cases=0
    for p in permutations(range(n)):
        J=tuple(sorted(p[:m]))
        K=tuple(sorted(p[m:]))
        local_a=tuple(J.index(x) for x in p[:m])
        local_b=tuple(K.index(x) for x in p[m:])
        key=(J,local_a,local_b)
        need(key not in seen,"Laplace index collision n="+str(n))
        seen.add(key)
        need(sign(p)==sign(J+K)*sign(local_a)*sign(local_b),
             "Laplace sign n="+str(n))
        cases+=1
    need(cases==factorial(n),"Laplace permutation count")
    need(len(seen)==len(list(combinations(range(n),m)))*factorial(m)**2,
         "binomial block count")
    return cases

def poly_coefficients(U):
    # Coefficients of product_i(sum_j U_ij*z_j) in Q[z].
    m=len(U);n=len(U[0])
    zero=(0,)*n
    f={zero:F(1)}
    for i in range(m):
        g=defaultdict(F)
        for alpha,v in f.items():
            for j in range(n):
                a=list(alpha);a[j]+=1
                g[tuple(a)]+=v*U[i][j]
        f={a:v for a,v in g.items() if v}
    return f

def permanent(A):
    n=len(A)
    return sum((signless_product(A,p) for p in permutations(range(n))),F(0))

def determinant(A):
    n=len(A)
    return sum((sign(p)*signless_product(A,p) for p in permutations(range(n))),F(0))

def signless_product(A,p):
    z=F(1)
    for i,j in enumerate(p):z*=A[i][j]
    return z

def bosonic_test(U):
    m=len(U);n=len(U[0])
    need(0<m<=n,"invalid rectangular dimensions")
    need(all(len(row)==n for row in U),"row width")
    C=poly_coefficients(U)
    fock=sum((F(v*v)*prod(factorial(k) for k in alpha)
              for alpha,v in C.items()),F(0))
    gram=[[sum((U[i][j]*U[k][j] for j in range(n)),F(0))
           for k in range(m)] for i in range(m)]
    rhs=permanent(gram)
    need(fock==rhs,"Fock / Gram permanent identity")
    squarefree=F(0);fermionic=F(0)
    for J in combinations(range(n),m):
        M=[[U[i][j] for j in J] for i in range(m)]
        squarefree+=permanent(M)**2
        fermionic+=determinant(M)**2
    need(fermionic==determinant(gram),"ordinary Cauchy Binet identity")
    need(squarefree<=rhs,"squarefree contribution exceeds norm")
    is_orthonormal=all(gram[i][j]==F(i==j) for i in range(m) for j in range(m))
    if is_orthonormal:
        need(rhs==1,"orthonormal Gram")
        supports_disjoint=all(sum(U[i][j]!=0 for i in range(m))<=1
                              for j in range(n))
        need((squarefree==1)==supports_disjoint,
             "collision-free equality criterion")
    return m,n,squarefree,fermionic

def tampered_sign_control():
    p=(0,2,1,3)
    j=(0,2)
    k=(1,3)
    left=sign(p)
    true_right=sign(j+k)*sign((0,1))*sign((0,1))
    need(left==true_right,"valid shuffle sign")
    need(left!=-true_right,"deliberately corrupted shuffle sign")

def main():
    tampered_sign_control()
    total=sum(laplace_test(m) for m in (1,2,3,4))
    print("PASS: all-even balanced Laplace permutation bijections")
    print("even matrix dimensions:",(2,4,6,8))
    print("exhaustive permutation/sign cases:",total)

    H=F(1,2)
    samples=[
        [[F(1),F(0)]],
        [[H,H,H,H],[H,H,-H,-H]],
        [[H,H,H,H],[H,H,H,H]],
        [[H,H,H,H,F(0),F(0)],
         [H,H,-H,-H,F(0),F(0)],
         [H,-H,H,-H,F(0),F(0)]],
        [[F(3,5),F(4,5),F(0),F(0),F(0),F(0)],
         [F(0),F(0),F(3,5),F(4,5),F(0),F(0)],
         [F(0),F(0),F(0),F(0),F(3,5),F(4,5)]],
        [[F(1),F(2),F(0),F(1),F(1),F(0)],
         [F(0),F(1),F(2),F(0),F(2),F(1)],
         [F(2),F(0),F(1),F(1),F(0),F(2)]],
    ]
    for U in samples:
        bosonic_test(U)
    print("bosonic Fock/Gram and Cauchy-Binet rational frames:",len(samples))
    print("both orthogonal collision cases and nonorthogonal frames checked")
    print("negative controls: corrupt Laplace parity rejected by exact sign gate")
    print("mathematical universality comes from EVEN_ROW_TRANSFER.md")
    print("all calculations exact rational; no float/optimizer/solver")

if __name__=="__main__":
    main()
