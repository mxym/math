#!/usr/bin/env python3
"""Exact algebraic verification of all-fixed-rank Lobatto dual/primal identities.

No numerical solver, floating point, or optimizer. SymPy is optional and only
needed for this finite regression; the written all-k proof is analytic.

Checks k=1..6:
  * Chebyshev alternation, endpoint derivative, node positivity;
  * Lagrange endpoint differentiation formula on every monomial degree <= k;
  * equality of the identity-mass first-order coefficient 2 k^2;
  * exact limiting rank-k primal matrix equations.
"""
import sympy as S

def bernstein(j,k,a):
    return S.binomial(k,j)*a**j*(1-a)**(k-j)

def verify(k):
    nodes=[S.simplify((1+S.cos(S.pi*j/k))/2)
           for j in range(k+1)]
    weights=[S.simplify(8*(S.Rational(1,2) if j==k else S.Integer(1))
                        /(1-S.cos(S.pi*j/k)))
             for j in range(1,k+1)]
    x=S.symbols('x')
    H=(1-S.chebyshevt(k,2*x-1))/2
    assert S.simplify(H.subs(x,1))==0
    assert S.simplify(S.diff(H,x).subs(x,1)+k*k)==0
    for j,a in enumerate(nodes):
        assert S.simplify(H.subs(x,a)-S.Rational(1-(-1)**j,2))==0
    for r in range(k+1):
        total=sum((-1)**(j+1)*weights[j-1]*(nodes[j]**r-1)
                  for j in range(1,k+1))
        assert S.simplify(total+2*r)==0,(k,r,total)
    assert S.simplify(sum(weights[j-1] for j in range(1,k+1)
                           if j%2==1)-2*k*k)==0

    # Limiting full-moment equality, including final j=k via normalization:
    for j in range(k+1):
        term=sum((-1)**(q+1)*weights[q-1]*
                 (bernstein(j,k,nodes[q])-bernstein(j,k,1))
                 for q in range(1,k+1))
        rhs=2*k*(int(j==k-1)-int(j==k))
        assert S.simplify(term-rhs)==0,(k,j,term,rhs)
    # The limiting matrix has independent columns, since the evaluation
    # differences at k nonidentity Lobatto nodes span polynomial duality.
    mat=S.Matrix([[
        (-1)**(q+1)*(bernstein(j,k,nodes[q])-bernstein(j,k,1))
        for q in range(1,k+1)]
        for j in range(k)])
    assert S.simplify(mat.det())!=0
    assert all(w.is_positive for w in weights)
    print('PASS k=%d: Chebyshev extrema, derivative weights, limit primal det'
          %k,flush=True)

def main():
    for k in range(1,7):
        verify(k)
    print('SIX EXACT ALGEBRAIC LOBATTO CHECKS PASSED')

if not __debug__:
    raise RuntimeError('Run without -O: optimized Python disables assert checks')

if __name__=='__main__':
    main()
