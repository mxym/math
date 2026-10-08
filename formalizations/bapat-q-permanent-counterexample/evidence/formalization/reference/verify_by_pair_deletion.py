#!/usr/bin/env python3
"""Independent exact certificate: explicit sum over deleted factor pairs.

Only Python's standard library. No import or reuse of either author's verifier.
Gaussian integers are pairs of ints; no complex, float, or approximate arithmetic
is used in any mathematical check. All synthetic divisions assert zero remainder.
"""
import csv
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import sys

Z=(0,0)
ONE=(1,0)
def add(z,w): return (z[0]+w[0],z[1]+w[1])
def neg(z): return (-z[0],-z[1])
def sub(z,w): return add(z,neg(w))
def mul(z,w): return (z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def conj(z): return (z[0],-z[1])
def scale(z,m): return (z[0]*m,z[1]*m)
def norm(z): return z[0]*z[0]+z[1]*z[1]
def divide_exact(z,w):
    d=norm(w)
    assert d>0
    numerator=mul(z,conj(w))
    qr,rr=divmod(numerator[0],d)
    qi,ri=divmod(numerator[1],d)
    assert rr==0 and ri==0, (z,w)
    return (qr,qi)

def multiply_linear(p,a,b):
    out=[Z]*(len(p)+1)
    for k,c in enumerate(p):
        out[k]=add(out[k],mul(a,c))
        out[k+1]=add(out[k+1],mul(b,c))
    return out

def product(rows):
    p=[ONE]
    for a,b in rows: p=multiply_linear(p,a,b)
    return p

def divide_linear(p,a,b):
    # p[k] is the coefficient of x^(degree-k) y^k.
    assert len(p)>=2 and (a!=Z or b!=Z)
    if a==Z:
        assert p[0]==Z
        return [divide_exact(c,b) for c in p[1:]]
    q=[divide_exact(p[0],a)]
    for k in range(1,len(p)-1):
        q.append(divide_exact(sub(p[k],mul(b,q[-1])),a))
    assert p[-1]==mul(b,q[-1]), 'nonzero synthetic-division remainder'
    return q

def determinant(v,w): return sub(mul(v[0],w[1]),mul(v[1],w[0]))
def gram(rows):
    return [[add(mul(a,conj(c)),mul(b,conj(d))) for c,d in rows] for a,b in rows]
def factorial_norm(p):
    degree=len(p)-1
    return sum(math.factorial(k)*math.factorial(degree-k)*norm(c) for k,c in enumerate(p))

def forms_by_deletion(rows):
    n=len(rows)
    f=product(rows)
    s=[Z]*(n-1)
    for i,(a,b) in enumerate(rows):
        without_i=divide_linear(f,a,b)
        for j in range(i+1,n):
            without_ij=divide_linear(without_i,*rows[j])
            delta=determinant(rows[i],rows[j])
            for k,c in enumerate(without_ij): s[k]=add(s[k],mul(delta,c))
    return f,s

def forms_by_rebuilding(rows):
    # Separate reference for small-n tests; never divides a polynomial.
    n=len(rows)
    f=product(rows)
    s=[Z]*(n-1)
    for i,j in itertools.combinations(range(n),2):
        p=product([r for k,r in enumerate(rows) if k!=i and k!=j])
        d=determinant(rows[i],rows[j])
        for k,c in enumerate(p): s[k]=add(s[k],mul(d,c))
    return f,s

def enumerated_q_coefficients(matrix):
    n=len(matrix)
    c=[Z]*(n*(n-1)//2+1)
    for perm in itertools.permutations(range(n)):
        inv=sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
        term=ONE
        for i,j in enumerate(perm): term=mul(term,matrix[i][j])
        c[inv]=add(c[inv],term)
    return c

def small_tests():
    rng=random.Random(20261008)
    tested=[]
    cases=[[(Z,ONE),(ONE,Z)],[(ONE,Z),(ONE,Z),(ONE,ONE)],
           [((1,1),(2,-1)),((3,-2),(-1,1)),((0,2),(1,-3))]]
    for n in range(2,9):
        for _ in range(3 if n<=6 else 1):
            rows=[]
            for __ in range(n):
                while True:
                    row=tuple((rng.randint(-3,3),rng.randint(-3,3)) for ___ in range(2))
                    if row!=(Z,Z): break
                rows.append(row)
            cases.append(rows)
    for rows in cases:
        f,s=forms_by_deletion(rows)
        assert (f,s)==forms_by_rebuilding(rows)
        n=len(rows); N=n*(n-1)//2
        c=enumerated_q_coefficients(gram(rows))
        p=Z; derivative=Z
        for inv,v in enumerate(c):
            assert v[1]==0, 'Hermitian q coefficient must be real'
            p=add(p,v); derivative=add(derivative,scale(v,inv))
        assert p==(factorial_norm(f),0)
        assert scale(derivative,2)==(N*factorial_norm(f)-factorial_norm(s),0)
        tested.append({'n':n,'permanent':str(p[0]),'endpoint_derivative':str(derivative[0])})
    return tested

def general_matrix_tests():
    rng=random.Random(89208818174)
    results=[]
    for n in range(2,7):
        N=n*(n-1)//2
        A=[[(rng.randint(-2,2),rng.randint(-2,2)) for _ in range(n)] for __ in range(n)]
        c=enumerated_q_coefficients(A)
        per=Z; derivative=Z
        for inv,v in enumerate(c):
            per=add(per,v); derivative=add(derivative,scale(v,inv))
        H=Z; marked_inversions=Z
        for i,j in itertools.combinations(range(n),2):
            I=[r for r in range(n) if r not in (i,j)]
            for k,l in itertools.combinations(range(n),2):
                J=[r for r in range(n) if r not in (k,l)]
                minor=[[A[r][s] for s in J] for r in I]
                minor_per=Z
                for coefficient in enumerated_q_coefficients(minor): minor_per=add(minor_per,coefficient)
                parallel=mul(A[i][k],A[j][l])
                crossed=mul(A[i][l],A[j][k])
                H=add(H,mul(sub(parallel,crossed),minor_per))
                marked_inversions=add(marked_inversions,mul(crossed,minor_per))
        assert marked_inversions==derivative
        assert sub(scale(per,N),H)==scale(derivative,2)
        results.append({'n':n,'permanent':per,'endpoint_derivative':derivative})
    return results

def main():
    root=Path(__file__).resolve().parent
    csv_path=Path(sys.argv[1]) if len(sys.argv)>1 else root/'counterexample_vectors_n200.csv'
    raw=csv_path.read_bytes()
    csv_hash=hashlib.sha256(raw).hexdigest()
    expected='9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25'
    assert csv_hash==expected
    with csv_path.open(newline='') as file:
        reader=csv.reader(file)
        assert next(reader)==['a_real','a_imag','b_real','b_imag']
        coords=[tuple(map(int,row)) for row in reader]
    assert len(coords)==200 and all(len(r)==4 for r in coords)
    rows=[((ar,ai),(br,bi)) for ar,ai,br,bi in coords]
    assert all(v!=(Z,Z) for v in rows)
    assert max(abs(c) for row in coords for c in row)<=20
    tests=small_tests()
    general_tests=general_matrix_tests()
    print('General complex matrix minor-identity tests passed:',len(general_tests),flush=True)
    print('Small-n direct permutation tests passed:',len(tests),flush=True)
    f,s=forms_by_deletion(rows)
    n=len(rows); N=n*(n-1)//2
    P=factorial_norm(f); Q=factorial_norm(s); D=Q-N*P
    assert P>0 and D>0
    assert 23*N*P<1000*D<24*N*P
    G=gram(rows)
    assert G[0][1]!=Z
    assert all(norm(entry)<=1600**2 for row in G for entry in row)
    diagonal=[G[i][i][0] for i in range(n)]
    assert all(G[i][i][1]==0 and 0<diagonal[i]<=1600 for i in range(n))
    # Two independent rows certify rank exactly 2, not just at most 2.
    assert determinant(rows[0],rows[1])!=Z
    certificate={
      'method':'explicit 19900 pair deletions by exact Gaussian synthetic division',
      'input_sha256':csv_hash,'n':n,'N':N,'coordinate_max_abs':20,
      'diagonal_min':min(diagonal),'diagonal_max':max(diagonal),
      'A_12':G[0][1], 'first_two_rows_determinant':determinant(rows[0],rows[1]),
      'P':str(P),'Q':str(Q),'D':str(D),'D_decimal_digits':len(str(D)),
      'strict_rational_certificate':'23*N*P < 1000*D < 24*N*P',
      'epsilon_denominator':str(4*N*math.factorial(n)*n*1601**(n-1)),
      'h_denominator':str(8*N*(N-1)*math.factorial(n)*1601**n),
      'F_coefficients':f,'S_coefficients':s,'small_permutation_tests':tests,
      'general_matrix_tests':general_tests,
    }
    coefficients=json.dumps({'F':f,'S':s},separators=(',',':')).encode()
    certificate['coefficient_sha256']=hashlib.sha256(coefficients).hexdigest()
    (root/'independent_certificate.json').write_text(json.dumps(certificate,indent=2)+'\n')
    print('Input SHA256:',csv_hash)
    print('A_12:',G[0][1], 'min/max diagonal:',min(diagonal),max(diagonal))
    print('n =',n,'N =',N)
    print('P =',P)
    print('Q =',Q)
    print('D = Q - N*P =',D)
    print('D digits =',len(str(D)))
    print('23*N*P < 1000*D < 24*N*P: PASSED')
    print('F/S coefficients SHA256:',certificate['coefficient_sha256'])
    print('All exact checks PASSED')

if __name__=='__main__': main()
