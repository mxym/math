#!/usr/bin/env python3
"""Exact algebra diagnostics, not a verifier of the Gaussian theorem.

All arithmetic is rational. The fixed finite grids below diagnose the
normal-cone/residual normalization and local Hessian expansion. General
scalar claims have separate partial Lean proofs; analytic claims are in
paper.md and are not certified by this program.
"""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def transpose(a):
    return list(map(list, zip(*a)))


def scale(c, a):
    return [[c*x for x in row] for row in a]


def add(a, b):
    return [[x+y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def multiply(a, b):
    bt = transpose(b)
    return [[sum((x*y for x, y in zip(row, col)), F(0)) for col in bt] for row in a]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), F(0))


def determinant(a):
    out = F(0)
    for p in permutations(range(len(a))):
        inversions = sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p)))
        term = F((-1)**inversions)
        for i, j in enumerate(p):
            term *= a[i][j]
        out += term
    return out


def psd(a):
    need(a == transpose(a), 'Nonsymmetric matrix')
    for size in range(1, len(a)+1):
        for index in combinations(range(len(a)), size):
            need(determinant([[a[i][j] for j in index] for i in index]) >= 0,
                 'Negative principal minor')


Z = [[F(x) for x in row] for row in
     [(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]]
P = [[F(int(i==j))-F(1,4) for j in range(4)] for i in range(4)]
STAR = scale(F(1,3), P)


def lift(a):
    return scale(F(1,4), multiply(multiply(Z, a), transpose(Z)))


def diagonal(values):
    return [[values[i] if i==j else F(0) for j in range(3)] for i in range(3)]


def main():
    matrix_cases = 0
    need(multiply(transpose(Z), Z) == diagonal([F(4)]*3), 'Hadamard normalization')
    for mu in map(F, [F(1,4),F(1,2),1,2]):
        for ratios in product([F(0),F(1,3),F(1)], repeat=3):
            if max(ratios) != 1:
                continue
            top = [i for i in range(3) if ratios[i] == 1]
            qfaces = [diagonal([F(1,len(top)) if i in top else F(0) for i in range(3)])]
            qfaces.extend(diagonal([F(int(i==j)) for i in range(3)]) for j in top)
            if len(top) >= 2:
                i,j=top[:2]
                for off in [F(1,5),F(1,2)]:
                    a = diagonal([F(1,2) if k in (i,j) else F(0) for k in range(3)])
                    a[i][j]=a[j][i]=off
                    qfaces.append(a)
            L = lift(diagonal([mu*r for r in ratios]))
            difference = add(L, scale(-mu,P))
            psd(L)
            psd(scale(-1,difference))
            for qface in qfaces:
                Q=lift(qface)
                psd(Q)
                need(trace(Q)==1, 'Trace-one normalization')
                need(multiply(difference,Q)==[[F(0)]*4 for _ in range(4)], 'Top-eigenspace condition')
                for eps in [F(1,2),F(1,10),F(1,100)]:
                    qt=add(scale(1-eps,Q),scale(eps,STAR))
                    psd(qt)
                    need(trace(multiply(L,qt))==(1-eps)*mu+eps*trace(L)/3,'Euler identity')
                    residual=trace(multiply(multiply(difference,difference),qt))
                    spectral=eps*trace(multiply(difference,difference))/3
                    need(residual==spectral,'Residual identity')
                    need(0<=residual<=eps*mu*mu,'Residual bound')
                    matrix_cases+=1
    # Removing the top-eigenspace condition invalidates the residual identity.
    L=lift(diagonal([F(1),F(0),F(0)])); Q=lift(diagonal([F(0),F(1),F(0)]))
    A=add(L,scale(-1,P)); eps=F(1,10)
    qt=add(scale(1-eps,Q),scale(eps,STAR))
    failed_gap=trace(multiply(multiply(A,A),qt))-eps*trace(multiply(A,A))/3
    need(failed_gap==F(9,10),'Missing-KKT negative control was not detected')
    # The false Lean control has this exact rational model.
    a,b,w,tr=F(3,5),F(1),F(5,4),F(5,2)
    need(b>0 and a<b and a>b/2 and 2*(b-a)*w==b and 2*w<=tr<=3,
         'Weakened-profile countermodel failed')
    need(not (a>3*b/4),'Countermodel also satisfies the actual profile')
    local_cases=0
    for a,c in product([F(1,3),F(1),F(2)],[F(1,4),F(1,2),F(3,4)]):
        for u,v,s in product(map(F, range(-3,4)), repeat=3):
            rho=(u+v+s)/3
            left=4*a*a*sum((c*(x-(y+z)/2)-(y+z)/2)*(y+z)
                           for x,y,z in [(u,v,s),(v,u,s),(s,u,v)])
            right=-24*a*a*rho*rho-2*a*a*(3*c+1)*sum((x-rho)**2 for x in [u,v,s])
            need(left==right,'Local Hessian diagonal expansion failed')
            local_cases+=1
    margin=1-F(9,16)+F(9,16)**2/2-F(9,16)**3/6-F(9,16)
    need(margin==F(29,8192)>0,'Taylor margin')
    report={'status':'PASS','arithmetic':'Python fractions.Fraction only',
            'scope':'finite exact algebra diagnostics; not an analytic proof certificate',
            'analytic_endpoint_checked':False,'matrix_cases':matrix_cases,
            'local_identity_cases':local_cases,'negative_controls_detected':2,
            'missing_kkt_residual_gap':str(failed_gap),'profile_margin':str(margin),
            'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
