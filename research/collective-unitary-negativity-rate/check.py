#!/usr/bin/env python3
"""Exact ancillary checks for the collective-unitary negativity rate.

Standard library only; no floats, optimizer, native proof evaluation, or assertions.
These finite/algebraic checks do NOT certify the external matrix Bernstein theorem
or substitute for the arbitrary-dimension analytic proof in PROOF.md.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial
from pathlib import Path
import hashlib
import json

class CheckFailed(RuntimeError):
    pass

def require(condition: bool, description: str) -> None:
    if not condition:
        raise CheckFailed(description)

class Cyclotomic:
    """Exact Q[x]/Phi_a(x), for the explicitly checked small orders."""
    POLYS = {2: (1, 1), 3: (1, 1, 1), 4: (1, 0, 1), 5: (1, 1, 1, 1, 1)}
    def __init__(self, order: int):
        self.order = order
        self.poly = self.POLYS[order]
        self.degree = len(self.poly)-1
        self.zero = (Q(0),)*self.degree
        self.one = (Q(1),)+(Q(0),)*(self.degree-1)
        self.x = self.reduce((0, 1))
    def reduce(self, values):
        v = list(map(Q, values))
        v += [Q(0)]*max(0, self.degree-len(v))
        for k in range(len(v)-1, self.degree-1, -1):
            c = v[k]
            if c:
                for j in range(self.degree):
                    v[k-self.degree+j] -= c*self.poly[j]
        return tuple(v[:self.degree])
    @lru_cache(maxsize=None)
    def add(self, x, y):
        return tuple(a+b for a,b in zip(x,y))
    @lru_cache(maxsize=None)
    def mul(self, x, y):
        v = [Q(0)]*(2*self.degree-1)
        for i,a in enumerate(x):
            for j,b in enumerate(y):
                v[i+j] += a*b
        return self.reduce(v)
    def scale(self, c, x):
        return tuple(Q(c)*a for a in x)
    @lru_cache(maxsize=None)
    def phase(self, exponent: int):
        result = self.one
        for _ in range(exponent % self.order):
            result = self.mul(result, self.x)
        return result
    @lru_cache(maxsize=None)
    def conj(self, value):
        result = self.zero
        for i,c in enumerate(value):
            result = self.add(result, self.scale(c, self.phase(-i)))
        return result
    def sum(self, values):
        result = self.zero
        for v in values:
            result = self.add(result,v)
        return result

# Sparse matrix keys are actual product-basis row/column indices.
def matrix_add(F, *matrices):
    out = {}
    for M in matrices:
        for ij,c in M.items():
            out[ij] = F.add(out.get(ij,F.zero),c)
    return {ij:c for ij,c in out.items() if c != F.zero}

def matrix_mul(F, A, B):
    byrow = defaultdict(list)
    for (j,k),v in B.items():
        byrow[j].append((k,v))
    out = {}
    for (i,j),x in A.items():
        for k,y in byrow[j]:
            out[i,k] = F.add(out.get((i,k),F.zero),F.mul(x,y))
    return {ij:c for ij,c in out.items() if c != F.zero}

def partial_transpose(M, b):
    return {(i*b+l,k*b+j):c
            for (row,col),c in M.items()
            for i,j in [divmod(row,b)] for k,l in [divmod(col,b)]}

def adjoint(F,M):
    return {(j,i):F.conj(c) for (i,j),c in M.items()}

def verify_bell_case(a: int, b: int, mutation: str | None = None) -> dict:
    F=Cyclotomic(a); J=b//a; N0=a*a*J
    require(F.phase(a)==F.one,'root order')
    for frequency in range(1,a):
        require(F.sum(F.phase(frequency*t) for t in range(a))==F.zero,
                'nontrivial Fourier sum')
    vectors=[]; projectors=[]; transposes=[]; squares=[]
    for j,u,v in product(range(J),range(a),range(a)):
        multiplier = 0 if mutation=='constant_phase' else 1
        vector={t*b+j*a+(t+v)%a:F.phase(multiplier*u*t) for t in range(a)}
        vectors.append(vector)
        P={(i,k):F.scale(Q(1,a),F.mul(x,F.conj(y)))
           for i,x in vector.items() for k,y in vector.items()}
        W = P if mutation=='identity_transpose' else partial_transpose(P,b)
        block={((i*b+j*a+t),(i*b+j*a+t)):F.scale(Q(1,a*a),F.one)
               for i,t in product(range(a),range(a))}
        require(adjoint(F,P)==P,'Hermitian Bell projector')
        require(matrix_mul(F,P,P)==P,'idempotent Bell projector')
        require(F.sum(c for (i,k),c in P.items() if i==k)==F.one,'trace-one Bell projector')
        require(adjoint(F,W)==W,'Hermitian partial transpose')
        require(partial_transpose(W,b)==P,'partial-transpose involution')
        require(matrix_mul(F,W,W)==block,'Bell partial-transpose square identity')
        projectors.append(P);transposes.append(W);squares.append(matrix_mul(F,W,W))
    for i,x in enumerate(vectors):
        for j,y in enumerate(vectors):
            inner=F.sum(F.mul(F.conj(c),y.get(k,F.zero)) for k,c in x.items())
            require(inner==(F.scale(a,F.one) if i==j else F.zero),'Bell orthogonality')
    I0={(i*b+t,i*b+t):F.one for i in range(a) for t in range(a*J)}
    require(matrix_add(F,*projectors)==I0,'Bell resolution of coordinate identity')
    require(matrix_add(F,*transposes)==I0,'sum of partial transposes')
    target = ({ij:F.scale(Q(1,a),c) for ij,c in I0.items()}
              if mutation=='wrong_covariance' else I0)
    require(matrix_add(F,*squares)==target,'sum-of-squares covariance identity')
    return {'a':a,'b':b,'ambient_dimension':a*b,'block_dimension':N0,
            'bell_vectors':len(vectors),'orthogonality_pairs':len(vectors)**2}

# Two-variable polynomial arithmetic independently expands the Bernstein constant.
def padd(*ps):
    out={}
    for p in ps:
        for m,c in p.items():out[m]=out.get(m,Q(0))+c
    return {m:c for m,c in out.items() if c}
def pscale(c,p):return {m:Q(c)*v for m,v in p.items() if c*v}
def pmul(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            key=tuple(a+b for a,b in zip(m,n))
            out[key]=out.get(key,Q(0))+c*d
    return {m:c for m,c in out.items() if c}

def verify_scalar(mutate=False):
    x={(1,0):Q(1)};y={(0,1):Q(1)}
    t=padd(pscale(2,x),pscale(2,y))
    # L*p0=x^2 and L*t/(3*a)=t*y/3.
    actual=padd(pmul(t,t),pscale(-2,pmul(x,x)),pscale(Q(-2,3),pmul(t,y)))
    expected={(2,0):Q(2),(1,1):Q(20,3),(0,2):Q(8,3)}
    if mutate:expected[(1,1)]+=1
    require(actual==expected,'Bernstein exponent certificate')
    require(all(c>0 for c in actual.values()),'positive Bernstein coefficients')
    require(Q(4,9)+Q(1,4)==Q(25,36)<1,'joint event probability bound')
    require(Q(3,2)**2>2 and 6*Q(3,2)+2<12,'dimension-independent norm constant')
    dimensions=0
    for a in range(2,25):
        for b in range(a,4*a+3):
            N=a*b;N0=a*a*(b//a)
            require(N<=2*N0 and N0<=N,'coordinate support dimension ratio')
            for r in range(1,N+1):
                if 8*r>N0:
                    require(Q(N,r)<16,'large-r envelope bound')
            dimensions+=1
    require(Q(3,11)**2+8*Q(1,11)**2==Q(17,121),'qutrit example purity')
    require(9*Q(17,121)==Q(153,121)>1,'qutrit activation factor')
    return {'bernstein_coefficients':{str(m):str(c) for m,c in actual.items()},
            'dimension_pairs':dimensions,'union_failure_bound':'25/36',
            'balanced_qutrit_factor':'153/121'}

def compositions(k,s):
    if s==1:
        yield (k,);return
    for first in range(k+1):
        for rest in compositions(k-first,s-1):yield (first,)+rest

def multinomial(counts):
    value=factorial(sum(counts))
    for n in counts:value//=factorial(n)
    return value

def verify_types():
    examples=0;word_types=0
    for s in range(1,5):
        for k in range(1,9):
            for c in compositions(k,s):
                size=multinomial(c)
                denominator=1
                for n in c:denominator*=n**n # Python 0**0=1, the intended convention.
                entropy_power=Q(k**k,denominator)
                require(size<=entropy_power<=size*(k+1)**s,'exact type size bounds')
                examples+=1
    # Independent word enumeration, rather than reuse of factorial arithmetic.
    for s in (2,3):
        for k in range(1,8):
            counts=Counter(tuple(word.count(i) for i in range(s)) for word in product(range(s),repeat=k))
            for c,observed in counts.items():
                require(observed==multinomial(c),'independent type cardinality')
                word_types+=1
    # A type is a mode under its own empirical distribution.
    modes=0
    for c in compositions(7,3):
        q=[Q(n,7) for n in c]
        own=Q(multinomial(c))
        for p,n in zip(q,c):own*=p**n
        for h in compositions(7,3):
            other=Q(multinomial(h))
            for p,n in zip(q,h):other*=p**n
            require(other<=own,'empirical multinomial type is a mode');modes+=1
    return {'exact_type_bounds':examples,'enumerated_types':word_types,'mode_comparisons':modes}

def verify_escort_algebra():
    # Variables are alpha, A, B, ell, z. Differentiate h in the paper;
    # these checks certify its exact algebraic matching, not calculus itself.
    def var(i):return {tuple(int(j==i) for j in range(5)):Q(1)}
    one={(0,)*5:Q(1)}
    a,A,B,ell,z=[var(i) for i in range(5)]
    H=padd(pscale(-1,pmul(a,ell)),z)
    KL=padd(pmul(padd(a,pscale(-1,one)),ell),pscale(-1,z))
    require(padd(H,KL,ell)=={},'entropy-relative-entropy identity')
    numerator=padd(A,pmul(padd(a,pscale(-1,one)),B),z)
    # alpha*N' - N = (B-A)-H, with z'=ell.
    derivative=padd(pmul(a,padd(B,ell)),pscale(-1,numerator))
    require(derivative==padd(B,pscale(-1,A),pscale(-1,H)),'escort derivative numerator')
    # At delta=H, B=A+H and the rate is A-D(q||p).
    boundary_num=padd(A,pmul(padd(a,pscale(-1,one)),padd(A,H)),z)
    require(pmul(a,padd(A,pscale(-1,KL)))==boundary_num,'interior escort matching')
    # At alpha=2, H=-2*ell+z and KL=ell-z.
    H2=padd(pscale(-2,ell),z);D2=padd(ell,pscale(-1,z))
    g2=padd(pscale(Q(1,2),padd(A,B,pscale(-1,H2))),pscale(-1,D2))
    require(g2==pscale(Q(1,2),padd(A,B,z)),'collision endpoint matching')
    return {'exact_identities':4}

def rejected(label,job):
    try:job()
    except CheckFailed as e:return {'name':label,'rejected':True,'reason':str(e)}
    raise CheckFailed('Corrupted control was accepted: '+label)

def run_checks():
    bell=[]
    for a in (2,3,4):
        for b in (a,a+1,2*a+1):bell.append(verify_bell_case(a,b))
    bell.append(verify_bell_case(5,5))
    scalar=verify_scalar();types=verify_types();escort=verify_escort_algebra()
    controls=[rejected('constant Bell phase',lambda:verify_bell_case(3,3,'constant_phase')),
              rejected('identity instead of partial transpose',lambda:verify_bell_case(2,3,'identity_transpose')),
              rejected('wrong matrix variance factor',lambda:verify_bell_case(3,3,'wrong_covariance')),
              rejected('altered Bernstein coefficient',lambda:verify_scalar(True))]
    return {'status':'PASS','scope':'Exact finite Bell/covariance identities, rational inequalities, type cardinalities, and escort algebra only; not a Lean or full analytic-proof certificate',
            'bell_cases':bell,'scalar_checks':scalar,'type_checks':types,'escort_algebra':escort,
            'negative_controls':controls,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--report',type=Path);ap.add_argument('--self-test',action='store_true')
    args=ap.parse_args();report=run_checks()
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
