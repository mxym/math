#!/usr/bin/env python3
"""Exact low-dimensional pure ECQC counterexamples and full-Schmidt-rank witness.

Standard library only; rational cyclotomic arithmetic, literal density matrices,
Born probabilities, spectral identities, and symbolic prime-log entropies.
All logarithmic identities used by the checker are proved in paper.tex.
Copyright (c) 2026 Yongxian Zhang. All rights reserved.
"""
from fractions import Fraction as Q
import json

if not __debug__:
    raise RuntimeError('Assertions are required; do not run with python -O.')

class Cyclotomic:
    """Q[z]/(1+z+...+z^(p-1)), used only for p=3 or p=5."""
    def __init__(self, p):
        assert p in (3, 5)
        self.p = p
        self.zero = (Q(0),)*(p-1)
        self.one = self.scalar(1)
    def scalar(self, x):
        return (Q(x),) + (Q(0),)*(self.p-2)
    def add(self, a, b):
        return tuple(x+y for x,y in zip(a,b))
    def scale(self, a, q):
        return tuple(x*q for x in a)
    def mul(self, a, b):
        p=self.p
        v=[Q(0)]*(2*p-3)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                v[i+j]+=x*y
        for k in range(len(v)-1,p-2,-1):
            for j in range(1,p):
                v[k-j]-=v[k]
        return tuple(v[:p-1])
    def zpow(self, k):
        k%=self.p
        if k==self.p-1:
            return (Q(-1),)*(self.p-1)
        return tuple(Q(int(k==j)) for j in range(self.p-1))
    def conj(self, a):
        return self.sum(self.scale(self.zpow(-k),v) for k,v in enumerate(a))
    def sum(self, xs):
        v=self.zero
        for x in xs:v=self.add(v,x)
        return v
    def inner(self, a, b):
        return self.sum(self.mul(self.conj(x),y) for x,y in zip(a,b))

def mmul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]

def shift(a,q):
    return [[x-(q if i==j else 0) for j,x in enumerate(row)] for i,row in enumerate(a)]

def prime_factors(n):
    assert isinstance(n,int) and n>=1
    out={};p=2
    while p*p<=n:
        while n%p==0:
            out[p]=out.get(p,0)+1;n//=p
        p+=1
    if n>1:out[n]=out.get(n,0)+1
    return out

def addlog(a,b,c=Q(1)):
    out=dict(a)
    for p,v in b.items():out[p]=out.get(p,Q(0))+c*v
    return {p:v for p,v in out.items() if v}

def entropy(vs):
    """Exact expression sum_p c_p log(p), by the rational logarithm laws."""
    assert sum(vs)==1 and all(v>=0 for v in vs)
    out={}
    for v in vs:
        if not v:continue
        v=Q(v)
        for p,k in prime_factors(v.numerator).items():
            out[p]=out.get(p,Q(0))-v*k
        for p,k in prime_factors(v.denominator).items():
            out[p]=out.get(p,Q(0))+v*k
    return {p:v for p,v in out.items() if v}

def mi(table):
    rows=[sum(row) for row in table]
    cols=[sum(row[j] for row in table) for j in range(len(table[0]))]
    return addlog(addlog(entropy(rows),entropy(cols)),entropy([x for row in table for x in row]),-1)

def check_bases(p):
    f=Cyclotomic(p)
    bases=[[[f.scalar(int(x==j)) for x in range(p)] for j in range(p)]]
    norms=[1]
    for a in range(p):
        bases.append([[f.zpow(a*x*x+j*x) for x in range(p)] for j in range(p)])
        norms.append(p)
    count=0
    for r in range(p+1):
        for s in range(p+1):
            for j in range(p):
                for k in range(p):
                    v=f.inner(bases[r][j],bases[s][k])
                    expected=Q(norms[r]*norms[s],p) if r!=s else Q(norms[r]*norms[s]*int(j==k))
                    assert f.mul(v,f.conj(v))==f.scalar(expected)
                    count+=1
    return f,bases,norms,count

def check_state(p,W,expected_numerators,expected_denominator,spectrum,name):
    f,bases,norms,overlaps=check_bases(p)
    N=sum(x*x for row in W for x in row)
    w=[x for row in W for x in row]
    rho=[[Q(x*y,N) for y in w] for x in w]
    assert mmul(rho,rho)==rho and sum(rho[i][i] for i in range(p*p))==1
    assert all(rho[i][j]==rho[j][i] for i in range(p*p) for j in range(p*p))
    # Hermitian idempotent of trace one has eigenvalues 1,0,...,0, hence is PSD.
    ra=[[sum(rho[x*p+y][z*p+y] for y in range(p)) for z in range(p)] for x in range(p)]
    rb=[[sum(rho[x*p+y][x*p+z] for x in range(p)) for z in range(p)] for y in range(p)]
    assert ra==rb
    for reduced in [ra,rb]:
        assert sum(reduced[i][i] for i in range(p))==1
        if spectrum==[Q(1,2),Q(1,2)]+[Q(0)]*(p-2):
            twice=[[2*x for x in row] for row in reduced]
            assert mmul(twice,twice)==twice
            # Eigenvalues are 0 or 1/2, with multiplicity two for 1/2 by trace.
        else:
            assert p==3 and spectrum==[Q(25,52),Q(25,52),Q(1,26)]
            a,b=Q(25,52),Q(1,26)
            assert mmul(shift(reduced,a),shift(reduced,b))==[[0]*p for _ in range(p)]
            assert 2*a+b==1 and a!=b
            # Hermiticity and the annihilating polynomial force these eigenvalues;
            # the trace forces the larger root to have multiplicity two.
    expected=[[Q(x,expected_denominator) for x in row] for row in expected_numerators]
    for basis,norm in zip(bases,norms):
        for j in range(p):
            for k in range(p):
                amplitude=f.sum(f.scale(f.mul(f.conj(basis[j][x]),f.conj(basis[k][y])),W[x][y])
                                for x in range(p) for y in range(p))
                prob=f.scale(f.mul(amplitude,f.conj(amplitude)),Q(1,N*norm*norm))
                assert prob==f.scalar(expected[j][k])
    # Every setting has this same table, so the ECQC minimization discards
    # any one of the p+1 identical mutual informations, retaining exactly p.
    measured=mi(expected)
    quantum=addlog({},entropy(spectrum),Q(2))
    gap=addlog(addlog({},measured,Q(p)),quantum,Q(-1))
    if name=='full_Schmidt_rank_qutrit':
        assert gap=={2:Q(57,26),5:Q(100,26),13:Q(1),3:-Q(243,26)}
        numerator=2**57*5**100*13**26
        denominator=3**243
        assert numerator>denominator>0
        positivity={'identity':'gap = log(2^57 * 5^100 * 13^26 / 3^243) / 26',
                    'positive_integer_difference':str(numerator-denominator)}
    else:
        assert measured=={2:Q(1)} and quantum=={2:Q(2)}
        assert gap=={2:Q(p-2)}
        positivity={'identity':f'gap = {p-2} log(2) > 0'}
    return {'name':name,'dimension':p,'integer_amplitude_matrix':W,'squared_normalization':N,
            'density_shape':[p*p,p*p],'ordered_MUB_overlaps_checked':overlaps,
            'Born_probabilities_checked':(p+1)*p*p,
            'marginal_spectrum':[str(x) for x in spectrum],
            'common_Born_table':[[str(x) for x in row] for row in expected],
            'single_setting_information_prime_log_coefficients':{str(k):str(v) for k,v in measured.items()},
            'quantum_information_prime_log_coefficients':{str(k):str(v) for k,v in quantum.items()},
            'positive_gap_certificate':positivity}

def run():
    W3=[[0,1,1],[-1,0,0],[-1,0,0]]
    P3=[[0,1,1],[1,0,0],[1,0,0]]
    W5=[[0]*5 for _ in range(5)]
    for i,j,v in [(1,2,1),(1,3,-1),(4,2,-1),(4,3,1),(2,1,-1),(2,4,1),(3,1,1),(3,4,-1)]:
        W5[i][j]=v
    P5=[[abs(x) for x in row] for row in W5]
    full=[[0,5,5],[-5,1,-1],[-5,-1,1]]
    Pfull=[[0,25,25],[25,1,1],[25,1,1]]
    records=[check_state(3,W3,P3,4,[Q(1,2),Q(1,2),Q(0)],'qutrit_singlet'),
             check_state(5,W5,P5,8,[Q(1,2),Q(1,2),Q(0),Q(0),Q(0)],'ququint_singlet'),
             check_state(3,full,Pfull,104,[Q(25,52),Q(25,52),Q(1,26)],'full_Schmidt_rank_qutrit')]
    return {'status':'PASS','arithmetic':'exact Fraction cyclotomic and integer arithmetic; symbolic prime-log expressions',
            'records':records,
            'scope':'Finite quantum objects and algebraic entropy identities. The spectral theorem, logarithm laws, and universal Holevo upper bound are justified in the written proof; this is not a Lean kernel proof.'}

if __name__=='__main__':print(json.dumps(run(),indent=2))
