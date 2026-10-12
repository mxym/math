"""Standalone exact certificate for Wakhare Conjecture 2, k=11, r=10.
Run from any working directory. Uses only standard-library exact integers.
It proves at least four roots; no floating-point arithmetic is used.
"""
from math import comb
from fractions import Fraction
from pathlib import Path
import json

P=[1,352705,60632419,1227099358,6330005947,10701243741,
   6330005947,1227099358,60632419,352705,1]
Q=[11,1939817,289126442,5380098482,25959010187,41238382790,
   22851341183,4098130058,181139618,831413,-1]

# Reconstruct both coefficient lists directly from equation (1.3).
def original_coefficients(r):
    return [sum((Fraction((-1)**(j-v),v+1)*comb(r*v+11,11)*comb(11,j-v)
                 for v in range(j+1)),Fraction()) for j in range(11)]
assert original_coefficients(11)==[Fraction(v) for v in P]
assert original_coefficients(10)==[Fraction(v,11) for v in Q]

# alpha^10(1+alpha)=1 has a unique positive solution.
# The two exact integer signs isolate it in (117/125,937/1000).
alpha_low_numerator=117**10*242-125**11
alpha_high_numerator=937**10*1937-1000**11
assert alpha_low_numerator==-90074807210933370467 < 0
assert alpha_high_numerator==10474898608767871728104442364513 > 0

# Homogeneous evaluation of an ascending-coefficient degree-10 polynomial.
def hom(c,a,b):
    return sum(c[j]*a**j*b**(10-j) for j in range(11))

# Exact bounds on R=B/A, where p(x)=A(x)(alpha-R(x)).
# At a/b, R=N/D as below. All N,D are positive.
# bounds: R<919/1000, R>1131/1000, R<935/1000,
#         R>938/1000, R<928/1000.
checks=[(1,5,919,-1),(2,5,1131,1),(3,5,935,-1),
        (2,3,938,1),(4,5,928,-1)]
rows=[]
for a,b,u,direction in checks:
    pp=hom(P,a**11,b**11)
    qq=hom(Q,a**10,b**10)
    N=10*(b**11-a**11)**11*qq
    D=121*b*(b**10-a**10)**11*pp
    assert N>0 and D>0
    residual=direction*(1000*N-u*D)
    assert residual>0
    if direction<0:
        assert Fraction(u,1000)<Fraction(117,125)
        p_sign=1
    else:
        assert Fraction(u,1000)>Fraction(937,1000)
        p_sign=-1
    rows.append({'x':f'{a}/{b}','ratio_bound':('<' if direction<0 else '>')+f'{u}/1000',
                 'p_sign':p_sign,'N':str(N),'D':str(D),'positive_residual':str(residual)})
assert [x['p_sign'] for x in rows]==[1,-1,1,-1,1]
assert all(Fraction(checks[i][0],checks[i][1])<Fraction(checks[i+1][0],checks[i+1][1]) for i in range(4))

out={'source':'Wakhare, Iterated Entropy Derivatives and Binary Entropy Inequalities, Conjecture 2',
     'arxiv':'https://arxiv.org/abs/2312.14743v2','doi':'https://doi.org/10.1016/j.jat.2025.106143',
     'k':11,'r':10,'alpha_interval':['117/125','937/1000'],
     'alpha_lower_comparison':str(alpha_low_numerator),'alpha_upper_comparison':str(alpha_high_numerator),
     'P_ascending':P,'Q_ascending':Q,'samples':rows,
     'conclusion':'At least four distinct roots in (1/5,2/5), (2/5,3/5), (3/5,2/3), (2/3,4/5).'}
path=Path(__file__).with_name('small_exact_certificate.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print('PASS: source coefficients, alpha interval, and all five strict rational signs verified.')
print('PASS: p_{11,10} has at least four distinct roots in (0,1).')
print('Certificate:',path)
