#!/usr/bin/env python3
"""Independent integer-only check of Wakhare arXiv:2312.14743v2 (1.3)-(1.4).
Does not use derivative recurrences, root solvers, or any other verifier output.
Every operation used to establish a sign is an exact Python integer operation.
"""
from math import comb, lcm, gcd
import json
from pathlib import Path
import sys
sys.set_int_max_str_digits(0)
K, R = 20, 19
L = lcm(*range(1,K+1))

def coefficients(s):
    return [sum((-1)**(j-v) * (L//(v+1)) * comb(s*v+K,K) * comb(K,j-v)
                for v in range(j+1)) for j in range(K)]

def homogeneous_h(c,s,a,b):
    # Equals L*b^(s*(K-1))*h_{K,s}(a/b).
    return sum(c[j]*a**(s*j)*b**(s*(K-1-j)) for j in range(K))

def sgn(n):
    return (n>0)-(n<0)

c20,c19 = coefficients(K), coefficients(R)
points = [(1,5),(2,5),(11,20),(13,20),(3,4)]
rows=[]
# A common positive denominator for p(a/b) is L*b^761.
# The two numerators below are computed directly from equations (1.3),(1.4).
for a,b in points:
    assert 0<a<b and gcd(a,b)==1
    H20=homogeneous_h(c20,20,a,b)
    H19=homogeneous_h(c19,19,a,b)
    A=20*b*(b**19-a**19)**20*H20
    B=19*(b**20-a**20)**20*H19
    assert A>0 and B>0
    g=gcd(A,B)
    A//=g; B//=g
    # f(t)=t^19(1+t) strictly increases for t>0.
    # f(alpha)=1, f(B/A)=B^19(A+B)/A^20.
    # Thus sign(alpha*A-B)=sign(A^20-B^19(A+B)).
    D=A**20-B**19*(A+B)
    assert D != 0
    rows.append({'x':[a,b], 'A':str(A),'B':str(B), 'sign_D':sgn(D),
                 'D':str(D), 'denominator_power_before_gcd':761,
                 'gcd_removed':str(g)})
assert [row['sign_D'] for row in rows]==[1,-1,1,-1,1]
assert all(a*d<c*b for (a,b),(c,d) in zip(points,points[1:]))
certificate={'k':K,'r':R,'L':L,'coefficient_numerators_20':c20,
             'coefficient_numerators_19':c19,'points':rows,
             'verified_signs':[row['sign_D'] for row in rows],
             'conclusion':'At least four distinct roots in (0,1), by the intermediate value theorem.'}
out=Path(__file__).with_name('integer_certificate.json')
out.write_text(json.dumps(certificate,indent=2)+'\n')
print('L =',L)
print('h20 coefficients (numerator / L):',c20)
print('h19 coefficients (numerator / L):',c19)
print('x; sign; digits(A); digits(B); digits(abs(D))')
for z in rows:
    print(z['x'], z['sign_D'],len(z['A']),len(z['B']),len(z['D'].lstrip('-')))
print('PASS: signs + - + - +; at least four distinct open-interval roots.')
print('Wrote',out)

# A second, compact exact rational certificate for human inspection.
# These are proven rational bounds, not floating point approximations.
Q=1000
alpha_low,alpha_high=965,966
alpha_low_residual=alpha_low**19*(Q+alpha_low)-Q**20
alpha_high_residual=alpha_high**19*(Q+alpha_high)-Q**20
assert alpha_low_residual<0<alpha_high_residual
expected_ratio_lows=[951,1187,924,979,962]
compact=[]
for z,n in zip(rows,expected_ratio_lows):
    A,B=int(z['A']),int(z['B'])
    lower_residual=Q*B-n*A
    upper_residual=(n+1)*A-Q*B
    assert lower_residual>0 and upper_residual>0
    if z['sign_D']>0:
        assert n+1<alpha_low
    else:
        assert n>alpha_high
    compact.append({'x':z['x'],'ratio_lower_numerator':n,'ratio_upper_numerator':n+1,
                    'ratio_denominator':Q,'lower_residual':str(lower_residual),
                    'upper_residual':str(upper_residual),'sign':z['sign_D']})
Path(__file__).with_name('compact_certificate.json').write_text(json.dumps({
    'alpha_interval':{'lower':[alpha_low,Q],'upper':[alpha_high,Q],
                      'lower_residual':str(alpha_low_residual),
                      'upper_residual':str(alpha_high_residual)},
    'ratio_intervals':compact},indent=2)+'\n')
print('PASS: independent compact rational-interval presentation of the same signs.')
