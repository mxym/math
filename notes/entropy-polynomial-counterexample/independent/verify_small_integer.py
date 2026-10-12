#!/usr/bin/env python3
"""Fresh integer-only direct-formula audit of the (k,r)=(11,10) instance.
Python 3.11+, standard library only; no imported certificate or other verifier.
"""
from math import comb,lcm,gcd
from pathlib import Path
import json
K,R=11,10
L=lcm(*range(1,K+1))

def C(s):
    return [sum((1 if (j-v)%2==0 else -1)*(L//(v+1))*comb(s*v+K,K)*comb(K,j-v)
                for v in range(j+1)) for j in range(K)]

def H(s,c,a,b):
    return sum(c[j]*(a**(s*j))*(b**(s*(K-1-j))) for j in range(K))

ck,cr=C(K),C(R)
points=[(1,5),(2,5),(3,5),(2,3),(4,5)]
expected=[1,-1,1,-1,1]
rows=[]
for (a,b),wanted in zip(points,expected):
    # Multiplication by positive L*b^(K*K+K*R-R) clears all denominators.
    A=K*b**(K-R)*(b**R-a**R)**K*H(K,ck,a,b)
    B=R*(b**K-a**K)**K*H(R,cr,a,b)
    assert A>0 and B>0
    g=gcd(A,B)
    A//=g; B//=g
    D=A**K-B**R*(A+B)**(K-R)
    got=(D>0)-(D<0)
    assert got==wanted
    n=1000*B//A
    assert n*A<1000*B<(n+1)*A
    rows.append({'x':[a,b],'A':str(A),'B':str(B),'D':str(D),'sign':got,
                 'ratio_interval':[[n,1000],[n+1,1000]],
                 'lower_residual':str(1000*B-n*A),'upper_residual':str((n+1)*A-1000*B)})
# alpha^10(1+alpha)=1. Unique root in (0,1) lies in (936/1000,937/1000).
alpha_lo=936**10*(1000+936)-1000**11
alpha_hi=937**10*(1000+937)-1000**11
assert alpha_lo<0<alpha_hi
for z in rows:
    if z['sign']>0: assert z['ratio_interval'][1][0]<936
    else: assert z['ratio_interval'][0][0]>937
assert all(a*d<c*b for (a,b),(c,d) in zip(points,points[1:]))
cert={'k':K,'r':R,'L':L,'coefficients_k_scaled':ck,'coefficients_r_scaled':cr,
      'common_denominator_power':K*K+K*R-R,'points':rows,
      'alpha_interval':[[936,1000],[937,1000]],
      'alpha_residual_low':str(alpha_lo),'alpha_residual_high':str(alpha_hi),
      'conclusion':'At least four distinct roots in (0,1), contradicting Conjecture 2.'}
Path(__file__).with_name('small_integer_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
print('L =',L)
print('scaled coefficients k =',ck)
print('scaled coefficients r =',cr)
print('alpha residuals:',alpha_lo,alpha_hi)
for z in rows:
 print('x=',z['x'],'sign=',z['sign'],'ratio interval=',z['ratio_interval'])
print('PASS: exact signs + - + - +, at least four distinct roots in (0,1).')
