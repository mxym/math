#!/usr/bin/env python3
"""Exact rational-polynomial check of explicit dyadic cofactor Rayleigh formulas.
No roots, matrix eigenvalues, or floating-point arithmetic are needed.
"""
import math,json,hashlib,argparse,sys
from pathlib import Path
if not __debug__:raise SystemExit('Optimized Python is not allowed.')
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def verify(K,C):
 assert K>=1 and C>4
 M=2**K;n=2*M;p=[1]
 for k in range(K):
  d=2**k;den=(C*d)**d;num=(M-1)**d
  assert len(p)==d
  p=[den*x for x in p]+[num*x for x in p]
 assert len(p)==M
 D=p[0]
 # Coefficient domination c_j <= (4/C)^j binom(M-1,j), cross-multiplied.
 for j,c in enumerate(p):assert c*C**j<=D*4**j*math.comb(M-1,j)
 fac=[math.factorial(i) for i in range(n+1)]
 pn=sum(c*c*fac[2*j]*fac[n-2*j] for j,c in enumerate(p))
 assert (C*C-16)*pn<C*C*fac[n]*D*D
 s0=[2*(M-1)*(K-j.bit_count())*c for j,c in enumerate(p)]
 sr=[s0[j]+(2*C*(j+1)*p[j+1] if j+1<M else 0) for j in range(M)]
 zn=sum(c*c*fac[2*j]*fac[n-2-2*j] for j,c in enumerate(s0[:-1]))
 rn=sum(c*c*fac[2*j]*fac[n-2-2*j] for j,c in enumerate(sr[:-1]))
 assert s0[-1]==sr[-1]==0
 znum=n*zn;zden=2*C*K*(M-1)*pn
 rnum=n*rn;rden=4*C*(M-1)*(K+1)*pn
 # The exact finite lower bounds proved by retaining one Fock coefficient.
 assert znum*C**3*M>=zden*(C*C-16)*K*(M-1)
 assert rnum*2*C**3*M>=rden*(C*C-16)*(K+1)*(M-1)
 # Return thousandth intervals with exact division.
 zlo=1000*znum//zden;rlo=1000*rnum//rden
 assert zlo*zden<1000*znum<(zlo+1)*zden
 assert rlo*rden<1000*rnum<(rlo+1)*rden
 vals=[pn,znum,zden,rnum,rden]
 dig=hashlib.sha256(('\n'.join(map(str,vals))+'\n').encode()).hexdigest()
 full={'scaled_polynomial_fock_norm':str(pn),'complex_numerator':str(znum),'complex_denominator':str(zden),'real_numerator':str(rnum),'real_denominator':str(rden)}
 Path(__file__).with_name(f'DYADIC_EXACT_VALUES_K{K}_C{C}.json').write_text(json.dumps(full,sort_keys=True,indent=2)+'\n')
 return {'K':K,'C':C,'n':n,'complex_rayleigh_millibounds':[zlo,zlo+1],'real_rayleigh_millibounds':[rlo,rlo+1],'scaled_exact_values_sha256':dig,'coefficient_bound_verified':True,'fock_norm_bound_verified':True,'finite_lower_bounds_verified':True,'arithmetic':'Python integers only'}

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--K',type=int,default=8);a.add_argument('--C',type=int,default=7);q=a.parse_args()
 ans=verify(q.K,q.C);s=json.dumps(ans,indent=2)+'\n'
 print(s,end='');Path(__file__).with_name(f'DYADIC_EXACT_K{q.K}_C{q.C}.json').write_text(s)
