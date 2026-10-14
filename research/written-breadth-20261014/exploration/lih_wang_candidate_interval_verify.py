"""Exact independent checks of stored matrices and their full fixed-matrix t interval.
This finite-input certificate cannot prove the all-n/all-matrix Lih-Wang conjecture.
"""
from pathlib import Path
from math import factorial
from fractions import Fraction
import hashlib,json
import sympy as sp
from lih_wang_exact_verify import record
BASE=Path(__file__).parent
source=BASE/'lih-wang-transport-discovery.json';raw=json.loads(source.read_text())
x=sp.Symbol('x');half=sp.Rational(1,2)
def centered_rooks(B):
 n=len(B);d=[0]*(1<<n);d[0]=1
 for row in B:
  nd=d.copy()
  for mask,value in enumerate(d):
   if not value:continue
   for j in range(n):
    if not (mask>>j&1):nd[mask|(1<<j)]+=value*row[j]
  d=nd
 return [sum(v for mask,v in enumerate(d) if mask.bit_count()==m) for m in range(n+1)]
results=[];potential=None;negative_curvature=[]
for c in raw['best_by_case']:
 A=c['integer_matrix'];n=c['n'];K=c['K'];a=c['t_a'];b=c['t_b']
 exact=record(A,K,a,b)
 assert exact['per_integer_matrix_dp_and_ryser']==int(c['per_integer_matrix'])
 assert exact['per_mixed_integer_matrix_dp_and_ryser']==int(c['per_mixed_integer_matrix'])
 assert exact['gap_integer']==int(c['gap_integer'])
 S=sum((n*v-K)**2 for row in A for v in row);assert S==c['scaled_squared_variance']>0
 B=[[n*v-K for v in row] for row in A]
 R=centered_rooks(B);coeff=[factorial(n-m)*K**(n-m)*R[m] for m in range(n+1)]
 assert coeff[0]==factorial(n)*K**n and coeff[1]==0
 assert sum(coeff)==n**n*exact['per_integer_matrix_dp_and_ryser']
 h=[sum(coeff[j+2:]) for j in range(n-1)]
 P=sp.Poly(sum(v*x**j for j,v in enumerate(h)),x)
 value=P.eval(sp.Rational(a,b))*a*(b-a)*b**(n-2)
 assert value==exact['gap_integer']
 H0=P.eval(0);Hhalf=P.eval(half);assert H0>0
 intervals=P.intervals(eps=sp.Rational(1,2**128))
 boxes=[]
 for (lo,hi),multiplicity in intervals:
  if hi<0 or lo>half:continue
  for _ in range(256):
   ambiguous=((lo<=0<=hi and P.eval(0)!=0) or (lo<=half<=hi and P.eval(half)!=0))
   if not ambiguous:break
   lo,hi=P.refine_root(lo,hi,eps=(hi-lo)/4)
  else:raise RuntimeError('root/end-point separation was not certified')
  if hi<0 or lo>half:continue
  boxes.append((lo,hi,multiplicity))
 probes=[sp.Rational(1,8),sp.Rational(1,4),sp.Rational(3,8),half]
 cursor=sp.Rational(0)
 for lo,hi,m in boxes:
  ll=max(sp.Rational(0),lo);hh=min(half,hi)
  if cursor<ll:probes.append((cursor+ll)/2)
  cursor=max(cursor,hh)
 if cursor<half:probes.append((cursor+half)/2)
 for tt in sorted(set(probes)):
  if 0<tt<=half and P.eval(tt)<0:
   potential={'integer_matrix':A,'K':K,'a':int(tt.p),'b':int(tt.q)};break
 internal=[(lo,hi,m) for lo,hi,m in boxes if lo>0 and hi<half]
 certified=Hhalf>=0 and all(m%2==0 for lo,hi,m in internal)
 F=sp.Poly(sum(v*x**j for j,v in enumerate(coeff)),x);F2=F.diff().diff()
 for tt in [sp.Rational(1,8),sp.Rational(1,4),sp.Rational(3,8),half]:
  if F2.eval(tt)<0:negative_curvature.append({'n':n,'K':K,'t':str(tt),'raw_second_derivative':str(F2.eval(tt))})
 results.append({'n':n,'K':K,'original_sample_t':str(sp.Rational(a,b)),'cpp_values_match_two_independent_python_methods':True,'raw_chord_polynomial_coefficients_low_to_high':[str(v) for v in h],'root_count_closed_half_interval':int(P.count_roots(0,half)),'root_intervals':[{'lo':str(lo),'hi':str(hi),'multiplicity':m} for lo,hi,m in boxes],'full_fixed_matrix_interval_nonnegative_certified':bool(certified),'scope':'Only this particular actual rational matrix; no all-matrix/order theorem.'})
 if potential:break
out={'scope':'Independent exact stored-matrix verification and full-parameter sign check for finitely many actual rational matrices only. No complete Lih-Wang result.','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'matrices_checked':len(results),'all_fixed_matrix_interval_certified':all(v['full_fixed_matrix_interval_nonnegative_certified'] for v in results),'potential_witness':potential,'sampled_negative_half_interval_curvature':negative_curvature,'records':results}
path=BASE/'lih-wang-candidate-interval-verification.json';path.write_text(json.dumps(out,indent=2)+'\n')
print({'matrices_checked':len(results),'cpp_values_match_dp_and_inclusion_exclusion':True,'fixed_matrix_intervals_certified':sum(v['full_fixed_matrix_interval_nonnegative_certified'] for v in results),'potential_legal_witness':potential is not None,'sampled_negative_curvature_controls':len(negative_curvature),'full_conjecture_solved':False})
