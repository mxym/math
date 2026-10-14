"""Two independent weighted-integer permanent checks for the full Lih-Wang target.
Known small controls are not new conjecture results. Rational inputs stay exact.
"""
from pathlib import Path
from math import factorial
from fractions import Fraction
import json,sys
BASE=Path(__file__).parent
def permanent_dp(a):
 n=len(a);d=[0]*(1<<n);d[0]=1
 for mask in range((1<<n)-1):
  i=mask.bit_count();value=d[mask]
  if not value:continue
  for j in range(n):
   if not (mask>>j&1):d[mask|(1<<j)]+=value*a[i][j]
 return d[-1]
def permanent_ryser(a):
 n=len(a);ans=0
 for mask in range(1<<n):
  product=1
  for row in a:product*=sum(row[j] for j in range(n) if mask>>j&1)
  ans+=(-product if (n-mask.bit_count())&1 else product)
 return ans
def record(a,K,num,den):
 n=len(a)
 assert all(isinstance(x,int) and x>=0 for row in a for x in row)
 assert all(len(row)==n and sum(row)==K for row in a)
 assert all(sum(a[i][j] for i in range(n))==K for j in range(n))
 assert 0<num<den
 C=[[num*n*x+(den-num)*K for x in row] for row in a]
 p=permanent_dp(a);p2=permanent_ryser(a);q=permanent_dp(C);q2=permanent_ryser(C)
 assert p==p2 and q==q2
 gap_integer=den**(n-1)*((den-num)*K**n*factorial(n)+num*n**n*p)-q
 gap=Fraction(gap_integer,(den*n*K)**n)
 return {'n':n,'K':K,'integer_matrix':a,'t_numerator':num,'t_denominator':den,'alpha':str(1-Fraction(num,den)),'original_domain':num*2<=den,'per_integer_matrix_dp_and_ryser':p,'per_mixed_integer_matrix_dp_and_ryser':q,'gap_integer':gap_integer,'gap_rational':str(gap),'strict_legal_counterexample':gap_integer<0 and num*2<=den}
def controls():
 I=[[2*int(i==j) for j in range(3)] for i in range(3)]
 C=[[2*int(j==(i+1)%3) for j in range(3)] for i in range(3)]
 A=[[int(i==j)+int(j==(i+1)%3) for j in range(3)] for i in range(3)]
 r=[record(I,2,1,2),record(C,2,1,2),record(A,2,1,2),record(A,2,3,4)]
 assert [x['gap_rational'] for x in r]==['1/4','1/4','0','-1/384']
 assert not any(x['strict_legal_counterexample'] for x in r)
 out={'scope':'Known exact controls and invalid shortcuts only, not a full Lih-Wang result.','known_vertex_concavity_obstruction':r[:3],'out_of_original_alpha_domain_control':r[3]}
 path=BASE/'lih-wang-exact-controls.json';path.write_text(json.dumps(out,indent=2)+'\n')
 print({'controls':4,'exact_gaps':[x['gap_rational'] for x in r],'legal_conjecture_counterexamples':0,'gap_not_concave_on_DS_polytope':True})
if __name__=='__main__':
 if len(sys.argv)>1:
  data=json.loads(Path(sys.argv[1]).read_text());w=data['potential_witness']
  if w is None:raise SystemExit('No potential witness supplied; no positive result inferred.')
  result=record(w['integer_matrix'],w['K'],w['a'],w['b'])
  if not result['strict_legal_counterexample']:raise SystemExit('Fails strict original-domain counterexample acceptance.')
  out=Path(sys.argv[1]).with_name('lih-wang-accepted-exact-counterexample.json')
  out.write_text(json.dumps(result,indent=2)+'\n');print(result)
 else:controls()
