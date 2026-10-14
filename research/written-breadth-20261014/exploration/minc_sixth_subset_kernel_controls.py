"""Exact subset-kernel and nonuniform-marginal controls, not a full Minc proof."""
from itertools import permutations,combinations
from fractions import Fraction as F
from pathlib import Path
import json,hashlib
def dp(a):
 n=len(a);d=[0]*(1<<n);d[0]=1
 for mask in range((1<<n)-1):
  i=mask.bit_count()
  for j in range(n):
   if not(mask>>j&1):d[mask|(1<<j)]+=d[mask]*a[i][j]
 return d[-1]
def ryser(a):
 n=len(a);total=0
 for mask in range(1,1<<n):
  product=1
  for row in a:product*=sum(row[j] for j in range(n) if mask>>j&1)
  total+=(-1 if (n-mask.bit_count())&1 else 1)*product
 return total if n else 1
def sub(a,I,J):return [[a[i][j] for j in J] for i in I]
n=5;k=2;A=[[int((j-i)%n in [0,1]) for j in range(n)] for i in range(n)]
C=[[1-v for v in row] for row in A];pa=dp(A);pc=dp(C)
assert pa==2 and pc==13 and ryser(A)==pa and ryser(C)==pc
P=[p for p in permutations(range(n)) if all(C[i][p[i]] for i in range(n))]
assert len(P)==pc
marg=[[F(sum(p[i]==j for p in P),pc) for j in range(n)] for i in range(n)]
assert sorted(set(v for row in marg for v in row if v))==[F(4,13),F(5,13)]
kernel_counts=[];terms=[]
for j in range(n+1):
 sets=list(combinations(range(n),j));comp={I:tuple(i for i in range(n) if i not in I) for I in sets}
 T=[[F(dp(sub(C,I,J))*dp(sub(C,comp[I],comp[J])),pc) for J in sets] for I in sets]
 assert all(sum(row)==1 for row in T)
 assert all(sum(T[i][h] for i in range(len(sets)))==1 for h in range(len(sets)))
 term=sum(dp(sub(A,I,J))*T[i][h] for i,I in enumerate(sets) for h,J in enumerate(sets))
 kernel_counts.append({'j':j,'dimension':len(sets),'exact_row_and_column_sums_one':True})
 terms.append(term)
direct=F(sum(dp([[A[i][j]+int(p[i]==j) for j in range(n)] for i in range(n)]) for p in P),pc)
assert sum(terms)==direct and terms[1]==0 and terms[0]==1 and terms[n]==pa
out={'scope':'Exact finite control of the whole-size subset-kernel formula and a real nonuniform complement-marginal example; no complete Minc-sixth theorem.','n':n,'k':k,'actual_binary_regular_matrices':True,'A':A,'C':C,'per_A_dp_and_ryser':pa,'per_C_dp_and_ryser':pc,'all_complement_permutations_enumerated':len(P),'uniform_matching_marginals':[[str(v) for v in row] for row in marg],'marginals_equal_C_divide_complement_degree':False,'nonzero_marginal_values':['4/13','5/13'],'kernel_controls':kernel_counts,'average_terms_by_A_size':[str(v) for v in terms],'direct_average_augmentation_permanent':str(direct),'all_average_identities_match':True,'full_conjecture_solved':False,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
p=Path(__file__).with_name('minc-sixth-subset-kernel-controls.json');p.write_text(json.dumps(out,indent=2)+'\n')
print({'exact_per_C':pc,'nonzero_matching_marginals':['4/13','5/13'],'all_subset_kernels_doubly_stochastic':True,'average':str(direct),'full_result':False})
