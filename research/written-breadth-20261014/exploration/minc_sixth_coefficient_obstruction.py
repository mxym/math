"""Exact checks of a shortcut obstruction, not a Minc-sixth counterexample.
The actual Jerrum family and its matching counts are credited to Wanless1999.
"""
from pathlib import Path
from collections import defaultdict
import json,hashlib
BASE=Path(__file__).parent
def graph(k,f):
 vertices=[None]+[(a,b,c) for a in range(k) for c in range(f) for b in range(k)]
 index={v:i for i,v in enumerate(vertices)};n=len(vertices);A=[[0]*n for _ in range(n)]
 for a in range(k):
  for c in range(f):
   for b in range(k):
    for beta in range(k):
     if b or beta:A[index[a,b,c]][index[a,beta,c]]=1
   if c+1<f:A[index[a,0,c]][index[a,0,c+1]]=1
  A[0][index[a,0,0]]=1;A[index[a,0,f-1]][0]=1
 assert all(sum(row)==k for row in A)
 assert all(sum(A[i][j] for i in range(n))==k for j in range(n))
 assert A[0][0]==0
 return A
def weighted_dp(A):
 d={0:1};peak=1
 for row in A:
  nd=defaultdict(int)
  for mask,value in d.items():
   for j,v in enumerate(row):
    if v and not(mask>>j&1):nd[mask|(1<<j)]+=value*v
  d=dict(nd);peak=max(peak,len(d))
 return d.get((1<<len(A))-1,0),peak
def ryser(A):
 n=len(A);s=[0]*n;total=0;prev=0
 for h in range(1,1<<n):
  mask=h^(h>>1);bit=(mask^prev).bit_length()-1;sign=1 if mask>>bit&1 else -1
  product=1
  for i,row in enumerate(A):s[i]+=sign*row[bit];product*=s[i]
  total+=(-1 if (n-mask.bit_count())&1 else 1)*product;prev=mask
 return total
records=[]
for f in [1,2,24]:
 A=graph(3,f);M=[row[1:] for row in A[1:]];pa,peak=weighted_dp(A);pm,peakm=weighted_dp(M)
 assert pa==3*2**(5*f) and pm==2**(6*f)
 if f<=2:assert ryser(A)==pa and ryser(M)==pm
 records.append({'k':3,'f':f,'n':len(A),'actual_binary_margins_checked':True,'A_st_zero':True,'per_A_actual_weighted_dp':str(pa),'per_A_without_s_t_actual_weighted_dp':str(pm),'published_closed_counts_match':True,'ryser_checked':f<=2,'max_nonzero_dp_masks':[peak,peakm]})
n=217;f=24;gap=2**f-n*(n*n+1);assert gap==6558686>0
out={'scope':'Actual-matrix strict obstruction to the stronger coefficientwise complement-average proof, not a full Minc-sixth solution or reverse total average.','credited_primary_family':'https://users.monash.edu.au/~iwanless/papers/HolDjokLAA.pdf, visual pages1-4/printed273-276','records':records,'dense_complement_edge_probability_lemma':'For any actual d-regular C with d>n/2, every supported edge has uniform perfect-matching probability at least1/[1+(n-1)^2] >1/(n^2+1).','f24_exact_integer_comparison':{'n':n,'f':f,'two_power_f':str(2**f),'n_times_n_squared_plus_one':str(n*(n*n+1)),'strict_difference':str(gap)},'conclusion':'The expected coefficient of z in per(A+zP), divided by perA, exceeds n/3 at this actual217-order3-regular A. Therefore the universal coefficientwise binomial sufficient bounds are false.','reverse_sum_average_proved':False,'reverse_global_minimum_comparison_proved':False,'new_major_result':False,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
p=BASE/'minc-sixth-coefficient-obstruction.json';p.write_text(json.dumps(out,indent=2)+'\n');print({'actual_graphs_checked':3,'largest_order':217,'max_dp_masks':max(max(r['max_nonzero_dp_masks']) for r in records),'strict_difference':gap,'full_conjecture_solved':False})
