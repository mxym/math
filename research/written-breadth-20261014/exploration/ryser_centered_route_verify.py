"""Independent exact checks of the centered route and invalid fractional descent.
No full Ryser solution or legal negative witness is asserted.
"""
from pathlib import Path
from fractions import Fraction
from math import factorial
import json,hashlib
from ryser_baseline_verify import matching_dp,ryser
BASE=Path(__file__).parent
n=13;k=4;lam=1
saved=json.loads((BASE/'ryser-rook-comparison.json').read_text())
centered=json.loads((BASE/'ryser-centered-rook-diagnostic.json').read_text())
def weighted_rooks(a):
 d=[0]*(1<<n);d[0]=1
 for row in a:
  nd=d.copy()
  for mask,value in enumerate(d):
   if not value:continue
   bits=((1<<n)-1)^mask
   while bits:
    bit=bits&-bits;bits-=bit;j=bit.bit_length()-1
    nd[mask|bit]+=value*row[j]
  d=nd
 return [sum(value for mask,value in enumerate(d) if mask.bit_count()==m) for m in range(n+1)]
records=[]
for name,key,expect in [('plane','plane_rows',3852),('nonconfiguration','nonconfiguration_rows',3884)]:
 rows=saved[key]
 assert all(r.bit_count()==k for r in rows)
 assert all(sum(row>>j&1 for row in rows)==k for j in range(n))
 a=[[row>>j&1 for j in range(n)] for row in rows]
 b=[[n*x-k for x in row] for row in a]
 r=weighted_rooks(b)
 assert r==centered[name+'_centered_rook_numbers']
 S=sum(x*x for row in b for x in row)
 energy4=sum(x**4 for row in b for x in row)
 row_energy=sum(sum(x*x for x in row)**2 for row in b)
 col_energy=sum(sum(b[i][j]**2 for i in range(n))**2 for j in range(n))
 trace2=sum(sum(b[i][h]*b[j][h] for h in range(n))**2 for i in range(n) for j in range(n))
 r4=Fraction(3,2)*energy4-Fraction(3,4)*(row_energy+col_energy)+Fraction(S*S,8)+Fraction(trace2,4)
 variance=sum((sum(a[i][h]*a[j][h] for h in range(n))-lam)**2 for i in range(n) for j in range(n) if i!=j)
 assert r[2]==Fraction(S,2) and r[3]==Fraction(2,3)*sum(x**3 for row in b for x in row) and r[4]==r4
 radial=[factorial(n-m)*k**(n-m)*r[m] for m in range(n+1)]
 assert radial==centered[name+'_integer_radial_coefficients']
 p=matching_dp(rows,n);q=ryser(rows,n);assert p==q==expect
 assert sum(radial)==n**n*p
 comp=[((1<<n)-1)^row for row in rows]
 compdp=matching_dp(comp,n);compryser=ryser(comp,n);assert compdp==compryser
 records.append({'name':name,'rows':rows,'row_intersection_variance':variance,'centered_r4':int(r4),'centered_rooks':r,'radial_coefficients':radial,'permanent_dp_and_ryser':p,'complement_permanent_dp_and_ryser':compdp})
diff=[b-a for a,b in zip(records[0]['radial_coefficients'],records[1]['radial_coefficients'])]
assert diff==centered['radial_coefficient_difference']
assert sum(diff)==32*13**13
assert records[1]['centered_r4']-records[0]['centered_r4']==13**4*16//4
rows=saved['plane_rows'];r,s,c,d=0,1,1,5
assert (rows[r]>>c&1,rows[r]>>d&1,rows[s]>>c&1,rows[s]>>d&1)==(1,0,0,1)
columns=[j for j in range(n) if j not in (c,d)]
sub=[sum((row>>j&1)<<h for h,j in enumerate(columns)) for i,row in enumerate(rows) if i not in (r,s)]
minor=matching_dp(sub,n-2);assert minor==ryser(sub,n-2)==214
original=[[Fraction(row>>j&1) for j in range(n)] for row in rows]
def weighted_permanent(a):
 dp=[Fraction(0)]*(1<<n);dp[0]=Fraction(1)
 for mask in range((1<<n)-1):
  i=mask.bit_count()
  for j in range(n):
   if not (mask>>j&1):dp[mask|(1<<j)]+=dp[mask]*a[i][j]
 return dp[-1]
values=[]
for t in [Fraction(0),Fraction(1,2),Fraction(1)]:
 a=[row.copy() for row in original]
 for i,j,sgn in [(r,c,-1),(s,d,-1),(r,d,1),(s,c,1)]:a[i][j]+=sgn*t
 assert all(sum(row)==4 for row in a)
 assert all(sum(a[i][j] for i in range(n))==4 for j in range(n))
 p=weighted_permanent(a);assert p==3852-372*t+428*t*t
 values.append({'t':str(t),'permanent':str(p),'binary':t in (0,1)})
out={'scope':'Exact route verification only. Neither full Ryser proof nor legal negative witness.','records':records,'radial_difference_negative_orders':[m for m,value in enumerate(diff) if value<0],'radial_sum_difference':sum(diff),'continuous_switch':{'indices_zero_based':[r,s,c,d],'two_deleted_minor_permanent':minor,'linear_coefficient':-372,'quadratic_coefficient':428,'weighted_dp_controls':values},'data_source_sha256':{name:hashlib.sha256((BASE/name).read_bytes()).hexdigest() for name in ['ryser-rook-comparison.json','ryser-centered-rook-diagnostic.json']}}
path=BASE/'ryser-centered-route-verification.json'
path.write_text(json.dumps(out,indent=2)+'\n')
print({'verified_actual_matrices':len(records),'negative_radial_difference_orders':out['radial_difference_negative_orders'],'continuous_midpoint_is_not_binary':not values[1]['binary'],'scope':out['scope']})
