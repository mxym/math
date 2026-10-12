#!/usr/bin/env python3
"""Independent marked-product recurrence and exact Rayleigh checks.

The first verifier uses binary digits. This one propagates P and a marked U,
uses recursive factorial weights, and checks a separate order-eight Gram matrix.
Neither checker needs floating-point arithmetic or third-party packages.
"""
import math,json,hashlib,sys
from pathlib import Path
if not __debug__:raise SystemExit('Optimized Python is not allowed.')
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
R=Path(__file__).resolve().parent

def poladd(a,b):
 c=[0]*max(len(a),len(b))
 for j,v in enumerate(a):c[j]+=v
 for j,v in enumerate(b):c[j]+=v
 return c

def factor_mul(p,d,a,b):
 q=[0]*(len(p)+d)
 for j,v in enumerate(p):q[j]+=a*v;q[j+d]+=b*v
 return q

def even_norm(p,degree):
 w=math.factorial(degree);out=0
 for j,c in enumerate(p):
  if 2*j>degree:
   assert c==0
   continue
  out+=c*c*w
  if 2*j+2<=degree:
   top=w*(2*j+2)*(2*j+1);bottom=(degree-2*j)*(degree-2*j-1)
   w,rem=divmod(top,bottom);assert rem==0
 return out

def formula(K,C):
 M=2**K;n=2*M;p=[1];u=[0]
 for k in range(K):
  d=2**k;a=(C*d)**d;b=(M-1)**d
  u=poladd(factor_mul(u,d,a,b),[a*x for x in p])
  p=factor_mul(p,d,a,b)
 s0=[2*(M-1)*x for x in u]
 sp=[2*C*(j+1)*p[j+1] if j+1<len(p) else 0 for j in range(len(p))]
 sr=poladd(s0,sp);pn=even_norm(p,n)
 zn=n*even_norm(s0,n-2);rn=n*even_norm(sr,n-2)
 zd=2*C*K*(M-1)*pn;rd=4*C*(M-1)*(K+1)*pn
 return pn,zn,zd,rn,rd

def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def cj(a):return a[0],-a[1]
def per(a):
 n=len(a);out=(0,0)
 for mask in range(1,1<<n):
  term=(1,0)
  for row in a:
   term=mul(term,(sum(row[j][0] for j in range(n) if mask>>j&1),sum(row[j][1] for j in range(n) if mask>>j&1)))
  if (n-mask.bit_count())%2:term=(-term[0],-term[1])
  out=add(out,term)
 return out

def direct_small():
 # K=2,c=5: after a common scaling, z_i=s*t_i with s^2=3/20.
 # The integer Gram matrix 20 J+3 t t* has identical normalized cofactor ratios.
 t=[(0,0),(0,0),(0,2),(0,-2),(1,1),(-1,1),(-1,-1),(1,-1)]
 a=[[add((20,0),tuple(3*x for x in mul(v,cj(w)))) for w in t] for v in t]
 p=per(a);assert p[1]==0 and p[0]>0
 C=[]
 for i in range(8):
  row=[]
  for j in range(8):
   minor=[[a[r][s] for s in range(8) if s!=j] for r in range(8) if r!=i]
   row.append(mul(a[i][j],per(minor)))
  assert (sum(x for x,y in row),sum(y for x,y in row))==p
  C.append(row)
 nums=[]
 for w in [t,[(v[1],0) for v in t]]:
  q=(0,0)
  for i in range(8):
   for j in range(8):q=add(q,mul(mul(cj(w[i]),C[i][j]),w[j]))
  assert q[1]==0
  den=p[0]*sum(x*x+y*y for x,y in w);nums.append((q[0],den))
 pn,zn,zd,rn,rd=formula(2,5)
 assert nums[0][0]*zd==nums[0][1]*zn
 assert nums[1][0]*rd==nums[1][1]*rn
 return {'n':8,'c':5,'rank_two_integer_gram_formula':'20 J+3 t t*','cofactor_row_sums_verified':True,'two_full_Rayleigh_formulas_cross_checked':True}

checks=[]
for K,C,zb,rb in [(8,7,1137,639),(10,5,1991,1094)]:
 pn,zn,zd,rn,rd=formula(K,C)
 assert zb*zd<1000*zn<(zb+1)*zd
 assert rb*rd<1000*rn<(rb+1)*rd
 got={'scaled_polynomial_fock_norm':str(pn),'complex_numerator':str(zn),'complex_denominator':str(zd),'real_numerator':str(rn),'real_denominator':str(rd)}
 expected=json.loads((R/f'DYADIC_EXACT_VALUES_K{K}_C{C}.json').read_text())
 assert got==expected
 dig=hashlib.sha256(('\n'.join(map(str,[pn,zn,zd,rn,rd]))+'\n').encode()).hexdigest()
 checks.append({'K':K,'C':C,'n':2**(K+1),'all_five_exact_values_match':True,'scaled_exact_values_sha256':dig})
result={'status':'PASS','method':'marked-product recurrence; recursive Fock weights; independent Gaussian-integer order-eight Gram calculation','cases':checks,'direct_small':direct_small(),'arithmetic':'Python integers only'}
s=json.dumps(result,indent=2)+'\n';(R/'INDEPENDENT_EXACT_RESULT.json').write_text(s);print(s,end='')
