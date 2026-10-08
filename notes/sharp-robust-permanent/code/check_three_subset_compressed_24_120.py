#!/usr/bin/env python3
"""Verify fixed Sn triple-action rational certificates, n=24..120, without LP."""
import json,math
from fractions import Fraction as F
from pathlib import Path

def orbital(n,x,y,z):
 N=n*(n-1)*(n-2)//6
 a=(n-2)*(2*n+(n-3)*x)//2
 b=(n-2)*x*(x-1)//2+(x+1)*(n-x)+(n-4)*y
 c=(x*(x-1)*(x-2)//6 if x>=3 else 0)+x*y+z
 vals=(N-a+b-c,a-2*b+3*c,b-3*c,c)
 assert sum(vals)==N and min(vals)>=0
 return vals

def all_types(n):
 for x in range(n+1):
  for y in range((n-x)//2+1):
   for z in range((n-x-2*y)//3+1):
    r=n-x-2*y-3*z
    if r==0 or r>=4:yield (x,y,z,r)

def class_size(n,t):
 x,y,z,r=t
 den=math.factorial(x)*2**y*math.factorial(y)*3**z*math.factorial(z)
 if r:den*=r
 assert math.factorial(n)%den==0
 return math.factorial(n)//den

def check_entry(rec):
 n=rec['n']
 P=[(tuple(v['type']),F(v['weight'])) for v in rec['P']]
 Q=[(tuple(v['type']),F(v['weight'])) for v in rec['Q']]
 assert len(P)==3 and len(Q)==2 and P[0][0]==(n,0,0,0)
 assert all(t[0]+2*t[1]+3*t[2]+t[3]==n and (t[3]==0 or t[3]>=4) for t,w in P+Q)
 assert len({t for t,w in P+Q})==5 and min(w for t,w in P+Q)>0
 assert sum(w for t,w in P)==sum(w for t,w in Q)==1
 lam=[F(v) for v in rec['dual']]
 lo,hi,C=F(rec['lower']),F(rec['upper']),F(rec['C'])
 assert len(lam)==3 and hi-lo==C==P[0][1] and 0<C<1
 for j in range(4):
  assert sum(w*orbital(n,*t[:3])[j] for t,w in P)==sum(w*orbital(n,*t[:3])[j] for t,w in Q),(n,j)
 D=math.lcm(*(v.denominator for v in lam+[lo,hi]))
 vec=[int(v*D) for v in lam]
 low,high=int(lo*D),int(hi*D)
 for t,w in P+Q:
  f=orbital(n,*t[:3])
  val=(D if t[0]==n else 0)-sum(vec[j]*f[j] for j in range(3))
  assert val==(high if t in {p for p,v in P} else low),(n,t,val,low,high)
 states=0
 for x,y,z,r in all_types(n):
  f=orbital(n,x,y,z)
  val=(D if x==n else 0)-sum(vec[j]*f[j] for j in range(3))
  assert low<=val<=high,(n,x,y,z,r,low,val,high)
  states+=1
 size=math.factorial(n)
 max_density=max(w/class_size(n,t) for t,w in Q)
 delta=F(1,2*size*max_density)
 assert delta>0
 for t,w in Q:assert F(1,size)-delta*w/class_size(n,t)>=0
 return states,C

def main():
 data=json.loads((Path(__file__).resolve().parents[1]/'certificates'/'three_subset_n24_120.json').read_text(encoding='utf-8'))
 recs=data['degrees']
 assert len(recs)==97 and [c['n'] for c in recs]==list(range(24,121))
 total=0
 for rec in recs:
  count,C=check_entry(rec);total+=count
  if rec['n']<=31 or rec['n']%10==0:
   print('PASS n=%d C=%s compressed_type_count=%d'%(rec['n'],C,count),flush=True)
 print('VERIFIED 97 FIXED EXACT OPTIMA 24..120;',total,
       'EXHAUSTIVE CONJUGACY-TYPE CHECKS',flush=True)
if __name__=='__main__':main()
