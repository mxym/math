#!/usr/bin/env python3
from itertools import combinations,product
import json,math,sys
from pathlib import Path
F8={(a,b) for a in (-1,0,1) for b in (-1,0,1) if (a,b)!=(0,0)}
P=((0,1),(3,1),(3,-1));Q=14

def req(c,m):
 if not c:raise ValueError(m)
def pf(n):
 out=[];p=2
 while p*p<=n:
  if n%p==0:
   out.append(p)
   while n%p==0:n//=p
  p=3 if p==2 else p+2
 if n>1:out.append(n)
 return out
def sf(n):return n==math.prod(pf(n))
def maxgens(q):
 out=[]
 for p in pf(q):
  if p==2:out.append((0,1))
  elif p==7:out += [(3,1),(3,-1)]
  elif p in (3,5,11,13):out.append((p,0))
  else:raise ValueError(p)
 return tuple(out)
def mul(x,y):
 a,b=x;c,d=y
 return (a*c+2*b*d,a*d+b*c)
def divs14():
 out=[]
 for es in product(range(3),range(2),range(2)):
  if es==(0,0,0):continue
  z=(1,0)
  for p,e in zip(P,es):
   for _ in range(e):z=mul(z,p)
  out.append((es,z))
 req(len(out)==11,'div count');return out
def sp(g):
 a,b=g;D=abs(a*a-2*b*b);return D//math.gcd(abs(a),abs(b))
def div(z,g):
 x,y=z;a,b=g;D=abs(a*a-2*b*b)
 return (a*x-2*b*y)%D==0 and (-b*x+a*y)%D==0
def allowed(z,gs):return all(not div(z,g) for g in gs)
def verify(q,gs,w):
 root=tuple(w['root']);steps=[tuple(d) for d in w['steps']]
 req(all(d in F8 for d in steps),'step');req(allowed(root,gs),'root')
 z=root
 for d in steps:
  z=(z[0]+d[0],z[1]+d[1]);req(allowed(z,gs),'forbidden')
 dx=z[0]-root[0];dy=z[1]-root[1]
 req(dx%q==0 and dy%q==0,'closed');v=(dx//q,dy//q)
 req(v!=(0,0) and list(v)==w['voltage'],'voltage')
 cnt=sum(allowed((x,y),gs) for x in range(q) for y in range(q))
 req(cnt==w['allowed_residues'],'count');return len(steps)

def main():
 here=Path(__file__).resolve().parent
 d=json.loads((here/'sqrt2_period_endpoint.json').read_text())
 req(d['schema']=='mxym-math-002-v4-sqrt2-f8-period-endpoint-1','schema')
 req([tuple(x) for x in d['prime_generators']]==list(P),'primes')
 expected_q=[1]+[x for x in range(2,14) if sf(x)]
 lower=d['lower_period_failures'];req([x['q'] for x in lower]==expected_q,'lower range')
 L=[]
 for x in lower:
  gs=tuple(tuple(g) for g in x['generators']);req(gs==maxgens(x['q']),'max gens')
  L.append(verify(x['q'],gs,x['witness']))
 D=divs14()
 got=[(tuple(x['exponents']),tuple(x['generator'])) for x in d['divisor_ideals_14']]
 req(got==D,'divisors');req(all(14%sp(a)==0 for es,a in D),'period divisor')
 success={(0,1),(0,2)}
 req({tuple(x) for x in d['successful_prime_pairs']}==success,'success pairs')
 expected_fail=[tuple(c) for k in range(3) for c in combinations(range(3),k) if tuple(c) not in success]
 # k<3 above gives empty/singles/pairs, then filter successes = 5 failures.
 fs=d['failed_prime_subsets'];req([tuple(x['indices']) for x in fs]==expected_fail,'failed subset coverage')
 for x in fs:
  gs=tuple(tuple(g) for g in x['generators']);L.append(verify(Q,gs,x['witness']))
 expected_rep=[]
 for pair in sorted(success):
  for pos,j in enumerate(pair):
   other=P[pair[1-pos]]
   for es,a in D:
    if a==P[j]:continue
    if div(a,P[j]):expected_rep.append((pair,j,es,a,(other,a)))
 reps=d['proper_subideal_replacements']
 gotrep=[(tuple(x['success_pair']),x['prime_index'],tuple(x['replacement_exponents']),
          tuple(x['replacement']),tuple(tuple(g) for g in x['generators'])) for x in reps]
 req(gotrep==expected_rep,'replacement coverage')
 for x in reps:L.append(verify(Q,tuple(tuple(g) for g in x['generators']),x['witness']))

 # Positive historical endpoint: sqrt(2), 3+sqrt(2).
 v3=here.parent.parent/'v3'/'certificates_v3'
 sys.path.insert(0,str(v3))
 from prime_element_checker import verify_certificate,statistics
 b=json.loads((v3/'sqrt2_eight_steps.json').read_text())
 req(verify_certificate(b['data'],b['certificate']),'positive')
 st=statistics(b['data'],b['certificate'])
 req(st['Q']==14 and st['avoiding_bound']==6,'positive stats')
 print(json.dumps({'status':'PASS','lower_radicals':len(lower),'divisor_ideals':len(D),
   'failed_prime_subsets':len(fs),'proper_subideal_replacements':len(reps),
   'failure_witnesses':len(L),'total_steps':sum(L),'max_walk_length':max(L),
   'positive_period':st['Q'],'positive_avoiding_bound':st['avoiding_bound'],
   'positive_irreducible_bound':st['irreducible_component_bound'],'arithmetic':'exact integer'},sort_keys=True))
if __name__=='__main__':main()
