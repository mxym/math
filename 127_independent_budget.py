from fractions import Fraction as F
from functools import lru_cache
from math import floor
D={"old":[15002,15002,15003,15005,15032,15073,15121,15174,15231,15293,15357,15423,15492,15528,15634,15709,15784],"tan":[[7,46,[838750,0,4538155,0,2801139,0,0,0,0,0,0,0],31832],[7,82,[847305,0,4524998,358140,3723215,1294305,0,0,158349,0,0,0],-8490]],"inherited":[[7,61,7000,"4743867114278617/2800000000000000"],[7,53,10000,"16850179333246369/10000000000000000"],[7,59,7000,"14810705924620269/8750000000000000"],[7,63,10000,"3386088072202697/2000000000000000"],[7,51,10000,"16829313074117719/10000000000000000"],[7,55,10000,"3373768082225781/2000000000000000"],[7,49,10000,"105034447210479/62500000000000"],[7,67,10000,"529950220864393/312500000000000"],[7,69,10000,"16969140491823137/10000000000000000"]],"prev":[[23,1602258],[25,1623081],[31,1653149],[35,1666337],[37,1670696],[39,1669262],[41,1671300],[43,1683463],[45,1687663],[57,1694283],[65,1697189],[71,1700717],[75,1702892],[77,1703976]],"extra":[[21,1584288,8000,"15842879327939213/10000000000000000"],[27,1637560,8000,"818779763233029/500000000000000"],[29,1645997,8000,"3291993027998531/2000000000000000"],[35,1655543,12000,"993325567992929/600000000000000"],[37,1659255,12000,"16592548571951079/10000000000000000"],[43,1670143,12000,"8350713958562559/5000000000000000"],[45,1673715,12000,"25105711647484243/15000000000000000"],[57,1687940,12000,"12659545261674437/7500000000000000"],[59,1689447,12000,"50683399903678147/30000000000000000"],[73,1701210,8000,"17012094004507081/10000000000000000"],[79,1707168,6000,"17071677859475427/10000000000000000"],[83,1711560,6000,"51346797030196187/30000000000000000"],[87,1702975,12000,"51089230114619003/30000000000000000"]]}
n=127
u=[(2,F(3,2))]+[(i,F(w,10000)) for i,w in enumerate(D['old'],4)]
u+=[(33,F(16498,10000)),(40,F(16659,10000)),(47,F(16779,10000)),(56,F(16796,10000))]
u += [(q,F(e)) for _,q,_,e in D['inherited']]
u += [(q,F(v,10**6)) for q,v in D['prev']]
u += [(q,F(v,10**6)) for q,v,_,_ in D['extra']]
assert len(D['extra'])==13
for q,v,_, e in D['extra']:
 assert F(v-1,10**6)<F(e)<=F(v,10**6)
def weight(k):
 w={1:F(4,3),5:F(1000,253),7:F(1000,203),9:F(10000,1648)}.get(k,F(0))
 core=[(F(3,4)+F(k-1,q-1)*(e-F(3,4)),q) for q,e in u if q<=k]
 core.extend((F(3,4)+F(sum(h)+(k-1)*B,10**7),('tan',q))for _,q,h,B in D['tan'])
 if core:
  val,q=min(core,key=lambda x:x[0])
  assert val>=F(3,4)
  if F(k)/val>w:
   return floor(10**6*F(k)/val),q
 return floor(10**6*w),'local'

Ws={k:weight(k) for k in [1]+list(range(5,n+1,2))}
@lru_cache(None)
def best_parts(total,count):
 if total==count==0:return 0,()
 if count<1 or total<5*count or (total-count)%2:return 10**14,()
 cand=[]
 for k in range(5,total-5*(count-1)+1,2):
  if k not in Ws:continue
  cost,P=best_parts(total-k,count-1)
  cand.append((cost+Ws[k][0],tuple(sorted((*P,k)))))
 return min(cand)if cand else (10**14,())
@lru_cache(None)
def all_opt(total,count):
 if total==count==0:return {()}
 target,unused=best_parts(total,count)
 if target>=10**14:return set()
 opts=set()
 for k in range(5,total-5*(count-1)+1,2):
  if k not in Ws:continue
  if best_parts(total-k,count-1)[0]+Ws[k][0]==target:
   opts.update(tuple(sorted((*P,k)))for P in all_opt(total-k,count-1))
 return opts
scans=[]
for t in range(n+1):
 for o in range(t+13,n-t+1):
  if (n-t-o)%2:continue
  for s in range(min(o,t+5)+1):
   c,P=best_parts(n-t-s,o-s)
   if c<10**14:
    scans.append((s*Ws[1][0]+c,t,o,s,P))
optimal=min(scans)
assert optimal[:4]==(84004920,0,13,5)
print('independent DP PASS',optimal,len(scans))
print('minimum partitions',all_opt(122,8));print([(k,Ws[k])for k in set(optimal[-1])|{1}])
print('runner-up barrier choice',sorted(scans)[1])
