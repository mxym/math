"""Search for a short planar witness recipe for each count 132..2678."""
import json
from math import comb
def path(n,E,s,t):
 A=[[] for i in range(n)]
 for i,j in E:A[i].append(j);A[j].append(i)
 def f(i,used):
  if i==t:return 1
  used|=1<<i
  return sum(f(j,used) for j in A[i] if not (used>>j)&1)
 return f(s,0)
G=json.load(open('labeled.json'))
P={}
for i,g in enumerate(G):
 if g['type']!='P':continue
 for ei,(s,t) in enumerate(g['edges']):
  A=g['edges'][:ei]+g['edges'][ei+1:];p=path(g['n'],A,s,t);c=g['k']-p
  P.setdefault((p,c),(i,ei))
ans={}
for (p,c),(i,e) in P.items():
 for (q,d),(j,f) in P.items():
  w=0;base=c+d+p*q
  while base<=2678:
   if base>=132:
    score=G[i]['n']+G[j]['n']+2*w
    if base not in ans or score<ans[base][0]: ans[base]=(score,i,e,j,f,w,p,q)
   base+=p+q+w;w+=1
print('pole types',len(P),'cover',len(ans),'missing',sorted(set(range(132,2679))-ans.keys()))
with open('cover.txt','w') as fd:
 for k in sorted(ans):print(k,*ans[k],file=fd)
