from itertools import combinations
W=(53,77,83,106,154,166,169,212)
H=(8707,9345,17600,49248,34864,2328,4364,4614)
n=24
G=[set()for _ in range(n)]
def edge(i,j):
 G[i].add(j);G[j].add(i)
for k,w in enumerate(W):
 for i in range(8):
  if w>>i&1:edge(i,8+k)
for k,w in enumerate(H):
 for i in range(16):
  if w>>i&1:edge(i,16+k)
assert all((x&y).bit_count()==(2 if (i-j)%8 in [1,7] else 0)for (i,x),(j,y)in combinations(enumerate(H),2))
B=[[int(i==j)for j in range(n)]for i in range(n)];power=[0];cp=[1]
for k in range(1,n+1):
 B=[[sum(B[a][j]for a in G[i])for j in range(n)]for i in range(n)]
 power.append(sum(B[i][i]for i in range(n)))
 q,r=divmod(-sum(cp[j]*power[k-j]for j in range(k)),k);assert not r
 cp.append(q)
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]+=x*y
 return z
h=[1,0,-12,-4,34,16,-4]
fs=[[1,0]]+[[1,-2]]*3+[[1,2],[1,4],[1,-4,-8]]+[[1,2,-2]]*2+[h]*2
f=[1]
for v in fs:f=mul(f,v)
assert f==cp and sum(z*3**(6-i)for i,z in enumerate(h))==-1
print('Exact 24-site characteristic polynomial; repeated real eigenvalue >3.')
