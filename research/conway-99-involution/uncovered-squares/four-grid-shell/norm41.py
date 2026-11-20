from itertools import product,permutations
P=[p for p in permutations(range(4))if p[0]^p[3]!=3];R=[2,3,4,5]
B=[tuple(sorted((z//2,z%2,R[p[z]],R[q[z]])for z in range(4)))for p in P for q in P if all(p[z]//2!=q[z]//2 for z in range(4))]
assert len(B)==len(set(B))==48;ids={w:i for i,w in enumerate(B)};seen=set();out=[]
for j,w in enumerate(B):
 if j in seen:continue
 orb=set()
 for a,b,sw in product(range(2),repeat=3):
  y=[tuple(t[i]for i in (a,1-a,b+2,3-b))for t in w]
  if sw:y=[(p,q,(r-2)^2,(s-2)^2)for p,q,r,s in y];y=[(p,q,r+2,s+2)for p,q,r,s in y]
  for sgn in product(range(2),repeat=4):
   V=tuple(sorted(tuple(c^t for c,t in zip(z,sgn))for z in y));orb.add(ids[V])
 seen|=orb;out.append((j,len(orb)))
assert len(seen)==48;print(out)
