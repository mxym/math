"""Exact consequences of R <= floor(2B/3) for Conway 99. Standard-library Python."""
if not __debug__: raise RuntimeError("run with assertions enabled")
vals=[]
for P in range(852):
 for G in range(P//6+1):
  B=P-6*G;h=B-int(B%3!=0);r=2*B//3;e=max(0,726-6*G)
  if 72*G-5544+2*e>3696-P+2*r:continue
  d=h+min(15*G,(3696-P+2*r)//4)
  y3=24948+max(0,7392-2*P-4*d)+2*(20790-9*P-36*G)
  y4=1398474+765072+18*P-48*d+2*(831600+36*P-2286*G)+96*(2079-9*G)+103*(8316-6*P)
  vals.append((P,G,B,h,r,d,y3,y4))
assert len(vals)==59261 and max(v[1] for v in vals)==118
for j,m in ((6,44804),(7,3748902)):
 assert min(v[j] for v in vals)==m
 assert [v[:6] for v in vals if v[j]==m]==[(851,118,143,142,95,900)]
print(len(vals),'pairs; G<=118; y3>=44804; y4>=3748902')
