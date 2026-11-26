import itertools, subprocess, sys, numpy as np
P=13
pairs=lambda r:list(itertools.combinations(range(r),2))
def read(exe,q,s,n):
  lines=subprocess.check_output([exe,str(q),str(s)],text=True).strip().splitlines()
  assert len(lines)>n and lines[-n-1].startswith('result '),lines[:4]
  assert all(not a.endswith('det 0') for a in lines if a.startswith('K '))
  lines=lines[-n:]
  return np.asarray([[int(x) for x in l.split()] for l in lines],dtype=np.int32)
def mat(A,G,r):
  pp=pairs(r); D=(G[:12,:12]-A)%P
  W=np.zeros((12*len(pp),12*len(pp)),dtype=np.int32)
  for j,e in enumerate(pp):
   for k,f in enumerate(pp):
    if j==k: block=(A+(r-2)*D)%P
    elif len(set(e+f))==3:
      u={a:i for i,a in enumerate(sorted(set(e+f)))}
      ii=pairs(3).index(tuple(u[a] for a in e));jj=pairs(3).index(tuple(u[a] for a in f))
      block=G[ii*12:ii*12+12,jj*12:jj*12+12]
    else: continue
    W[12*j:12*j+12,12*k:12*k+12]=block
  return W
def rkdet(M):
  n=len(M)
  d=1;r=0
  for j in range(n):
   loc=np.nonzero(M[r:,j])[0]
   if not len(loc): continue
   i=loc[0]+r
   if i!=r: M[[i,r]]=M[[r,i]];d=-d
   k=int(M[r,j]);d=(d*k)%P
   col=(M[r+1:,j]*(-pow(k,-1,P)))%P
   non=np.flatnonzero(col)+r+1
   M[non,j+1:]=(M[non,j+1:]+np.outer(col[non-r-1],M[r,j+1:]))%P
   r+=1
  return r,d if r==n else 0

if __name__=="__main__":
 executable=sys.argv[1] if len(sys.argv)>1 else "./local-negative"
 expected=[3,9,12,1,1,1,12,1,1,1,10,1,9]
 for s in (1,4):
  A=read(executable,5,s,12);G=read(executable,7,s,36)
  assert A.shape==(12,12) and G.shape==(36,36)
  assert (mat(A,G,3)==G).all()
  for r in ([2,3]+[x for x in range(4,17) if x not in {10,13}] if s==1 else [10,13]):
   M=mat(A,G,r); a,b=rkdet(M)
   assert a==len(M) and b==({2:1,3:12}[r] if r<4 else expected[r-4])
   print(s,r,a,len(M),b,flush=True)
