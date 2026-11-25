import numpy as np,pickle
P=65521
def gauss(m):
 B=m.copy();cols=[];k=0
 for j in range(B.shape[1]):
  inds=np.flatnonzero(B[k:,j])
  if not len(inds):continue
  i=k+inds[0];B[[k,i]]=B[[i,k]];cols.append(j)
  B[k]=B[k]*pow(int(B[k,j]),-1,P)%P
  f=B[:,j].copy();f[k]=0
  B=(B-f[:,None]*B[k,None,:])%P;k+=1
 return cols,B
for v in [0]:
 E,R,S=pickle.load(open(f'./c8q5_0_1_{v}.pkl','rb'))
 ki=[i for i,w in enumerate(R) if 0 not in w]; ei=[i for i,w in enumerate(R) if 0 in w]
 kj=[i for i,w in enumerate(S) if 0 not in w]; ej=[i for i,w in enumerate(S) if 0 in w]
 H=E[2][np.ix_(ki,kj)];b,I=gauss(np.c_[H,np.eye(len(H),dtype=np.int64)]);assert b==list(range(len(H)));h=I[:,len(H):]
 L=E[2][np.ix_(ei,kj)]; B=E[2][np.ix_(ki,ej)]
 U=np.eye(len(R),dtype=np.int64)[ei]; V=np.eye(len(S),dtype=np.int64)[:,ej]
 U[:,ki]=-L@h%P; V[kj,:]=-h@B%P
 print(v,U@E[2]@V%P,U@E[3]@V%P)
 assert int((U@E[3]@V%P)[0,1])==21540
