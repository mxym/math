from itertools import product
import numpy as np
s=8;p=101;t=7
W={q:[] for q in range(-s,s+1)}
for w in product((-1,0,1),repeat=s): W[sum(w)].append(w)
I={q:{w:i for i,w in enumerate(ws)} for q,ws in W.items()}
A={q:np.zeros((len(ws),len(W[-q])),dtype=np.int32) for q,ws in W.items()}
for v in range(1<<(2*s)):
    b=[v>>i&1 for i in range(2*s)]
    d=[b[(i+1)%(2*s)]-b[i] for i in range(2*s)]
    a=tuple(d[::2]);y=tuple(d[1::2]);q=sum(a)
    i=I[q][a];j=I[-q][y];e=sum(b[i] for i in range(2*s) if d[i]==0)
    A[q][i,j]=(A[q][i,j]+pow(t,e,p))%p

def rank(a):
    r=0
    for j in range(a.shape[1]):
        nz=np.flatnonzero(a[r:,j]);
        if not nz.size: continue
        k=r+int(nz[0]);a[[r,k]]=a[[k,r]]
        ix=r+1+np.flatnonzero(a[r+1:,j]);
        if ix.size:
            m=(a[ix,j]*pow(int(a[r,j]),-1,p))%p
            a[ix,j:]=(a[ix,j:]-m[:,None]*a[r,j:])%p
        r+=1
    return r
rr={q:rank(a) for q,a in A.items()}
print([(q,len(W[q]),rr[q]) for q in W]);print('total',sum(rr.values()))
assert sum(rr.values())==6518
