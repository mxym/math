from itertools import product
import numpy as np

P=1009
def eliminate(M):
    A=M.copy()
    r=0
    piv=[]
    for j in range(A.shape[1]):
        hits=np.flatnonzero(A[r:,j])
        if not len(hits):
            continue
        i=r+hits[0]
        A[[r,i]]=A[[i,r]]
        A[r,j:]=A[r,j:]*pow(int(A[r,j]),-1,P)%P
        A[r+1:,j:]=(A[r+1:,j:]-A[r+1:,j:j+1]*A[r:r+1,j:])%P
        piv.append(j);r+=1
    return piv,A

def words(q):
    return np.array(list(product(range(q),repeat=4)), dtype=np.int64)
def altern(K,W):
    A=np.ones((len(W),len(W)),dtype=np.int64)
    for i in range(4):
        A=A*K[W[:,i,None],W[None,:,i]]*K[W[None,:,i],W[:,(i+1)%4,None]]%P
    return A
def difference(V,W):
    D=np.zeros((len(W),len(W)),dtype=np.int64)
    for i in range(4):
        D+=V[W[:,i,None],W[None,:,i]]-V[W[None,:,i],W[:,(i+1)%4,None]]
    return D%P

W=words(3)
A=altern(np.array([[1,1,1],[1,2,3],[1,4,5]],dtype=np.int64),W)
piv,Ae=eliminate(A)
assert len(piv)==80
(free,)=set(range(81))-set(piv)
h=np.zeros(81,dtype=np.int64);h[free]=1
for i,j in reversed(list(enumerate(piv))):
    h[j]=-Ae[i,j+1:] @ h[j+1:] %P
assert not np.any(A@h%P) and not np.any(h@A%P)
inds={tuple(w):i for i,w in enumerate(W)}
assert all(h[inds[tuple(w[1:])+tuple(w[:1])]]==(-h[i])%P for i,w in enumerate(W))
selector=(W[:,0,None]==0)&(W[None,:,0]==0)
s0=int((h @ (A*selector) @ h)%P)
s1=int((h @ (A*((W[None,:,0]==0)&(W[:,1,None]==0))) @ h)%P)
assert (s0,s1)==(9,1000)
print('Anchor: rank=80, free=%d, c=%d'%(free,s0),flush=True)

B4=[[323,723,309,941],[879,574,208,625],[298,91,464,5],[10,96,719,506]]
B6=[[323,723,309,941,879,574],[208,625,298,91,464,5],[10,96,719,506,636,718],
    [301,854,469,27,625,576],[301,552,554,470,718,706],[889,237,899,747,110,296]]
for s,V,wanted in [(4,B4,256),(5,[[i*j*j for j in range(5)]for i in range(5)],624),(6,B6,1296)]:
    W=words(s);K=np.array([[pow(i+1,j,P) for j in range(s)]for i in range(s)],dtype=np.int64)
    B=altern(K,W)
    rankB=len(eliminate(B)[0]);rankD=len(eliminate(B*difference(np.array(V,dtype=np.int64),W)%P)[0])
    assert rankB==s**4 and rankD==wanted
    print('q=%d: rank(B)=%d rank(D)=%d lifted=%d'%(3*s,rankB,rankD,80*rankB+rankD),flush=True)
