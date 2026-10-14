import numpy as np, scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from time import perf_counter
I2=np.eye(2); I4=np.eye(4)
v=np.array([1,0,0,1])/np.sqrt(2); P=np.outer(v,v)
Q1=np.diag([0.,1.])
def place(a,start,q):
 return sp.kron(sp.eye(2**start,format='csr'),sp.kron(sp.csr_matrix(a),sp.eye(2**(q-start-int(round(np.log2(a.shape[0]))))),format='csr'),format='csr')
for delta in (.2,.5,.8):
 L=delta*P+(I4-P)
 h0=L@np.kron(Q1,I2)@L
 B=np.kron(L,L)
 hmid=B@(np.eye(16)-np.kron(I2,np.kron(P,I2)))@B
 C=np.kron(L,I2)
 hlast=C@np.kron(I2,I4-P)@C
 for depth in range(1,7):
  q=2*depth+1; z=2**q; t=perf_counter()
  H=place(h0,0,q)+place(hlast,2*depth-2,q)
  for ell in range(1,depth):H=H+place(hmid,2*ell-2,q)
  odd=np.array([i for i in range(z) if i.bit_count()%2],dtype=int)
  even=np.array([i for i in range(z) if not i.bit_count()%2],dtype=int)
  oddH=H[odd][:,odd]; evenH=H[even][:,even]
  vals=eigsh(oddH,k=1,which='SA',tol=1e-10,maxiter=50000,return_eigenvectors=False)
  ge=eigsh(evenH,k=1,which='SA',tol=1e-10,maxiter=50000,return_eigenvectors=False)
  print({'delta':delta,'depth':depth,'qubits':q,'odd_min':float(vals[0]),'even_min':float(ge[0]),'seconds':round(perf_counter()-t,3)},flush=True)
