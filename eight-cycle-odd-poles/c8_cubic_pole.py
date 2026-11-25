import pickle,numpy as np
p=65521
D=[pickle.load(open('cub7_1_%d.pkl'%i,'rb')) for i in range(4)]
E,R,S=D[1];print(len(R),R==S)
M=[np.array(x[0]) for x in D]
assert not np.count_nonzero((M[3]-3*M[2]+3*M[1]-M[0])%p)
a2=(M[2]-2*M[1]+M[0])*pow(2,-1,p)%p
a1=(M[1]-M[0]-a2)%p
a0=M[0]
k0=[i for i,w in enumerate(R) if 0 not in w]
kk=[i for i,w in enumerate(R) if 0 in w]
G=[i for i,w in enumerate(R) if sorted(w)==[1,2,5,6]]
print(G,[R[i] for i in kk])

from sympy import GF, Symbol
from sympy.polys.matrices import DomainMatrix
from collections import defaultdict
x=Symbol("x"); F=GF(p).frac_field(x)
# Show selected root is a pole by exact rational arithmetic.
J=[[[[F(int(a0[k,i,j]))+F.gens[0]*F(int(a1[k,i,j]))+F.gens[0]**2*F(int(a2[k,i,j])) for j in range(len(S))] for i in range(len(R))] for k in (2,3)]][0]
d=defaultdict(list)
for i in k0:d[tuple(sorted(R[i]))].append(i)
X=[F.zero]*len(R);Y=[F.zero]*len(S)
X[kk[1]]=F.one;Y[kk[0]]=F.one
for group, ids in d.items():
 jds=[j for j in k0 if tuple(sorted(S[j]))==group]
 B=DomainMatrix.from_list([[J[0][i][j] for j in jds] for i in ids],F)
 BI=B.inv().to_list()
 for k,j in enumerate(jds):X[j]=-sum((a*J[0][i][kk[1]] for a,i in zip(BI[k],ids)),F.zero)
 for k,i in enumerate(ids):Y[i]=-sum((J[0][kk[0]][j]*BI[k1][k] for k1,j in enumerate(jds)),F.zero)
w=sum((Y[i]*J[1][i][j]*X[j] for i in range(len(R)) for j in range(len(S)) if Y[i] and X[j]),F.zero)
print(w)
root=12833
def val(f):
 f0=f
 fac=F.field.ring.from_dict({(1,):GF(p)(1),(0,):GF(p)(-root)})
 e=0
 while not f.rem(fac):
  f=f.exquo(fac);e+=1
 return e,f.evaluate(0,GF(p)(root))
assert tuple(map(int,val(w.numer)))==(0,26517)
assert tuple(map(int,val(w.denom)))==(1,57464)
print('Exact simple pole at x=12833, numerator 26517 and reduced denominator 57464')
for group,ids in d.items():
 jds=[j for j in k0 if tuple(sorted(S[j]))==group]
 B=DomainMatrix.from_list([[J[0][i][j] for j in jds] for i in ids],F)
 want=2 if group==(1,2,5,6) else 0
 assert val(B.det().numer)[0]==want and val(B.det().denom)[0]==0
 print(group,val(B.det().numer),val(B.det().denom))
