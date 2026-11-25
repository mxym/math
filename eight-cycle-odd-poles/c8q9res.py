import pickle,sys
import numpy as np
from sympy import GF, Symbol
from sympy.polys.matrices import DomainMatrix
from collections import defaultdict
p=65521
g4,choice=map(int,sys.argv[1:])
arr=[pickle.load(open(f'./c8q9_{g}_{g4}_{choice}.pkl','rb')) for g in range(4)]
M=[np.array(x[0]) for x in arr]; R,S=arr[0][1:]
assert all((a[1],a[2])==(R,S) for a in arr)
assert not np.count_nonzero((M[3]-3*M[2]+3*M[1]-M[0])%p)
a2=(M[2]-2*M[1]+M[0])*pow(2,-1,p)%p
a1=(M[1]-M[0]-a2)%p;a0=M[0]
x=Symbol("x");F=GF(p).frac_field(x);X=F.gens[0]
J=[[[F(int(a0[k,i,j]))+X*F(int(a1[k,i,j]))+X**2*F(int(a2[k,i,j])) for j in range(len(S))] for i in range(len(R))] for k in (2,3)]
ki=[i for i,w in enumerate(R) if 0 not in w];ei=[i for i,w in enumerate(R) if 0 in w]
kj=[j for j,w in enumerate(S) if 0 not in w];ej=[j for j,w in enumerate(S) if 0 in w]
U=[[F(int(i==j)) for j in range(len(R))] for i in ei]
V=[[F(int(i==j)) for j in range(len(S))] for i in range(len(S))]
V=[[row[j] for j in ej] for row in V]
d=defaultdict(list)
for i in ki:d[tuple(sorted(R[i]))].append(i)
determinants={}
for group,ids in d.items():
 jds=[j for j in kj if tuple(sorted(S[j]))==group]
 H=DomainMatrix.from_list([[J[0][i][j] for j in jds] for i in ids],F); hi=H.inv().to_list()
 determinants[group]=H.det()
 for a,ir in enumerate(ei):
  for k,i in enumerate(ids):U[a][i]=-sum((J[0][ir][j]*hi[b][k] for b,j in enumerate(jds)),F.zero)
 for b,jc in enumerate(ej):
  for k,j in enumerate(jds):V[j][b]=-sum((hi[k][a]*J[0][i][jc] for a,i in enumerate(ids)),F.zero)
Ws=[]
for JS in J:
 W=[[sum((U[a][i]*JS[i][j]*V[j][b] for i in range(len(R)) for j in range(len(S)) if U[a][i] and JS[i][j] and V[j][b]),F.zero) for b in range(len(ej))] for a in range(len(ei))]
 Ws.append(W)
print('W2 ident zero on line:',not any(z for r in Ws[0] for z in r));W=Ws[1]
assert not any(W[i][j]+W[j][i] for i in range(len(W)) for j in range(len(W)))
pf=W[0][1]*W[2][3]-W[0][2]*W[1][3]+W[0][3]*W[1][2]
r=12833
fac=F.field.ring.from_dict({(1,):GF(p)(1),(0,):GF(p)(-r)})
def fval(f):
 if not f:return 100,0
 e=0
 while not f.rem(fac):f=f.exquo(fac);e+=1
 return e,int(f.evaluate(0,GF(p)(r)))
def val(z):
 if not z:return 100,0
 a,b=fval(z.numer),fval(z.denom)
 return a[0]-b[0],a[1]*pow(b[1],-1,p)%p
print('W3',[[val(z) for z in row] for row in W]);a,b=val(pf),val(W[0][1])
print('PF',a,'selected',b,'full corrected local normalized factor',a[1]*pow(b[1],-1,p)%p,'valuation delta',a[0]-b[0])
assert a==(-1,16895) and b==(-1,21978)
assert a[1]*pow(b[1],-1,p)%p==21540
assert {key:val(det)[0] for key,det in determinants.items() if val(det)[0]}=={(1,2,7,8):2}
