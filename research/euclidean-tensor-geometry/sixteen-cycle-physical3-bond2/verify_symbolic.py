from collections import defaultdict
from sympy import symbols
from sympy.polys.matrices import DomainMatrix
from sympy.polys.domains import ZZ
s=8
rot=lambda a:a[1:]+a[:1]
reflect=lambda a:tuple(-a[-i%s] for i in range(s))
# Generate words and orbit representatives from binary cyclic walks, then use direct symbolic rank.
D=defaultdict(int)
W=set()
for bits in range(1<<(2*s)):
    b=[bits>>i&1 for i in range(2*s)]
    w=[b[(i+1)%(2*s)]-b[i] for i in range(2*s)]
    row=tuple(w[::2]); col=tuple(w[1::2]);
    if sum(row)!=0 or sum(col)!=0: continue
    e=sum(b[i] for i in range(2*s) if w[i]==0)
    D[row,col,e]+=1
    W.add(row);W.add(col)
O={}; rep={};
for u in sorted(W):
    if u in rep: continue
    vals=[];w=u
    while not vals or w!=u:
        vals.append(w);w=rot(w)
    for j,w in enumerate(vals):rep[w]=(u,(-1)**j)
    if len(vals)%2==0:O[u]=[(w,(-1)**j) for j,w in enumerate(vals)]
B={1:[], -1:[]}
for u in sorted(O):
    v,e=rep[reflect(u)]
    if v<u:continue
    if v==u:B[e].append([(u,1)])
    else:
        for c in B:B[c].append([(u,1),(v,c*e)])
Bsmall,Blong=sorted(B.values(),key=len)
print('dims',len(Bsmall),len(Blong),flush=True)
t=symbols('t');R=ZZ.poly_ring(t);tp=[R.gens[0]**i for i in range(2*s+1)];
A=[]
for row in Bsmall:
    u=row[0][0]
    A.append([sum(c*d*D.get((u,w,i),0)*tp[i] for v,c in col for w,d in O[v] for i in range(2*s+1)) for col in Blong])
C=max(sum(abs(c) for c in a.to_dict().values()) for aa in A for a in aa if a); d=max(a.degree() for aa in A for a in aa if a)
print('max norm',C,'degree',d,flush=True)
DM=DomainMatrix(A,(len(Bsmall),len(Blong)),R)
rank = len(DM.rref_den(method='FF')[2])
print('rank', rank, flush=True)
assert (len(Bsmall), len(Blong), C, d, rank) == (57, 84, 4, 12, 49)
