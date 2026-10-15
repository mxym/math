"""Exact rational rejection of an overly strong general Schur certificate.
This counterexample is INSIDE a qubit sector where actual Q_k>=0.
It is therefore explicitly not a distillation/N0 counterexample.
"""
from pathlib import Path
import sympy as sp, itertools, json, datetime
P=Path('/home/mxym/math-breadth-quantum-20261015/research/breadth-quantum-20261015')
d=2;k=3;n=8
digits=list(itertools.product(range(d),repeat=k))
index={a:i for i,a in enumerate(digits)}
R=sp.zeros(n*n)
for a,b in itertools.product(digits,repeat=2):
    row=index[a]*n+index[b]
    for subset in itertools.product([0,1],repeat=k):
        aa=tuple(b[i] if subset[i] else a[i] for i in range(k));bb=tuple(a[i] if subset[i] else b[i] for i in range(k))
        R[row,index[aa]*n+index[bb]]+=(-sp.Rational(1,2))**sum(subset)

# u=(001+010+100)/sqrt(3); factors of sqrt(3) cancel in M.
support=[index[x] for x in [(0,0,1),(0,1,0),(1,0,0)]]
block=lambda a,b:R[a*n:(a+1)*n,b*n:(b+1)*n]
A=sum((block(a,b) for a in support for b in support),sp.zeros(n))/3
Ai=A.inv()
L=[sum((block(a,b) for a in support),sp.zeros(n)) for b in range(n)]
M=sp.zeros(n*n)
for a,b in itertools.product(range(n),repeat=2):
    M[b*n:(b+1)*n,a*n:(a+1)*n]=L[a]*Ai*L[b].T/3
C=R-M

w=sp.zeros(n*n,1);entries=[]
# Six pairs: first string has weight2, second weight1, with a common1.
for a,b in itertools.product(digits,repeat=2):
    if sum(a)==2 and sum(b)==1:
        value=4 if sum(x*y for x,y in zip(a,b))==1 else 1
        w[index[a]*n+index[b]]=value;entries.append({'first':a,'second':b,'coefficient':value})
w[index[(1,1,1)]*n+index[(0,0,0)]]=1
entries.append({'first':[1,1,1],'second':[0,0,0],'coefficient':1})
qR=(w.T*R*w)[0];qM=(w.T*M*w)[0];qC=(w.T*C*w)[0]
assert qC==-2,(qR,qM,qC)
assert C==C.T
out={'schema':'exact-strong-certificate-rejection-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'local_dimension':2,'resource_slots':3,'u_support':[[0,0,1],[0,1,0],[1,0,0]],'u_normalization':'1/sqrt(3)','w_entries':entries,'w_squared_norm':str((w.T*w)[0]),'w_R_w':str(qR),'w_Mhat_w':str(qM),'w_coChoi_deficit_w':str(qC),'exact_arithmetic':'SymPy rationals; actual dimension64 co-Choi matrix, no rounded eigenvector used in final witness','physical_interpretation':'This refutes only universal complete-copositivity of the switched-Schur deficit. The underlying qubit W2 is PSD, so actual endpoint distillation expectation is nonnegative for every coefficient rank, all copy counts. No N0 or Werner rank-two counterexample is claimed.','qutrit_embedding':'The same witness embeds into qubit supports inside local dimension3.','complete_target_solved':False}
(P/'SWITCHED_EXACT_REJECTION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
