"""Exact example and algebraic checkpoints for the universal rational qutrit path. Python stdlib."""
from fractions import Fraction as F
from itertools import product
def ok(v,msg):
    if not v:raise ArithmeticError(msg)
    print('PASS:',msg)
I=[[int(i==j) for j in range(3)] for i in range(3)]
J=[[0,-1,1],[1,0,-1],[-1,1,0]]
def tr(m):return [list(u) for u in zip(*m)]
def mm(a,b): return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
def mat(q):
    s=1+3*q*q;J2=mm(J,J)
    return [[I[i][j]+(2*q*J[i][j]+2*q*q*J2[i][j])/s for j in range(3)] for i in range(3)]
def det(m):
    m=[[F(x) for x in row]for row in m];p=F(1)
    for i in range(len(m)):
        j=next((j for j in range(i,len(m)) if m[j][i]),None)
        if j is None:return F(0)
        if j!=i:m[j],m[i]=m[i],m[j];p=-p
        v=m[i][i];p*=v
        for j in range(i+1,len(m)):
            c=m[j][i]/v;m[j]=[a-c*b for a,b in zip(m[j],m[i])]
    return p
def kern(u,v):return [u[i]*v[i] for i in range(3)]+[u[i]*v[j]+u[j]*v[i] for i,j in [(0,1),(1,2),(2,0)]]
def props(t,lam):
    mats=[I,mat((1-t)*(1-2*t)),mat((1-t)*(6*t-1))]
    assert all(mm(m,tr(m))==I and det(m)==1 for m in mats)
    # u[x][a] is a COLUMN
    u=[tr(m) for m in mats]
    minors=[det([u[c[a]][a] for a in range(3)]) for c in product(range(3), repeat=3)]
    lin=det([kern(u[0][a],u[j][a]) for j in (1,2) for a in range(3)])
    def inner(v,w):return sum(l*i*j for l,i,j in zip(lam,v,w))
    ratios=[]
    for a in range(3):
        for j,k in [(0,1),(1,2),(2,0)]:
            v,w=u[j][a],u[k][a]
            ratios.append(inner(v,w)**2/(inner(v,v)*inner(w,w)))
    return minors,lin,ratios,mats
for ts in [(0,1),(1,1),(1,2),(1,1000)]:
    t=F(*ts);m,d,q,U=props(t,[F(1,6),F(2,6),F(3,6)])
    if t==0:ok(all(not z for z in q),'base cyclic shifts; all posterior overlaps zero')
    if t==1:ok(all(z==1 for z in m),'endpoint I,I,I: all 27 transversal determinants one')
    if t==F(1,2):ok(abs(d)==1,'midpoint I,I,C: six identifiability constraints form coordinate basis')
    if t==F(1,1000):
        ok(all(z!=0 for z in m),'t=1/1000: every transversal is nonsingular')
        ok(d!=0,'t=1/1000: six real Gram constraints have rank six')
        ok(all(0<4*z<1 for z in q),'t=1/1000, Schmidt probabilities (1,2,3)/6: all 9 squared inner products strictly between 0 and 1/4')
        ok(all(mm(m,tr(m))==I and det(m)==1 for m in U),'three rotation matrices are exactly orthogonal and special')
