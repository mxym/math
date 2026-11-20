"""Integer, zero-tolerance verification. Q(w), w^2+w+1=0. No third-party packages."""
from itertools import combinations_with_replacement,permutations
from collections import defaultdict
import json,os,sys
O=(0,0); one=(1,0);om=(0,1);v=(1,2) # w-wbar
def add(x,y):return x[0]+y[0],x[1]+y[1]
def neg(x):return -x[0],-x[1]
def sub(x,y):return add(x,neg(y))
def bar(x):return x[0]-x[1],-x[1]
def mul(x,y):
    a,b=x;c,d=y;return a*c-b*d,a*d+b*c-b*d
def sc(k,x):return k*x[0],k*x[1]
def sumv(xs):
    y=O
    for x in xs:y=add(x,y)
    return y
W=(one,om,(-1,-1))
def dag(M):return [[bar(x) for x in a] for a in zip(*M)]
def kmat(M):return [[mul(M[i//3][j//3],M[i%3][j%3]) for j in range(9)] for i in range(9)]
def herm(M,kind):return [[add(M[i][j],dag(M)[i][j]) if kind==0 else mul(v,sub(M[i][j],dag(M)[i][j])) for j in range(9)] for i in range(9)]
M0=kmat([[sc(7,W[-i%3]) if i==j else O for j in range(3)] for i in range(3)])
# 7 Z* B = Z^2 (7H) Z^2
MB=kmat([[mul(W[-(i+j)%3],(3,1) if i==j else (-4,1)) for j in range(3)]for i in range(3)])
S=lambda a:3*(a%3)+a//3
T=lambda a:3*((a//3+1)%3)+(a%3+1)%3
Ms=[herm(m,d)for m in (M0,MB) for d in (0,1)]+[[[sc(49*(3*int(i==S(j))-int(i==j)),one) for j in range(9)]for i in range(9)]]
terms=json.load(open(os.path.join(os.path.dirname(__file__),sys.argv[1] if len(sys.argv)>1 else 'witness21.json')))['terms']
# Build twice the F-averaged T; a global factor, and the common 49, are harmless.
ts=[[[O for j in range(9)]for i in range(9)]for k in range(5)]
for k,a,b,h,c in terms:
    for p,q in ((a,b),(S(a),S(b))):
        y=sc(c,v if h else one);ts[k][p][q]=add(ts[k][p][q],y)
        if p!=q:ts[k][q][p]=add(ts[k][q][p],bar(y))
# Coefficient at |a,c><b,d| of sum M tensor T, after unnormalized C3-twirl.
def coeff(a,c,b,d):
    x=O
    for j in range(3):
        x=add(x,sumv(mul(m[a][b],t[c][d]) for m,t in zip(Ms,ts)))
        a,c,b,d=T(a),T(c),T(b),T(d)
    return x
# Real unnormalized common eigenvectors for F and D tensor D.
basis=[];charges=[];sgn=[]
for f in (0,1):
    for a in range(3):
        for b in range(a+f,3):
            basis.append([(3*a+b,1)] if a==b else [(3*a+b,1),(3*b+a,(-1)**f)])
            charges.append((2**a+2**b)%7);sgn.append(f)
# Group by (charge,total antisymmetric count), i.e. average over C7 and relative phase.
sectors=defaultdict(list)
for i,j in combinations_with_replacement(range(9),2):
    vec=defaultdict(int)
    for k,l in ([(i,j)] if i==j else [(i,j),(j,i)]):
        for a,x in basis[k]:
            for c,y in basis[l]:vec[a,c]+=x*y
    sectors[(charges[i]+charges[j])%7,sgn[i]+sgn[j]].append(vec)
def det(A):
    n=len(A)
    if n==0:return one
    return sumv(sc((-1)**j,mul(A[0][j],det([r[:j]+r[j+1:] for r in A[1:]]))) for j in range(n))
nn=0;md=10**100
for tag,vecs in sorted(sectors.items()):
    block=[[sumv(sc(i*j,coeff(a,c,b,d)) for (a,c),i in v1.items() for (b,d),j in v2.items()) for v2 in vecs]for v1 in vecs]
    if block!=dag(block): raise ValueError("non-Hermitian block",tag)
    vals=[det([r[:j] for r in block[:j]]) for j in range(1,len(block)+1)]
    if not all(v[1]==0 and v[0]>0 for v in vals): raise ValueError("bad minor",tag,vals)
    ns=[v[0] for v in vals];md=min(md,*ns);nn+=len(ns)
    print(tag,ns)
if nn!=45 or md!=290: raise ValueError("unexpected counts",nn,md)
print('45 positive leading principal minors; smallest positive integer',md)
