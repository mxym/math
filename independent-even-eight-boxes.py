from itertools import combinations,permutations
from math import isqrt,comb
from fractions import Fraction as F
import json,sys,hashlib

if not __debug__: raise RuntimeError("run without -O")
EXPECTED = ((40,80,224,193,130,5,14,28),(168,112,224,65,130,7,14,21),(56,112,224,193,131,7,14,28))
n=8;K=4096;D=4*K**4;E=list(combinations(range(n),2));ix={e:j for j,e in enumerate(E)}
counts=[];stack=[];matrix_count=0
def ceil_sqrt(x):
    a=isqrt(x)
    return a+(a*a<x)
def angles(A,B):
    Q=[[-K]*16 for i in range(16)]
    for i in range(16):Q[i][i]=K
    for (i,j),a,b in zip(E,A,B):
        Q[i][j]=Q[j][i]=Q[i+8][j+8]=Q[j+8][i+8]=a
        Q[i][j+8]=Q[j+8][i]=Q[i+8][j]=Q[j][i+8]=-b
    for u in range(16):
        v=Q[u][:]
        for i in range(16):
            for j in range(16):
                if v[i]+v[j]<0:continue
                c=(v[i]*v[j]-ceil_sqrt((K*K-v[i]**2)*(K*K-v[j]**2)))//K
                Q[i][j]=max(Q[i][j],c)
    A=[Q[i][j] for i,j in E];B=[-Q[i][j+8] for i,j in E]
    if any(a>b for a,b in zip(A,B)) or any(Q[j][j+8]>-K for j in range(8)):return None
    return A,B

def affine_majorizes(L,U,S,B):
    p=lambda x:4*x**4-K*K*x*x-S*x-B
    assert p(L)<=0 and p(U)<=0
    if U==L:return
    if (U<=0 and 24*U*U>=K*K) or (L>=0 and 24*L*L>=K*K):return
    if S==0:
        assert not (L<=0<=U) or p(0)<=0
        return
    coefficients=[-B,-S,-K*K,0,4]
    for j in range(4):
        a=L+(U-L)*j//4;b=L+(U-L)*(j+1)//4
        z=[(b-a)**t*sum(coefficients[k]*comb(k,t)*a**(k-t) for k in range(t,5)) for t in range(5)]
        bern=[sum(F(z[t]*comb(i,t),comb(4,t)) for t in range(i+1)) for i in range(5)]
        assert max(bern)<=0, (L,U,S,B,bern)

def dual_bound(A,B,S,T,weights,orders,tests,tar,allowed):
    total=F(0); constants=F(0); coefficient=[F(0)]*len(E)
    for t,w in weights:
        assert t>=0 and len(w)==8 and min(w)>=0 and sum(w)==600
        total+=t;constants+=F(3*t*sum(q*q for q in w),4*600**2)
        for z,(i,j) in enumerate(E):
            h=F(2*t*w[i]*w[j],600**2*D)
            constants+=h*T[z];coefficient[z]+=h*S[z]
    for t,a,b in orders:
        assert t>=0 and (a,b) in allowed
        coefficient[a]+=F(t,K); coefficient[b]-=F(t,K)
    for t,v in tests:
        assert t>=0 and len(v)==8
        constants+=t*sum(z*z for z in v)
        for j,(a,b) in enumerate(E):
            coefficient[j]+=F(2*t*v[a]*v[b],K)
    U=constants+sum(max(a*c,b*c) for a,b,c in zip(A,B,coefficient))
    if total:
        assert U<=F(tar,10**6)*total
    else:
        assert U<0

def sym_expected(G,chief):
    possible=[]
    for p in permutations(range(n)):
        if any((G[i]>>j&1)!=(G[p[i]]>>p[j]&1) for i,j in E):continue
        possible.append(tuple(ix[tuple(sorted([p[i],p[j]]))] for i,j in E))
    ss=[j for j,(a,b) in enumerate(E) if G[a]>>b&1]
    order=ss+[j for j in range(len(E)) if j not in ss]
    if chief is not None:order=[chief]+[j for j in order if j!=chief]
    S=set()
    for a in order:
        S|={(a,s[a]) for s in possible if s[a]!=a}
        possible=[s for s in possible if s[a]==a]
    return S

H=hashlib.sha256()
for ln in sys.stdin:
    if not ln.startswith('AUD '):continue
    H.update(ln.encode('utf8'))
    what,*X=json.loads(ln[4:])
    if what=='start':
        assert not stack
        G,order,chief,tar=X
        assert tar==187470 and tuple(G)==EXPECTED[matrix_count]
        assert set(map(tuple,order))==sym_expected(G,chief)
        if chief is not None:
            assert chief==ix[(0,4)]
            assert {a for b,a in order if b==chief}|{chief}=={ix[(i,i+4)] for i in range(4)}
        lo=[-K if G[i]>>j&1 else -K//2 for i,j in E]
        hi=[-K//2 if G[i]>>j&1 else K//2 for i,j in E]
        if chief is not None:lo[chief]=(-9*K)//10
        stack.append((lo,hi));matrix_count+=1
        counts.append([0,0,0,0]);continue
    A,B=stack.pop()
    cur=counts[-1]
    g=angles(A,B)
    if g is None:
        assert what=='sphere';cur[0]+=1;continue
    lo,hi=g
    for _ in range(2):
        for a,b in order:
            lo[a]=max(lo[a],lo[b]);hi[b]=min(hi[b],hi[a])
    if any(a>b for a,b in zip(lo,hi)):
        assert what=='order';cur[1]+=1;continue
    A,B,*data=X
    assert lo==A and hi==B
    if what=='split':
        a,t=data
        assert A[a]<t<B[a]
        left=lo[:];right=hi[:];left[a]=right[a]=t
        stack.append((left,hi));stack.append((lo,right))
        cur[2]+=1
    else:
        assert what=='close'
        S,T,W,O,V=data
        assert len(S)==len(T)==len(E)
        for a,b,c,d in zip(A,B,S,T):affine_majorizes(a,b,c,d)
        dual_bound(A,B,S,T,W,O,V,tar,set(map(tuple,order)))
        cur[3]+=1
assert matrix_count==3 and not stack
assert counts==[[0,0,15,16],[0,0,32,33],[0,0,49,50]]
print("independent exact closed-box verification",counts,"leaf transcript",H.hexdigest())
