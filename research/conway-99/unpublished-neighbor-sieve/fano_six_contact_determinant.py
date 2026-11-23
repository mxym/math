"""Original Fano local cubic test. NumPy integer arithmetic; exhaustive 512 six-site masks. The full 39/40 Gram replay takes a second."""
import numpy as np,itertools as it
from collections import Counter
# duplicate pairs (0,1),(2,3),(4,5); mates (1,2),(3,4),(5,0), so each mixed sign
pairs=list(it.combinations(range(6),2))
E=[(a,b) for a,b in pairs if (b-a)%6 not in (1,5)]
D=np.array([[int(a==2*b)-int(a==2*b+1) for b in range(3)] for a in range(6)],dtype=np.int64)
def four(H):
    hh=np.zeros((4,4),dtype=np.int64)
    hh[:3,:3]=9*np.eye(3,dtype=np.int64)+3-D.T@H@D
    vv=D.T@H@np.ones(6,dtype=np.int64)
    hh[:3,3]=hh[3,:3]=vv;hh[3,3]=-H.sum()
    return hh
def det(G):
    def sn(p):return (-1)**sum(p[i]>p[j] for i,j in it.combinations(range(len(p)),2))
    return int(sum(sn(p)*np.prod(G[range(len(G)),p]) for p in it.permutations(range(len(G)))))%7
def graph(code):
    A=np.zeros((6,6),dtype=np.int64)
    for i,(a,b) in enumerate(E):
        if code>>i&1:A[a,b]=A[b,a]=1
    return A
def caps_ok(A):
    # fixed six degrees to cap side, need simple 4-cap cubic complement
    v=(3-A.sum(axis=1));m=int(A.sum())//2-3
    if not 0<=m<=6:return False
    for eb in it.combinations(it.combinations(range(4),2),m):
        deg=[3]*4
        for i,j in eb:deg[i]-=1;deg[j]-=1
        if min(deg)<0 or sum(deg)!=sum(v):continue
        # bipartite degree graphical by Gale-Ryser
        if all(sum(sorted(v,reverse=True)[:k])<=sum(min(k,j) for j in deg) for k in range(1,7)):return True
    return False
def complete(A):
    v=3-A.sum(axis=1);m=int(A.sum())//2-3
    for eb in it.combinations(it.combinations(range(4),2),m):
        deg=[3]*4
        for i,j in eb:deg[i]-=1;deg[j]-=1
        if min(deg)<0 or sum(deg)!=sum(v):continue
        def aug(t):
            if t==6:return [] if not any(deg) else None
            for j in it.combinations([i for i in range(4) if deg[i]],int(v[t])):
                for k in j:deg[k]-=1
                got=aug(t+1)
                for k in j:deg[k]+=1
                if got is not None:return [(t,k+6) for k in j]+got
        got=aug(0)
        if got is not None:
          return [(i,j) for i,j in E if A[i,j]]+[(i+6,j+6) for i,j in eb]+got
def corecalc(ed):
    A=np.zeros((39,39),dtype=np.int64)
    def add(i,j):A[i,j]=A[j,i]=1
    for i in range(7):
      for j in range(7):
        if ((i+1)&(j+1)).bit_count()%2:add(i,7+j)
    for i,j in enumerate((2,2,4,4,6,6,1,3,5,7)):
        add(0,29+i);add(7+j-1,29+i)
    for i,j in ((1,2),(3,4),(5,0)):add(29+i,29+j)
    for k,(i,j) in enumerate(ed):
        add(14+k,29+i);add(14+k,29+j)
    return 3*np.eye(39,dtype=np.int64)-A+4
def rankcols(G):
    a=G.copy()%7;n=len(G);i=0;cols=[]
    for j in range(n):
        hs=np.flatnonzero(a[i:,j])
        if not len(hs):continue
        v=i+hs[0];a[[i,v]]=a[[v,i]]
        a[i]=a[i]*pow(int(a[i,j]),-1,7)%7
        col=a[:,j].copy();col[i]=0;a=(a-col[:,None]*a[i])%7
        i+=1;cols.append(j)
    return cols
import numpy as np
ALL=(1<<18)-1
def matinv(G):
    a=np.concatenate((G%7,np.eye(len(G),dtype=np.int64)),axis=1)
    det=1
    for j in range(len(G)):
        hits=np.flatnonzero(a[j:,j])
        if not len(hits):return None
        v=j+hits[0];a[[j,v]]=a[[v,j]];det=det*int(a[j,j])*(-1 if v!=j else 1)%7
        a[j]=a[j]*pow(int(a[j,j]),-1,7)%7
        col=a[:,j].copy();col[j]=0;a=(a-col[:,None]*a[j])%7
    return (det,a[:,len(G):])
if __name__=='__main__':
    ranks=Counter(); plain=Counter(); populations=Counter(); surviving=[]; squares=(1,2,4)
    for k in range(512):
        H=graph(k)
        if not caps_ok(H):continue
        M=four(H);A=corecalc(complete(H));ii=rankcols(M);I=rankcols(A)
        assert len(I)==32+len(ii)
        plain[len(I),matinv(A[np.ix_(I,I)])[0] not in squares]+=1
        if len(ii)==4:assert (det(M) in squares)==(matinv(A[np.ix_(I,I)])[0] in squares)
        G=np.zeros((40,40),dtype=np.int64);G[:39,:39]=A;G[-1,-1]=2
        G[-1,:7]=G[:7,-1]=1;G[-1,7:14]=G[7:14,-1]=-1
        M[3,3]-=3
        ii=rankcols(M);I=rankcols(G)
        assert len(I)==33+len(ii)
        dm=matinv(M[np.ix_(ii,ii)])[0];dg=matinv(G[np.ix_(I,I)])[0]
        if len(ii)==3:assert (dm in squares)==(dg not in squares)
        ranks[len(I),dg not in squares]+=1
        if len(I)<36 or (len(I)==36 and dg not in squares):
            surviving.append(k);populations[int(H.sum())//2]+=1
    T=A[:29,:29];si=rankcols(T);d0,R=matinv(T[np.ix_(si,si)]);f=np.r_[np.ones(7,int),-np.ones(7,int),np.zeros(15,int)]
    co=f[si]@R%7
    assert len(si)==22 and d0 not in squares and np.all((co@T[si,:]-f)%7==0) and (2-co@f[si])%7==1
    assert plain[36,False]==185 and plain[36,True]==217 and sum(plain.values())==466
    assert ranks=={(37,True):256,(37,False):166,(36,True):32,(36,False):12}
    assert populations=={4:12,5:18,6:1,9:1}
    print('Cubic completions:',sum(ranks.values()),'; original rank36 survivors:',len(surviving),'; H edge counts:',dict(populations))
    print('Surviving masks:',surviving)
