"""Exact graph/7-adic obstruction for disconnected triangle wings. Standard library.
Place beside twelve_sites.py and run python3 triangle_wing_twelve_currents.py.
"""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from twelve_sites import MATES, CERTIFICATES, chart, connected, multiplicities, code


def determinant(a):
    a=[r[:] for r in a];prev=1;sign=1
    for i in range(len(a)-1):
        p=next((j for j in range(i,len(a)) if a[j][i]),None)
        if p is None:return 0
        if p!=i:a[i],a[p]=a[p],a[i];sign=-sign
        v=a[i][i]
        for j in range(i+1,len(a)):
            for k in range(i+1,len(a)):
                n=v*a[j][k]-a[j][i]*a[i][k]
                assert n%prev==0
                a[j][k]=n//prev
        prev=v
    return sign*a[-1][-1]


def kernel(a):
    A=[[v%7 for v in r] for r in a];m=len(A);n=len(A[0]);piv=[]
    for j in range(n):
        t=len(piv);r=next((i for i in range(t,m) if A[i][j]),None)
        if r is None:continue
        A[t],A[r]=A[r],A[t];inv=pow(A[t][j],-1,7)
        A[t]=[v*inv%7 for v in A[t]]
        for i in range(m):
            if i!=t:
                q=A[i][j];A[i]=[(v-q*u)%7 for v,u in zip(A[i],A[t])]
        piv.append(j)
    B=[]
    for f in sorted(set(range(n))-set(piv)):
        x=[0]*n;x[f]=1
        for i,j in enumerate(piv):x[j]=-A[i][f]%7
        B.append(tuple(x))
    return B


def rank_sign(a):
    A=[[v%7 for v in r] for r in a];rank=0;det=1
    while any(any(r) for r in A):
        n=len(A);j=next((i for i in range(n) if A[i][i]),None)
        if j is None:
            i,j=next((i,j) for i,j in combinations(range(n),2) if A[i][j])
            A[i]=[(v+w)%7 for v,w in zip(A[i],A[j])]
            for k in range(n):A[k][i]=(A[k][i]+A[k][j])%7
            j=i
        A[0],A[j]=A[j],A[0]
        for r in A:r[0],r[j]=r[j],r[0]
        d=A[0][0];rank+=1;det=det*d%7;di=pow(d,-1,7)
        A=[[(A[i][j]-A[i][0]*di*A[0][j])%7 for j in range(1,n)] for i in range(1,n)]
    return rank,(1 if det in (1,2,4) else -1)


def labelsum(pair,v):return (v[pair[0]]+v[pair[1]])%7


def line(a):return tuple(x*pow(next(z for z in a if z),-1,7)%7 for x in a)


def inventory():
    charts={}
    for q,r,f in product(MATES,MATES,permutations(range(4))):
        p=MATES[0],q,r,f;g=chart(*p)
        if connected(g) and min(multiplicities(g).values())>=0:charts.setdefault(code(p),p)
    assert len(charts)==15
    bad={code(p) for p in CERTIFICATES}
    assert len(bad)==2
    types=[];special={}
    for key,p in charts.items():
        if key in bad:continue
        g=chart(*p);L=[[3*int(i==j)-int(j in g[i]) for j in range(12)] for i in range(12)]
        tau=determinant([r[:-1] for r in L[:-1]])
        D=[[L[i][j]-L[i][-1]-L[-1][j]+L[-1][-1] for j in range(11)] for i in range(11)]
        n,s=rank_sign(D);k=kernel(L+[[1]*12]);assert n+len(k)==11
        E={pair:m for pair,m in multiplicities(g).items() if m}
        # Every signed-current vector is visible, independent of the unknown exterior.
        incidence=[[int(i in e) for i in range(12)] for e in E]
        assert not kernel(incidence)
        if not k:
            assert s==(1 if tau%7 in (1,2,4) else -1);types.append(('U',s))
        else:
            name={7350:'A',7140:'B'}[tau];assert (len(k),s)=={'A':(2,1),'B':(1,-1)}[name]
            types.append((name,s));special[name]=(E,k)
    assert Counter(types)=={('U',1):6,('U',-1):5,('A',1):1,('B',-1):1}
    return types,special


def vecs(B):
    return {tuple(sum(z*x[i] for z,x in zip(v,B))%7 for i in range(12))
            for v in product(range(7),repeat=len(B)) if any(v)}


def cross(E,F,p,vals,vals2):
    E0=list(E);F0=list(F);ne,nf=len(E0),len(F0);O=ne+nf
    h,k=Counter(),Counter()
    for e,t in zip(E0,vals):h[t]+=E[e]
    for f,u in zip(F0,vals2):k[u]+=F[f]
    if h!=k:return 'hist'
    rhs=list(E.values())+list(F.values())+[2-int(i//4==p[j//4]) for i in range(12) for j in range(12)]
    available=[0]*len(rhs);bas={}
    for ei,(e,t) in enumerate(zip(E0,vals)):
        for fi,(f,u) in enumerate(zip(F0,vals2)):
            if t!=u:continue
            if max(Counter([i//4 for i in e]+[p[j//4] for j in f]).values())>2:continue
            rows=(ei,ne+fi,*(O+12*i+j for i in e for j in f))
            for r in rows:available[r]+=1
            w=sum(1<<r for r in rows)
            while w and w.bit_length() in bas:w^=bas[w.bit_length()]
            if w:bas[w.bit_length()]=w
    if any(a<b for a,b in zip(available,rhs)):return 'cell'
    b=sum((v%2)<<i for i,v in enumerate(rhs))
    while b and b.bit_length() in bas:b^=bas[b.bit_length()]
    return 'parity' if b else 'pass'


def run():
    types,D=inventory();p3=list(permutations(range(3)))
    for a,b in (('A','B'),('B','B')):
        E,K=D[a];F,L=D[b];result=Counter()
        for h in sorted(set(map(line,vecs(K)))):
            for k in vecs(L):
                V=[labelsum(e,h) for e in E];W=[labelsum(f,k) for f in F]
                for p in p3:result[cross(E,F,p,V,W)]+=1
        assert not result['pass']
        print(a+b,sorted(result.items()))
    E,K=D['A'];V=[tuple(labelsum(e,h) for h in K) for e in E]
    H=Counter()
    for e,v in zip(E,V):H[v]+=E[e]
    res=Counter()
    for a,b,c,d in product(range(7),repeat=4):
        if (a*d-b*c)%7==0:continue
        U=[((a*x+b*y)%7,(c*x+d*y)%7) for x,y in V];G=Counter()
        for e,u in zip(E,U):G[u]+=E[e]
        if G!=H:res['hist']+=6;continue
        for p in p3:res[cross(E,E,p,V,U)]+=1
    assert res=={'hist':12024,'cell':72}
    print('AA entire evaluation planes',sorted(res.items()))
    cuts=Counter()
    for triple in combinations_with_replacement(types,3):
        names=[v[0] for v in triple];a,b=names.count('A'),names.count('B')
        # Lower bound on the union of evaluated radical spaces, not sum in general.
        s=max([0]+([1] if b else [])+([2] if a or b>=2 else [])+([3] if a>=2 or (a and b) else []))
        d=2*a+b;ell=34-d;rank=ell+2*s
        ds=triple[0][1]*triple[1][1]*triple[2][1]
        if rank>36 or (rank==36 and ds*(-1)**s!=-1):cuts[''.join(sorted(names))]+=1
    assert cuts=={'AUU':36,'ABU':11,'BBU':6,'AAU':5}
    print(sum(cuts.values()),'of 455 previously retained connected 12+12+12 multisets',dict(cuts))


if __name__=='__main__':run()
