"""Independent exact checks using point/line incidence, plus F4 code fibers."""
from math import comb
from itertools import product, combinations_with_replacement
from collections import Counter, defaultdict
def ck(v,tag):
    if not v: raise ArithmeticError(tag)
def mw(a,b):
    # F4 as F2[z]/(z^2+z+1)
    s=0
    while b:
        if b&1:s^=a
        a <<=1
        if a&4:a^=7
        b>>=1
    return s
def hist(n,k):
    if k==1:yield (n,);return
    for j in range(n+1):
        for tail in hist(n-j,k-1):yield (j,)+tail

def diag(q,d,t):
    # No general-purpose Gaussian elimination or rank tables.
    L=(q**d-1)//(q-1);n=t*L
    if d==3: # only Fano plane here, line normal u
        lines=[[v-1 for v in range(1,8) if (v&u).bit_count()%2==0] for u in range(1,8)]
    def slices(h):
        z=h[0];m=h[1:]
        out=[]
        for k in range(n+1):
            b=lambda j:comb(j,k) if j>=k else 0
            total=b(n);P0=b(z);r1=sum(b(z+x) for x in m)-L*P0 # exact rank-one subset count
            if d==2:out.append(2*(total-P0)-r1)
            else:
                r2=sum(b(z+sum(m[i] for i in H)) for H in lines)-(q+1)*r1-L*P0
                out.append(3*(total-P0)-2*r1-r2)
        return out
    opt=(0,)+(t,)*L;u=slices(opt);num=0;total=0
    for h in hist(n,L+1):
        total+=1;v=slices(h)
        if v[n]!=d:continue
        num+=1;g=[a-b for a,b in zip(u,v)]
        # Nonnegative Bernstein coefficients certify all probabilities for THESE cases only.
        ck(min(g)>=0 and (max(g)==0)==(h==opt),'finite coefficientwise order')
    ck(total==comb(n+L,L),'exhaustion')
    print('GF',q,'d/t',d,t,'tested',num,'spanning histograms of',total)
def fibers():
    # Unnormalized, nontrivially scaled representative of every F4 projective line plus alternatives.
    # Distinct A annihilating an observation exactly count all possible cosets, not pairwise ranks.
    for columns in [[(0,2),(1,0),(3,3),(2,mw(2,2)),(1,3)],[(0,0),(3,0),(2,0),(3,2),(1,1)]]:
        n=len(columns);V=list(product(range(4),repeat=n))
        code=[tuple(mw(a,i)^mw(b,j) for i,j in columns) for a,b in product(range(4),repeat=2)]
        def dot(x,y):
            s=0
            for a,b in zip(x,y):s ^=mw(a,b)
            return s
        dual=[v for v in V if all(dot(v,x)==0 for x in code)]
        ck(len(set(code))==16 and len(dual)==4**(n-2),'dimensions')
        # Label cosets by evaluation on dual (redundancy is harmless).
        lab={v:tuple(dot(v,b) for b in dual) for v in V}
        ck(len(set(lab.values()))==4**(n-2),'lab')
        for s in range(1<<n):
            obs=lambda v:tuple(val for j,val in enumerate(v) if s>>j&1)
            cm=lambda v:tuple(val for j,val in enumerate(v) if not (s>>j&1))
            rows=defaultdict(Counter)
            for v in V:rows[obs(v)][lab[v]]+=1
            numpr=len(set(map(obs,code)));numco=len(set(map(cm,code)))
            ck(len(set(map(obs,dual)))*len(code)==4**s.bit_count()*numco,'dual')
            ck(all(len(set(counts.values()))==1 and len(counts)*4**s.bit_count()==4**(n-2)*numpr for counts in rows.values()),'fiber')
    print('GF4 cosets and duals passed on 64 physical subsets (both layouts).')
if __name__=='__main__':
    diag(4,2,1);diag(4,2,2);diag(2,3,1);fibers()
