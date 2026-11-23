"""Verify the signed mass decks for a forced 42/43-site three-source configuration.
Pure Python 3.10+, no data input, no graph search. Q masks in binary index order,
lowest bit belongs to source 1. h is the population on q-positive sites."""
from itertools import product, permutations
from collections import Counter

def decks():
    raw=[]
    for d in (0,1):
        for r in range(2+d):
            m=(1+d-r,3+r,3-d+r,4-r,3-d+r,4-r,4+d-r,r)
            for a,b,c,k in product(*(range(m[i]+1) for i in (3,5,6,7))):
                for ell in product((5,6),repeat=3):
                    sig=tuple(2*l-11 for l in ell)
                    h=[0,ell[0]-a-b-k,ell[1]-a-c-k,a,ell[2]-b-c-k,b,c,k]
                    h[0]=11-sum(h);h=tuple(h)
                    if any(t<0 or t>s for t,s in zip(h,m)): continue
                    for f in ((0,) if not d else (-1,1)):
                        for i,j in ((0,1),(0,2),(1,2)):
                            extra,eps=(d,f) if i==1 else (0,0)
                            u=2*(h[(1<<i)|(1<<j)]+k)-4-extra
                            if u-eps not in (0,2*sig[i]) or u+eps not in (0,2*sig[j]): break
                        else: raw.append((d,f,m,h))
    return raw

def canonical(z):
    d,f,m,h=z; out=[]
    for p in (permutations(range(3)) if not d else ((0,1,2),(0,2,1))):
        for sign,swap in product((0,1),repeat=2):
            M=[0]*8; H=[0]*8
            for i in range(8):
                j=7*swap
                for a in range(3): j^=(i>>a&1)<<p[a]
                M[j]=m[i]; H[j]=m[i]-h[i] if sign else h[i]
            F=f*(-1)**(sign+swap+(p[1]==2))
            out.append((d,F,tuple(M),tuple(H)))
    return min(out)


def elementary(z):
    """Two direct graph obstructions: q opposite degree 4; 4-site slots."""
    d,f,m,h=z; V=[]
    for g in (1,-1):
        for k in range(8):
            V += [(g,)+(tuple(g*(k>>j&1) for j in range(3)))]*(h[k] if g==1 else m[k]-h[k])
    sigma=[sum(x[0] for x in V if x[j+1]) for j in range(3)]
    for g in (1,-1):
        for j in range(3):
            both=(d+g*f)//2 if j==1 else (d-g*f)//2 if j==2 else 0
            V += [(0,)+tuple(g*int(j==k) for k in range(3))]*((7-g*sigma[j])//2-both)
        V += [(0,0,g,-g)]*((d+g*f)//2)
    V += [(0,0,0,0)]*(99-len(V))
    def marks(v):
        q,a,b,c=v
        return (q,a,b,c,q-a,q-b,q-c,a+b-q,a+c-q,b+c-q)
    X=list(map(marks,V)); possible=lambda i,j: all(t*u<=0 for t,u in zip(X[i],X[j]))
    if any(sum(1 for j,y in enumerate(V) if y[0]==-x[0] and possible(i,j))<4
           for i,x in enumerate(V[:22])): return False
    # If S of size >=4 is contained in aligned sign sides with disjoint opposite
    # targets T1,T2, every 4-subset needs 16 neighbors-with-multiplicity in
    # each. Looking only at T1=9,T2=11, one impossible target leaves <=19
    # possible sites altogether, needing >=32-19=13 pair incidences >12.
    for i in range(1,7):
        for j in (0,7,8,9):
            for s,t in product((1,-1),repeat=2):
                A=[v for v in range(99) if X[v][i]==s and X[v][j]==t]
                if len(A)<4 or any(y[i]==-s and y[j]==-t for y in X): continue
                for v,y in enumerate(X):
                    if (y[i]==-s or y[j]==-t) and sum(not possible(v,w) for w in A)>=4: return False
    return True

if __name__=='__main__':
    raw=decks(); full=set(map(canonical,raw))
    assert Counter(z[0] for z in raw)=={0:48,1:128}
    assert Counter(z[0] for z in full)=={0:4,1:17}
    good={z for z in full if all(z[3][j]<=1 and z[2][j]-z[3][j]<=1 for j in (0,7))}
    assert Counter(z[0] for z in good)=={0:4,1:13}
    final=set(filter(elementary,good))
    assert Counter(z[0] for z in final)=={0:4,1:10}
    for z in sorted(final): print(*z)
    print("raw signed decks 48/128; canonical 4/17; after norm-34 tests 4/13; after elementary graph cuts 4/10")
