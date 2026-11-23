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

if __name__=='__main__':
    raw=decks(); full=set(map(canonical,raw))
    assert Counter(z[0] for z in raw)=={0:48,1:128}
    assert Counter(z[0] for z in full)=={0:4,1:17}
    good={z for z in full if all(z[3][j]<=1 and z[2][j]-z[3][j]<=1 for j in (0,7))}
    assert Counter(z[0] for z in good)=={0:4,1:13}
    for z in sorted(good): print(*z)
    print("raw signed decks 48/128; canonical 4/17; after norm-34 tests 4/13")
