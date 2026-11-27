"""Exact checks for the two clipping orientations and polynomial factorization."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import factorial
from random import Random

def law(weights):
    return [F(x,sum(weights)) for x in weights]

def tv_difference(v):
    return sum(abs(x) for x in v)

def cpoly(m):
    # Coefficients of pi times the normalized Chebyshev approximant.
    t=[[F(1)],[F(0),F(1)]]
    for k in range(2,2*m+1):
        u=[0]+[2*x for x in t[k-1]]
        for i,x in enumerate(t[k-2]): u[i]-=x
        t.append(u)
    c=[F(2)]+[F(0)]*(2*m)
    for j in range(1,m+1):
        a=F(4*(-1)**(j-1),4*j*j-1)
        for k,x in enumerate(t[2*j]): c[k]+=a*x
    return c

def dot(u,v):
    return sum(a*b for a,b in zip(u,v))

def evalp(c,x):
    out=F(0)
    for a in c[::-1]: out=out*x+a
    return out

def multiindexes(q,k):
    for a in combinations_with_replacement(range(q),k):
        multiplicity=factorial(k)
        for v in Counter(a).values(): multiplicity//=factorial(v)
        yield a,multiplicity

def mon(v,a):
    y=F(1)
    for i in a: y*=v[i]
    return y

def run_trial(seed):
    rng=Random(seed)
    q,na,nb=4,3,4
    pr=law([rng.randrange(1,11) for _ in range(q)])
    def prob(n):
        return law([1]+[rng.randrange(6) for _ in range(n-1)])
    p0=[prob(na) for _ in range(q)]
    p1=[prob(na) for _ in range(q)]
    qq=[prob(nb) for _ in range(q)]
    A=[list(map(lambda t:(t[0]+t[1])/2,zip(p0[r],p1[r]))) for r in range(q)]
    da=[[(u-v)/2 for u,v in zip(p0[r],p1[r])] for r in range(q)]
    pa=[sum(pr[r]*A[r][a] for r in range(q)) for a in range(na)]
    pb=[sum(pr[r]*qq[r][b] for r in range(q)) for b in range(nb)]
    pairs=[(a,b) for a in range(na) for b in range(nb) if pa[a] and pb[b]]
    direct=sum(abs(sum(pr[r]*da[r][a]*qq[r][b] for r in range(q))) for a,b in pairs)
    K=F(5,4) if seed%2 else F(2)
    U=[r for r in range(q) if r != seed%q]
    tau=sum(pr[r] for r in range(q) if r not in U)
    m=3
    c=cpoly(m)
    pi_hi,pi_lo=F(355,113),F(333,106)
    for alice_clipped in [True,False]:
        if alice_clipped:
            L=[[A[r][a]/pa[a] for r in range(q)] for a in range(na) if pa[a]]
            uu=[[da[r][a]/pa[a] for r in range(q)] for a in range(na) if pa[a]]
            ww=[[pr[r]*qq[r][b]/pb[b] for r in range(q)] for b in range(nb) if pb[b]]
            mm,nn=[p for p in pa if p],[p for p in pb if p]
        else:
            L=[[qq[r][b]/pb[b] for r in range(q)] for b in range(nb) if pb[b]]
            uu=L
            ww=[[pr[r]*da[r][a]/pa[a] for r in range(q)] for a in range(na) if pa[a]]
            mm,nn=[p for p in pb if p],[p for p in pa if p]
        uncut=sum(pm*pn*abs(dot(u,w)) for pm,u in zip(mm,uu) for pn,w in zip(nn,ww))
        assert uncut==direct and all(sum(map(abs,w))<=1 for w in ww)
        uc=[[u[r]*min(1,K/ell[r])/K if ell[r] else F(0) for r in U] for u,ell in zip(uu,L)]
        wc=[[w[r] for r in U] for w in ww]
        hc=sum(pr[r]*pm*max(0,ell[r]-K) for ell,pm in zip(L,mm) for r in range(q))
        cut=K*sum(pm*pn*abs(dot(u,w)) for pm,u in zip(mm,uc) for pn,w in zip(nn,wc))
        tail_only=sum(pm*pn*abs(sum(u[r]*w[r] for r in U))
                      for pm,u in zip(mm,uu) for pn,w in zip(nn,ww))
        assert abs(uncut-tail_only)<=tau and abs(cut-tail_only)<=hc
        assert all(all(abs(x)<=1 for x in u) for u in uc)
        scalar=K*sum(pm*pn*evalp(c,dot(u,w)) for pm,u in zip(mm,uc) for pn,w in zip(nn,wc))
        mf=F(0)
        for k,a in enumerate(c):
            for inds,mult in multiindexes(len(U),k):
                ucoef=sum(pm*mon(u,inds) for pm,u in zip(mm,uc))
                wcoef=sum(pn*mon(w,inds) for pn,w in zip(nn,wc))
                mf+=K*a*mult*ucoef*wcoef
        assert scalar==mf
        assert abs(mf-pi_hi*cut)<=2*K/(2*m+1)+K*(pi_hi-pi_lo)
    return 2

def clipping_negative_control():
    # Alice and Bob both reveal the seed; signed difference comes from
    # the one half of seeds on which Alice additionally transmits s.
    # Clipping Alice's joint likelihood from 4 to 1 suppresses the gap.
    q=4
    pr=[F(1,q)]*q
    h=sum(pr[r]*(1-F(1,q)) for r in range(q))
    d=F(1,2)
    clipped=d/q
    assert h==F(3,4) and d-clipped==F(3,8)>F(1,8)
    assert d-clipped<=h

def exact_perfect_protocol(n):
    N=1<<n
    n1=n0=0
    for x,y in product(range(N),repeat=2):
        full=[]
        for s in [0,1]:
            hist=Counter()
            for v,t in product(range(N),range(2)):
                a=s^((x&v).bit_count()%2)^t
                b=tuple(sorted(((v,t),(v^y,t^1))))
                hist[a,b]+=1
            full.append(hist)
        if (x&y).bit_count()%2:
            assert not full[0].keys()&full[1].keys()
            n1+=1
        else:
            assert full[0]==full[1]
            n0+=1
    assert n0+n1==N*N
    for x,v,t in product(range(N),range(N),range(2)):
        assert {(s^((x&v).bit_count()%2)^t) for s in [0,1]}=={0,1}
    return n0,n1

if __name__=='__main__':
    print("exact clipping/truncation/independent monomial factorization:",sum(run_trial(i) for i in range(50)),"orientations PASS")
    clipping_negative_control()
    print("large-leakage invalid-small-tail negative control: PASS")
    for n in range(1,6):
        print("exact perfect one-bit encoder n=%d: %d private zero inputs, %d fully decodable one inputs" %
              (n,*exact_perfect_protocol(n)))
