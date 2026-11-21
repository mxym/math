#!/usr/bin/env python3
"""Exact finite structural controls, not a verification of an asymptotic."""
from math import gcd, isqrt

def require(ok):
    if not ok: raise ValueError("structural replay failed")

def main(maximum=1400):
    spf=list(range(maximum+1))
    for p in range(2,isqrt(maximum)+1):
        if spf[p]==p:
            for k in range(p*p,maximum+1,p):
                if spf[k]==k: spf[k]=p
    primes=[p for p in range(2,maximum+1) if p==spf[p]]
    def factors(n):
        out=[]
        while n>1:
            p=spf[n]; out.append(p); n//=p
        return out
    cases=falsecount=lostcount=checked=0
    for N in range(6,maximum+1,2):
        V={p for p in primes if 3<=p<=N-3 and N%p}
        F={p:factors(N-p) for p in V}; FV={p:set(F[p]) for p in V}
        require(all(q in V for p in V for q in FV[p]))
        gold={p for p in primes if p<N and N-p>=2 and spf[N-p]==N-p}
        menus=[{s} for s in sorted(V) if s<=19]
        menus+= [{s for s in V if 5<=s<=31},set()]
        for S in menus:
            # Literal reachability on the divisor graph, not the sieve characterization.
            reached=set(S); U=[]
            for j in range(3):
                reached=reached|{p for p in V if FV[p]&reached}
                U.append(V-reached)
            T={t for t in V if any(t%s==N%s for s in S)}
            require(T==V-U[0]-S or T|S==V-U[0])
            A={p for p in V if p not in S|T and FV[p].isdisjoint(T)}
            require(A==U[1])
            survivors={p for p in A if FV[p]<=A}
            require(survivors==U[2])
            false=survivors-gold; lost=gold-survivors
            require(lost=={p for p in gold if p not in V or p in S or N-p in S})
            require(len(lost)<=2*len(S)+1)
            for x in false:
                q=max(FV[x]); m=(N-x)//q
                require(m>=2 and m*q==N-x and FV[x]<=A and q in A)
                require(set(factors(m))<=A and FV[q].isdisjoint(T))
                for t in T:
                    if t>=5 and gcd(t,m*(m-1)*N)==1:
                        require(len({0,N*pow(m,-1,t)%t,N%t})==3)
                        # Prime-equality boundary exceptions are exactly why
                        # the proof discards q or x at/below the sieve cutoff.
                        if t<min(q,x):
                            require(q%t not in {0,N*pow(m,-1,t)%t,N%t})
                        checked+=1
            cases+=1; falsecount+=len(false); lostcount+=len(lost)
    require(falsecount>0 and lostcount>0 and checked>0)
    print("PASS",cases,"center/menu cases;",falsecount,"composite-survivor memberships;",
          lostcount,"lost pair memberships;",checked,"three-root tests")
if __name__=="__main__": main()
