#!/usr/bin/env python3
"""Exact rational checks for the near-antipodal tail in dimensions 6 and 7."""
from fractions import Fraction as R

TOLS={
 6:(36,[85,920,1800,2800,4000,5700,8200,19600,30700]),
 7:(63,[43,475,960,1500,2200,3150,4650,11450,18400])
}
# Upper bounds for the negative-neighbor sum in the cited local moment lemma.
U=[None,None]+[R(k,100000) for k in (11258,11898,12538,13178,13818,14458,15098)]
F1,H=R(1389,1000),R(4,625)

def verify(n,P,a,k):
    h=R(k,10**6)
    lam=((R(1,2)+h*h)/(1-h*h))**2
    mixed=(R(1,2)+h)**2/(1-h*h)
    assert R(1,4)<lam<mixed<1 and lam<R(6,n+4)
    delta=lam-R(1,4); T=1-lam; f0=R(3,n*(n+2))-lam/n
    M=mixed*(mixed-lam)
    assert f0>0 and f0>M
    def certificate(D):
        assert D>0 and 1/D>f0
        b=a*(f0-M)/(1/D-f0)
        gap=f0*(a+b)**2-T*a-2*a*b*M-b*b/D
        assert b>0 and gap>0
        # Solve the same two-population quadratic by its determinant, independently.
        assert (f0*a*a-T*a)*(1/D-f0)+(a*(f0-M))**2>0
        return gap
    b=P+1-a
    line_gap=certificate(b/T)
    row_gaps=[]
    for s in range(2,P-a+1):
        q=2*s+1
        Ks=[F1+U[d]+(q-1-d)*H-delta*(1+R(d,4)) for d in range(2,s+1)]
        K=max(Ks); j=P-a-s; D=j/T+q/K
        gap=certificate(D)
        B=a*(f0-M)/(1/D-f0); u=B/(T*D); v=B/(K*D)
        assert j*u+q*v==B
        # Independent direct evaluation of every possible row degree at the chosen weights.
        for kd in Ks:
            upper=T*(a+j*u*u)+2*a*(j*u+q*v)*M+q*v*v*kd
            assert f0*(a+j*u+q*v)**2-upper>=gap>0
        row_gaps.append(gap)
    return line_gap,row_gaps

if __name__=='__main__':
    passes=0
    for n,(P,ks) in TOLS.items():
        for a,k in zip(range(P-8,P+1),ks):
            lg,rg=verify(n,P,a,k)
            assert lg>0 and all(x>0 for x in rg)
            passes+=1
            print(n,a,k,'line: pass, residual cases:',len(rg))
    assert passes==18
