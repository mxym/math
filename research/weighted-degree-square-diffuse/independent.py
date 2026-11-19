"""Exact pointwise and averaged centering checks; stdlib, no assertions."""
from fractions import Fraction as R
from itertools import combinations,product
from math import comb

def ck(v,m):
    if not v: raise ArithmeticError(m)
def evaluate(n,w,allcond=False):
    edges=tuple(combinations(range(n),2)); W=sum(w)
    d=tuple(sum(a for edge,a in zip(edges,w) if i in edge) for i in range(n))
    allsign=list(product((-1,1),repeat=n)); law=1<<n
    c=[sum(a for (i,j),a in zip(edges,w) if s[i]!=s[j]) for s in allsign]
    C=max(c);g=R(2*C,W)-1
    p=tuple(R(a,2*W) for a in d);P=sum(v*v for v in p);T=sum(v**3 for v in p)
    E={lam:[R(0),R(0)] for lam in (R(0),R(1,5),R(2,3),R(1),R(2))}
    ms=mh=E3=E4=eff=R(0)
    flips=0
    for s,cw in zip(allsign,c):
        m=sum(x*v for x,v in zip(s,p));u=abs(m);f=1-R(2*cw,W)
        ms+=m*m;E3+=u**3;E4+=m**4;mh+=u; eff+=f/(1+u)**2
        for lam in E:
            # Flip each initial heavier-side sign independently, leaving the others deterministic.
            # This derives the conditional cut directly from two types of edges.
            t=lam*u/(1+lam*u);pol=1 if m>=0 else -1
            H=sum(a for (i,j),a in zip(edges,w) if s[i]==s[j]==pol)
            cut=(1-t)*cw+2*t*(1-t)*H
            ck(cut<=C,'concrete conditional cut')
            lhs=(1-R(2,W)*cut)*(1+lam*u)**2
            ck(lhs==f-(2*lam-lam**2)*m*m,'pointwise')
            E[lam][0]+=lhs; E[lam][1]+=(1+lam*u)**2
            if allcond:
                I=[i for i in range(n) if s[i]==pol];tot=val=R(0)
                for flipsig in product((0,1), repeat=len(I)):
                    y=list(s)
                    for v,b in zip(I,flipsig):
                        if b:y[v]*=-1
                    h=sum(flipsig);prob=t**h*(1-t)**(len(I)-h)
                    tot+=prob; val+=prob*sum(a for (i,j),a in zip(edges,w) if y[i]!=y[j])
                    flips+=1
                ck(tot==1 and cut==val,'enumeration over all new sign vectors')
    e=mh/law
    ck(ms/law==P and E4/law==3*P**2-2*sum(v**4 for v in p),'second and fourth moments')
    ck(eff/law<=6*T and (E3/law)**2<=P*(E4/law),'non-tilted bound')
    for lam,(num,den) in E.items():
        ck(-num/law==(2*lam-lam*lam)*P and den/law==1+2*lam*e+lam*lam*P,'averaging')
        ck(g*den>=-num,'tilted ratio')
    # g >= P/(1+2sqrt(P)), checking without non-rational roots
    ck(max(R(0),P-g)**2<=4*P*g*g,'optimized P-only bound')
    return flips

def main():
    count=flips=0
    for w in product(range(3),repeat=6):
        if not any(w):continue
        flips+=evaluate(4,w,allcond=(sum(w) in (1,11,12)));count+=1
    for w in ((1,1,1),(1,9,17),(2,5,7,11,13,17,19,23,29,31),(0,0,0,0,0,3,3,3,3,3)):
        n=3 if len(w)==3 else 5
        flips+=evaluate(n,w,True);count+=1
    for j in range(1,2001):
        t=R(j,2001);lam=1/(1+t)
        ck((2*lam-lam**2)/(1+lam*t)**2==1/(1+2*t),'optimal-lambda substitution')
    for k in range(2,120):
        d1,d2=R(1,2*k),R(1,2*k*k)
        P=k*d1*d1+k*k*d2*d2;n=k+k*k
        ck(P==(R(1,k)+R(1,k*k))/4 and n*P==R((k+1)**2,4*k),'two-clique ratio')
    print(f'{count} weighted graphs tested at five rational lambda values; {flips} explicit independent-flip outcomes')
    print('2000 rational optimized-lambda checks; 118 exact two-clique profile checks')
    print('PASS')
if __name__=='__main__': main()
