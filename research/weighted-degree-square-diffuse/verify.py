"""Exact tests for PROOF-TILT.md. Finite corroboration, not needed in the proof."""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb
from random import Random

def require(b, label):
    if not b: raise ValueError(label)

def graph(n, raw, sample_scalars):
    edges=list(combinations(range(n),2)); W=sum(raw)
    w=[F(z,W) for z in raw]; p=[sum(z for ij,z in zip(edges,w) if i in ij)/2 for i in range(n)]
    J=2**n
    require(sum(p)==1,'endpoint masses')
    P=sum(z*z for z in p)
    require(sum(z*(p[i]+p[j]) for (i,j),z in zip(edges,w))==2*P,'weighted endpoint identity')
    def f(s): return sum(z*s[i]*s[j] for (i,j),z in zip(edges,w))
    records=[(s,sum(q*a for q,a in zip(p,s)),f(s)) for s in product((-1,1),repeat=n)]
    A=-min(f0 for _,_,f0 in records)
    beta=sum(abs(m) for _,m,_ in records)/J
    require(sum(f0 for _,_,f0 in records)==0 and sum(m*m for _,m,_ in records)==J*P and beta*beta<=P,'moments')
    for l in sample_scalars:
        SS=H=0
        for s,m,f0 in records:
            y=[F(v)-l*m for v in s]; g=1+l*abs(m)
            left=f(y); rhs=g*g
            require(all(abs(v)<=g for v in y) and left==f0-(2*l-l*l)*m*m and left>=-A*rhs,'pointwise rounding')
            SS+=left;H+=rhs
        require(SS/J==-(2*l-l*l)*P and H/J==1+2*l*beta+l*l*P and -SS<=A*H,'tilt')
    # For all real l (not just the checked rationals), l^2 P(1+A)+2l(A beta-P)+A>=0.
    B=P-A*beta
    require(B<=0 or B*B<=A*P*(1+A),'quadratic minimum')
    # Equivalence to A(1+2 sqrt(P))>=P without floating-point arithmetic.
    require(A>=P or 4*A*A*P>=(P-A)**2,'simplified conclusion')
    return J*len(sample_scalars)

def main():
    graphs=rows=0
    for n in (2,3,4):
        for w in product(range(3),repeat=comb(n,2)):
            if any(w):
                rows+=graph(n,w,(F(0),F(3,4),F(1),F(2))); graphs+=1
    rng=Random(287016)
    for n, count in ((5,16),(6,8),(7,4)):
        for _ in range(count):
            rows+=graph(n,[rng.randrange(17) for _ in combinations(range(n),2)],(F(2,3),F(7,8),F(1))); graphs+=1
    # Optimizer value as a rational polynomial identity for rational u=sqrt(P).
    for den in range(1,33):
        for num in range(den+1):
            u=F(num,den); l=1/(1+u)
            require((2*l-l*l)/(1+l*u)**2==1/(1+2*u),'closed form')
    for n in (31,65,200,585,1023):
        A=F(2*(n//2)*(n-n//2),comb(n,2))-1; P=F(1,n)
        beta=sum(F(comb(n,j)*abs(n-2*j),n*(1<<n)) for j in range(n+1))
        # Strictness and profile law on even/odd cliques, without enumerating 2^n rows.
        require(beta*beta<P and A>=P and (n%2==0 or A==P),'clique leading term')
    print(f'PASS: {graphs} finite weighted graphs; {rows} exact sign-and-scalar trials; 560 rational substitutions; five binomial clique laws.')
if __name__=='__main__': main()
