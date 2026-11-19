"""Finite, exact regression certificates for the scalar identities in PROOF.md.
The uniform mathematical result follows from the proof, not these test cases."""
from fractions import Fraction as Q
from itertools import combinations_with_replacement,product
from collections import defaultdict

def ok(x,msg):
    if not x: raise ArithmeticError(msg)

def bottom(rows,weights):
    mass=defaultdict(Q)
    for w,row in zip(weights,rows):
        for x in row:mass[x]+=w
    left=Q(1);cost=Q(0)
    for x,w in sorted(mass.items()):
        take=min(w,left);cost+=take*x;left-=take
    ok(left==0,'capacity')
    return cost

def cutoff(rows,weights,t):
    return t-sum(w*sum(max(Q(0),t-x) for x in row) for w,row in zip(weights,rows))

def area(poly):
    return abs(sum(x*b-y*a for (x,y),(a,b) in zip(poly,poly[1:]+poly[:1])))/2 if poly else 0

def clip(poly,A,B,C):
    out=[]
    for (x,y),(u,v) in zip(poly,poly[1:]+poly[:1]):
        a=A*x+B*y-C;b=A*u+B*v-C
        if a<=0:out.append((x,y))
        if (a<0<b) or (b<0<a):
            h=a/(a-b)
            out.append((x+h*(u-x),y+h*(v-y)))
    return out

def main():
    s=Q(2,27)
    simplex=[(Q(0),Q(0)),(Q(1),Q(0)),(Q(0),Q(1))]
    # Probability y_(2)<=s via three convex regions at simplex vertices, each
    # checked by clipping the labeled probability simplex to two inequalities.
    constraints=[(1,0,s),(0,1,s),(-1,-1,s-1)]
    csum=0
    for i,j in ((0,1),(0,2),(1,2)):
        pol=clip(clip(simplex,*constraints[i]),*constraints[j])
        csum+=area(pol)/area(simplex)
    ok(csum==6*s*s and 3*s<1,'pair events')
    # Verify minimum survival polygon has exact quadratic (1-3t)^2 using
    # its translated vertices; integrate that polynomial on [0,1/3].
    for t in (Q(0),Q(1,12),Q(1,6),Q(1,4),Q(1,3)):
        p=clip(clip(clip(simplex,-1,0,-t),0,-1,-t),1,1,1-t)
        ok(area(p)/area(simplex)==(1-3*t)**2,'minimum area')
    u=Q(1,3);haarmin=u-3*u*u+3*u**3
    ok(haarmin==Q(1,9),'minimum average')
    h=(haarmin+csum*s/2)/(1+csum/2)
    eta=1-3*h
    ok(h==haarmin-Q(4,6669) and eta==Q(1486,2223) and eta-Q(2,3)==Q(4,2223),'margin')
    rows=[tuple(Q(j,6) for j in R) for R in combinations_with_replacement(range(7),3) if sum(R)==6]
    weights=[Q(1,7),Q(2,7),Q(4,7)]
    n=0;nt=0
    for three in product(rows,repeat=3):
        g=bottom(three,weights)
        knots=sorted(set((Q(0),Q(1))+sum(three,())))
        ok(g==max(cutoff(three,weights,t) for t in knots),'fractional knapsack')
        alpha=sum(w*r[0] for w,r in zip(weights,three));beta=sum(w for w,r in zip(weights,three) if r[1]<=s)
        for t in knots+[(a+b)/2 for a,b in zip(knots,knots[1:])]:
            deficit=alpha-cutoff(three,weights,t)
            alt=sum(w*(max(0,r[0]-t)+max(0,t-r[1])+max(0,t-r[2])) for w,r in zip(weights,three))
            ok(deficit==alt and deficit>=max(alpha-t,beta*(t-s)) and deficit>=beta/(1+beta)*(alpha-s),'cutoff deficit')
            nt+=1
        n+=1
    print("Exact Haar simplex regions; E minimum =",haarmin,"; E beta =",csum)
    print("Pooled fraction upper bound",h,"; Werner lower bound",eta,"; margin",eta-Q(2,3))
    print("Weighted tie/quantile checks:",n,"ensembles;",nt,"cutoff deficits")
    print("PASS")
if __name__=='__main__':main()
