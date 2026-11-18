"""Exact two-dimensional consistency checks. Only the accompanying proof is universal."""
from fractions import Fraction as F
from itertools import product
from random import Random

def need(b,msg):
    if not b: raise RuntimeError(msg)

def plus(A,B): return {(x+u,y+v) for x,y in A for u,v in B}
def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
def hull(A):
    pts=sorted(set(A))
    if len(pts)<=1: return pts
    def chain(xs):
        s=[]
        for x in xs:
            while len(s)>1 and cross(s[-2],s[-1],x)<=0: s.pop()
            s.append(x)
        return s[:-1]
    return chain(pts)+chain(reversed(pts))
def double(P):
    return abs(sum(p[0]*q[1]-p[1]*q[0] for p,q in zip(P,P[1:]+P[:1])))
def clip(P,coord,t,sign):
    ans=[]
    for p,q in zip(P,P[1:]+P[:1]):
        a=(p[coord]-t)*sign; b=(q[coord]-t)*sign
        if a>=0: ans.append(p)
        if (a<0<b) or (b<0<a):
            v=F(-a,b-a)
            ans.append(tuple(p[h]+v*(q[h]-p[h]) for h in (0,1)))
    return ans
def outside_twice(C,K):  # C=union of unit lattice squares, K=rational convex polygon
    total=0
    for x,y in C:
        P=K
        for c,t,s in [(0,x,1),(1,y,1),(0,x+1,-1),(1,y+1,-1)]:
            P=clip(P,c,t,s)
        total+=2-double(P)
    return total

S={(0,0),(1,0),(0,1),(1,1)}
def nonempty_subsets(s):
    v=sorted(s)
    return [{v[j] for j in range(len(v)) if mask>>j&1} for mask in range(1,1<<len(v))]
def main():
    need(double(hull(S))==2,'square hull')
    need(outside_twice({(0,0)},[(0,0),(1,0),(0,1)])==1,'triangle clipping')
    need(outside_twice({(0,0)},[(0,0),(2,1),(0,1)])==F(1,2),'oblique clipping')
    # Exact area via unions of closed unit cells: distinct cells meet in area zero.
    count=0;eq=0
    subs=nonempty_subsets(S)
    for A,B,C in product(subs,repeat=3):
        # A denotes lower-left corners of a polyomino; B,C are finite sets of points.
        ab=plus(A,B);ac=plus(A,C);abc=plus(ab,C)
        deficit=2*len(abc)+double(hull(plus(A,S)))-2*(len(ab)+len(ac))
        need(deficit>=0,('corollary',A,B,C,deficit))
        eq+=deficit==0
        count+=1
    need(count==3375 and 0<eq<count,'exhaustive coverage')
    rng=Random(4401)
    X=list(product(range(-3,4),repeat=2));H=list(product(range(-4,5),repeat=2))
    Eqs=0
    for i in range(160):
        E=set(rng.sample(X,rng.randrange(1,14)));B=set(rng.sample(X,rng.randrange(1,9)))
        K=hull(rng.sample(H,1+i%8));Q=hull(plus(K,B))
        v=outside_twice(plus(E,B),Q)-outside_twice(E,K)
        need(v>=0,('exterior',E,B,K,v)); Eqs+=v==0
    need(0<Eqs<160,'exterior equality and strictness')
    print(f'PASS: {count} hull-corrected area cases ({eq} equalities); 160 exterior-area cases ({Eqs} equalities).')
if __name__=='__main__': main()
