#!/usr/bin/env python3
"""Exact finite checks of the proof mechanisms, not of the infinite theorem."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import comb

def check(statement, name):
    if not statement: raise RuntimeError(name)

def hull_or_drop(Q,N):
    hull = []
    for i,y in enumerate(Q):
        while len(hull)>=2:
            a,b=hull[-2:]
            if (Q[b]-Q[a])*(i-b) > (Q[i]-Q[b])*(b-a): break
            hull.pop()
        hull.append(i)
    for a,b in zip(hull,hull[1:]):
        check(all((v-Q[a])*(b-a)<=(k-a)*(Q[b]-Q[a]) for k,v in enumerate(Q[a:b+1],a)), 'upper hull')
    faces=[(a,b) for a,b in zip(hull,hull[1:]) if Q[b]>Q[a]]
    def certificate(i,j,buff):
        check(j-i>=N and Q[j]>Q[i] and all(
            (Q[k]-Q[i])*(j-i)<=(k-i+buff)*(Q[j]-Q[i]) for k in range(i,j+1)), 'secant')
    for i,j in faces:
        if j-i>=N:
            certificate(i,j,0);return 'face'
    t=0
    while t<len(faces):
        i,j=faces[t]
        first=F(Q[j]-Q[i],j-i)
        while j-i<N and t+1<len(faces):
            t+=1;j=faces[t][1]
        if j-i<N: break
        a,b=faces[t];last=F(Q[b]-Q[a],b-a)
        if first*N<=last*(N+1):
            certificate(i,j,2);return 'group'
        t+=1
    L=max(F(Q[r]-Q[0],r) for r in range(1,min(N,len(Q)-1)+1))
    check(Q[-1]-Q[0]<=2*N*(N+1)*L,'geometric rise bound')
    return 'drop'

def exercise_hulls():
    counts=Counter()
    for inc in product(range(3),repeat=8):
        Q=[0]
        for e in inc: Q.append(Q[-1]+e)
        for N in [2,3,4]:
            counts[hull_or_drop(Q,N)]+=1
    for N in [2,3,5,8,10]:
        Q=[0]
        for i in range(1600,1560,-1):Q.append(Q[-1]+i)
        check(hull_or_drop(Q,N)=='group','strictly concave slowly changing slopes')
        counts['group']+=1
    return dict(sorted(counts.items()))

def exercise_sperner():
    n=0
    for a,b in [(1,2),(1,3),(2,3),(2,5),(5,8),(1,17)]:
        p=F(a,b);q=1-p
        for l in range(1,9):
            mixed=Counter()
            for roles in product([p,q],repeat=l):
                masses=Counter({0:1})
                for f in roles:
                    nxt=Counter()
                    for x,c in masses.items():
                        nxt[f*x]+=c;nxt[f*x+(1-f)]+=c
                    masses=nxt
                check(max(masses.values())<=comb(l,l//2),'conditional max atom')
                mixed.update(masses);n+=1
            check(sum(mixed.values())==4**l and max(mixed.values())<=2**l*comb(l,l//2),'mixed max atom')
            points=sorted(mixed)
            check(points[0]==0 and len(points)>1 and min(y-x for x,y in zip(points,points[1:]))>0,'support/spacing')
    return n

def exercise_clip():
    # Choose s=b log 2 and X,Y integer, p=a/b. All the needed exponentials are rational.
    count=0
    for rawx,rawy in [([1,2,5,1,3],[4,1,2,3,2]),([2,0,3,0,1],[0,5,1,2,1])]:
        X={F(i):F(v,sum(rawx)) for i,v in enumerate(rawx) if v}
        Y={F(i):F(v,sum(rawy)) for i,v in enumerate(rawy) if v}
        def tail(L,x):return sum((v for t,v in L.items() if t>x),F(0))
        def tilt(k,t):
            e=k*t;check(e.denominator==1,'exact rational tilt');return F(2)**e.numerator
        for a,b in [(1,2),(1,3),(2,3),(1,5),(4,5)]:
            W=Counter()
            for x,m in X.items():
                for y,n in Y.items():W[(a*x+(b-a)*y)/b]+=m*n
            for A in range(3):
                for B in range(A+1,5):
                    def moment(L,k):
                        val=sum((tilt(k,min(t,B))*v for t,v in L.items() if t>A),F(0))
                        knots=sorted({F(A),F(B)}|{t for t in L if A<t<B})
                        quad=tilt(k,A)*tail(L,A)+sum((tilt(k,v)-tilt(k,u))*tail(L,u) for u,v in zip(knots,knots[1:]))
                        check(quad==val,'clipped Stieltjes integral')
                        return val
                    check(moment(X,a)*moment(Y,b-a)<=moment(W,b),'weighted clipping')
                    count+=1
    return count

if __name__=='__main__':
    print('hull cases:',exercise_hulls())
    print('conditional role histories:',exercise_sperner())
    print('exact strict-tail clipping products:',exercise_clip())
