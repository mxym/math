"""Optional finite consistency checks, not used to prove the theorem. Standard library."""
from fractions import Fraction as F
from itertools import combinations
from math import factorial, comb, ceil

def req(v, msg):
    if not v: raise ArithmeticError(msg)

def constants(d):
    b=F(1,(4*d)**(d*d)*4**d*factorial(d))
    p=F(1,2**(d*(d+1)+2)*factorial(d))
    return b,p,p*b/4**d

def thresholds(d,c):
    # Bound exp(-t) <= 1/t for t>0.
    goal=c/(4*(d+1))
    J=max(4*d+1,ceil(8*d*d/goal))
    k=ceil(2*(2*J)**(2*d)/goal)
    req(F(4*d*d,J)+F((2*J)**(2*d),k)<=goal,"missing fraction")
    return max(2*d+1,2*k)

def det(o,a,b):
    return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])

def hull(points):
    points=sorted(set(points))
    if len(points)<=1: return points
    def half(arr):
        h=[]
        for p in arr:
            while len(h)>=2 and det(h[-2],h[-1],p)<=0: h.pop()
            h.append(p)
        return h
    return half(points)[:-1]+half(points[::-1])[:-1]

def inside(h,x):
    if len(h)==0: return False
    if len(h)==1: return x==h[0]
    if len(h)==2:
        a,b=h
        return det(a,b,x)==0 and all(min(a[i],b[i])<=x[i]<=max(a[i],b[i]) for i in (0,1))
    return all(det(t,h[(i+1)%len(h)],x)>=0 for i,t in enumerate(h))

def main():
    binom_cases=0
    for d in range(1,11):
        b,p,c=constants(d)
        n0=thresholds(d,c)
        req(c>0 and n0>=2*d+1,"threshold")
        for m in range(2*d,2*d+20):
            cap_event=comb(m,d)*F(1,2**d*m)**d*F(m-1,m)**(m-d)
            req(cap_event>=p,('cap probability',d,m))
            # At the largest admitted outer fraction, verify the inequality
            # from the exact one-new term with the pair union bound.
            n=m+1;g=c/(2*m)
            q=min(F(1,2*n),g/(2*m))
            delta=n*q*(1-q)**m*g-comb(n,2)*q*q
            req(delta>=c*q/(16*(1-q)),('linear gain',d,n))
            binom_cases+=1
        print('d =',d,', binary digits of sufficient N =',n0.bit_length())
    cloud=tuple((x,y) for x in (-2,0,2) for y in (-2,0,2))
    ys=tuple((x,y) for x in range(-2,3) for y in range(-2,3))
    counts=[0,0,0,0];configs=0
    for n in (3,4,5,6):
        for S in combinations(cloud,n):
            configs+=1;H=hull(S);H0=hull(S[:n//2])
            leaves=[hull(S[:i]+S[i+1:]) for i in range(n//2,n)]
            for y in ys:
                b=sum(inside(H,y) and not inside(h,y) for h in leaves)
                req(0<=b<=3 and (not inside(H0,y) or b==0),('essential count',S,y))
                counts[b]+=1
    req(all(counts[:3]) and sum(counts)==configs*len(ys),'essential count coverage')
    print('PASS:',binom_cases,'exact cap and mixture checks;',configs,'finite planar configurations and',sum(counts),'holdout/test comparisons; counts by essential holdout labels:',counts)
if __name__=='__main__': main()
