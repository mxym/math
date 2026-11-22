"""Standard-library exact fixtures for the moving-sign switch."""
from math import gcd,isqrt
from fractions import Fraction
from collections import Counter

def need(x):
    if not x: raise ValueError("fixture failed")

def prime(x):
    return x>=2 and all(x%d for d in range(2,isqrt(x)+1))

def row(N,r,a,b):
    return (r,N-r,a*r-b*N,(b+1)*N-a*r)

def sign(p,q):
    t=pow(q,(p-1)//2,p)
    need(t in (1,p-1))
    return 1 if t==1 else -1

def run():
    branches=0;switches=0;nlocal=0
    for a in [13,37,61]:
        Bs=list(range(3,a-1,3))
        for b in Bs:
            need(len(set([Fraction(0),Fraction(1),Fraction(b,a),Fraction(b+1,a)]))==4)
            for l in [2,3,5,7,11,13,17,19,23,29,31,37,41,61]:
                vals=[]
                for t in range(l):
                    forbidden={u for u in range(l) if not all(x%l for x in row(t,u,a,b))}
                    if l==2:
                        if t==0: need(forbidden=={0})
                    elif l==3 or l==a and t:
                        need(forbidden=={0,t})
                    elif l!=a:
                        need(len(forbidden)<=4)
                    vals.append(Fraction(l**4,(l-1)**4)*(1-Fraction(len(forbidden),l)))
                if l>3 and a*b*(b+1)*(a-b)*(a-b-1)%l!=0:
                    first=sum(vals)/l
                    need(sum(x*x for x in vals)/l-first*first==Fraction(l-1,l*l)*(Fraction(3*l**3,(l-1)**4))**2)
                nlocal+=l
        for N in range(100,3001,4):
            if pow(N,(a-1)//2,a)!=a-1: continue
            uses=Counter();rseen=set()
            for b in Bs:
                for r in range((b*N+N//4)//a,(b*N+N//2)//a+2):
                    if not (N<4*(a*r-b*N)<2*N): continue
                    legs=row(N,r,a,b)
                    if not all(map(prime,legs)): continue
                    p,q,s,t=legs
                    need(gcd(a,N)==1 and (a*r)%N==s and r not in rseen)
                    rseen.add(r)
                    need(sign(p,q)==sign(q,p)==-sign(s,t) and sign(t,s)==sign(s,t))
                    for pair in [(p,q),(s,t)]: uses[tuple(sorted(pair))]+=1
                    switches+=1
            need(not uses or max(uses.values())<=4)
            branches+=1
    need(switches>100)
    print("PASS",nlocal,"local residues;",branches,"eligible multiplier-targets;",switches,"genuine switches")
if __name__=='__main__':run()
