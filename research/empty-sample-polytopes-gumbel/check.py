"""Finite exact consistency tests only.  No numerical claim about the limiting law."""
from math import comb, factorial
from itertools import combinations,permutations
from collections import defaultdict

def fall(n,k):
    return factorial(n)//factorial(n-k) if k<=n else 0
def req(v,x):
    if not v: raise ArithmeticError(x)

def test(t,mode,m,n):
    # corner overlaps Y, exclusive complement per corner, two exclusive interiors,
    # one common interior, and a common outside. Every elementary atom is equiprobable.
    Y=[[int((i+j+mode)%3==0)+int(i==j and mode%2==0) for j in range(t)] for i in range(t)]
    b=2+max(max(map(sum,Y)),max(map(sum,zip(*Y))))
    row=[b-sum(r) for r in Y]; col=[b-sum(c) for c in zip(*Y)]
    outside,inner_common,inner_exclusive=7,mode%3,3
    I=sum(map(sum,Y))+inner_common
    a=t*b+inner_common+inner_exclusive
    M=outside+2*a-I
    # Direct dynamic counting of distinct corners occupied by the early labels.
    data=[(0,outside)]+[(1<<i,v) for i,v in enumerate(row)]+[(1<<(j+t),v) for j,v in enumerate(col)]
    data.extend(((1<<i)|(1<<(t+j)),Y[i][j]) for i in range(t) for j in range(t))
    tab={0:1}
    for _ in range(m):
        z=defaultdict(int)
        for s,h in tab.items():
            for mask,w in data:
                if s&mask==0:z[s|mask]+=w*h
        tab=z
    actual=tab.get((1<<(2*t))-1,0)*outside**(n-m)
    matched=upper=0
    for l in range(t+1):
        needed=2*t-l
        if needed>m:continue
        coef=fall(m,needed)*outside**(n-needed)
        for r in combinations(range(t),l):
            for c in permutations(range(t),l):
                prod=coef
                for i,j in zip(r,c):prod*=Y[i][j]
                for i in range(t):
                    if i not in r:prod*=row[i]
                    if i not in c:prod*=col[i]
                matched+=prod
        upper+=comb(t,l)**2*factorial(l)*coef*b**(2*t-2*l)*I**l
    req(actual==matched<=upper,(t,mode,m,n,actual,matched,upper))
    req(outside==M-2*a+I,"union identity")

def main():
    cases=0
    for t in (2,3,4):
        for mode in range(6):
            for m in range(t,2*t+2):
                for n in (m,m+1,m+3):
                    test(t,mode,m,n);cases+=1
    for d in range(2,101):
        B=2*d+2;A=3*d*d+d
        req(A-d-B*(d-1)+1-d*d==3,d)
        req(2*d-1-B==-3,d)
        req(1-d<0 and 4*(d+1)<10*d*(d+1),d)
    # Track powers of n and log(n) in n^(k-j) v^m exp(-nv) for j shared vertices.
    # v ~ d log(n)/n and exp(-nv) is const n^(-d) log(n)^(-(m-1)).
    exps=0
    for d in range(2,17):
        for k in range(d+1,d+20):
            m=k-d
            req(k-d-(m-1)-1==0 and m-1-(m-1)==0,"shell")
            for j in range(1,k):
                free_heights=m if j<=d else k-j
                npower=k-j-free_heights-d
                logpower=free_heights-(m-1)
                req(npower==(-j if j<=d else -d) and npower<0,(d,k,j))
                req(j>d or logpower==1,(d,k,j))
                exps+=1
    print("Fixed-k volume-shell and shared-vertex exponents:",exps,"triples")
    print("Matched-corner upper bound versus direct finite occupancy:",cases,"exact cases")
    print("All log-exponent identities and near-overlap power signs: dimensions 2..100")
    print("PASS finite checks only. Count and maximum limit laws are analytic.")

if __name__=="__main__":main()
