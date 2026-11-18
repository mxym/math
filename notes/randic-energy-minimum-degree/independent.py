"""Finite independent exact checks. All assertions enforced in optimized Python."""
from itertools import combinations
from math import lcm
from collections import Counter
from fractions import Fraction as Q

def ck(ok, label):
    if not ok: raise RuntimeError(label)

def mul(A,B):
    C=list(zip(*B))
    return [[sum(a*b for a,b in zip(row,col)) for col in C] for row in A]

def rspos(y,c,r):
    # y+c sqrt(r) >= 0; c>=0
    ck(c>=0,'negative radical coefficient')
    return y>=0 or c*c*r>=y*y

def graph_test(n,edges):
    N=[set() for _ in range(n)]
    for j,k in edges:N[j].add(k);N[k].add(j)
    seen={0};work=[0]
    while work:
        for j in N[work.pop()]-seen:
            work.append(j); seen.add(j)
    if len(seen)!=n:return None
    deg=[len(z) for z in N]; h=lcm(*deg)
    P=[[h//d if j in S else 0 for j in range(n)] for d,S in zip(deg,N)]
    S=mul(P,P);t2=Q(sum(S[i][i] for i in range(n)),h*h)
    t4=Q(sum(S[i][j]*S[j][i] for i in range(n) for j in range(n)),h**4)
    leaves=deg.count(1); ninth=2*n+11*t2-4*t4
    ck(ninth<=6*n+2*leaves,('leaf bound',n,edges))
    for d in range(2,min(deg)+1):
        U=Q(n,d)-t2; V=Q(n*(2*d-1),d**3)-t4
        b=(1+Q(3*(d-1),d*d))*U-V; c=Q(2,d)*U
        ck(rspos(b,c,d-1),('d moment cap',n,d,edges))
        ck(min(deg)==max(deg)==d or b>0 or c*c*(d-1)>b*b,'strict moment cap')
    return min(deg)

def polynomial_coeffs():
    # H(x difference) as a polynomial, exact rational coefficients a.
    for a in (Q(1,2),Q(2,5),Q(9,17)):
        f=[Q(1)]
        for root in (a,a,1,-1-2*a):
            f=[(f[i-1] if i else 0)-root*(f[i] if i<len(f) else 0) for i in range(len(f)+1)]
        ck([-x for x in f]==[a*a*(1+2*a),-2*a*(1+a)**2,1+2*a+3*a*a,0,-1],
           'interpolant')
    for d in range(2,201):
        t=Q(1,d*d-d+1); s=Q(d-1,d*d)
        ck(t+(1-t)*s==Q(1,d) and t+(1-t)*s*s==Q(2*d-1,d**3),'moments')

def quotient(p,q):
    A=Q(1,p+1);B=Q(1,q+1)
    w=[Q(1,2),(1-A)/2,A*B,(1-B)/2,Q(1,2)]
    # Determinant recurrence for the weighted-path characteristic polynomial;
    # polynomial coefficients in ascending order. Strip known factors.
    pol0,pol1=[Q(1)],[0,1]
    for edge_sq in w:
        pol2=[0]+pol1
        for i,c in enumerate(pol0):pol2[i]-=edge_sq*c
        pol0,pol1=pol1,pol2
    C=1-(A+B)/2+A*B; D=A*B/4
    ck(pol1==[-D,0,D+C,0,-1-C,0,1],('weighted path',p,q))
    if abs(p-q)<=1:
        z=(A+B)/2-A*B
        ck(z<=0 or A*B>z*z,('strict lower bound',p,q))

if __name__=='__main__':
    polynomial_coeffs()
    hist=Counter();count=0
    for n in range(3,7):
        pairs=list(combinations(range(n),2))
        for m in range(len(pairs)+1):
            for es in combinations(pairs,m):
                out=graph_test(n,es)
                if out is not None:
                    delta=out
                    hist[n,'connected']+=1
                    if delta>=2:hist[n,'core']+=1
                    count+=1
    for p in range(1,31):
        for q in range(1,31):quotient(p,q)
    ck(count==27474,'total')
    print('PASS:',count,'connected labeled graphs and 900 exact double-sun quotient polynomials')
    print(dict(sorted(hist.items())))
