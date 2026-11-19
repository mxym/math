"""Arithmetic, small incidence matrices and same-order completions. No dependencies."""
from itertools import product,combinations
from math import isqrt
from fractions import Fraction
from check import graph,need,connectivity
def plane(q):
    P=[x for x in product(range(q),repeat=3) if next((v for v in x if v),None)==1]
    E={i:set() for i in range(2*len(P))}
    for i,x in enumerate(P):
        for j,y in enumerate(P,len(P)):
            if sum(a*b for a,b in zip(x,y))%q==0:E[i].add(j);E[j].add(i)
    return E
def exact_plane():
    for q in (2,3,5,7):
        E=plane(q);n=len(E);d=q+1;need(n==2*(d*d-d+1) and set(map(len,E.values()))=={d},'plane degree/order')
        for u,v in combinations(E,2):
            need(len(E[u]&E[v])<=1,'4-cycle')
        if q==2:
            conn=0;alone=0
            for z in range(1,1<<n):
                U={i for i in E if z>>i&1}
                if connectivity(E,U):conn+=1
                if any(not(U&E[i]) for i in U):alone+=1
            p=Fraction(1,2**(d+1));lower=n*p-(n*(n-1))*p*p
            need(Fraction(alone,2**n)>=lower and Fraction(2**n-conn,2**n)>=lower-Fraction(n,2**n),'Bonferroni')
            print('exact Fano graph connected subsets, isolated-event subsets:',conn,alone)
def same_order(q):
    t=q//4;d=q+1;m=2*d
    H=graph(m,True)
    Z={x:tuple((x,a) for a in range(t+int(x in ((0,0),(0,3))))) for x in H}
    A={u:set() for z in Z.values() for u in z};c=lambda u:sum(u[0])%2
    for x in H:
        for y in H[x]:
            if x<y:
                for u,v in product(Z[x],Z[y]):A[u].add(v);A[v].add(u)
    L=sorted(u for u,z in A.items() if c(u)==0 and len(z)==d-1)
    R=sorted(u for u,z in A.items() if c(u)==1 and len(z)==d-1)
    need(len(A)==2*(d*d-d+1) and len(R)==len(L)==d*d-2*d+2 and {len(z) for z in A.values()}=={d-1,d},'deficiencies')
    # An explicit shift matching is often available; use a general augmenting search.
    match={};idx={u:i for i,u in enumerate(L)}
    def augment(u,seen):
        for h in range(len(R)):
            v=R[(h+idx[u])%len(R)]
            if v in seen or v in A[u]:continue
            seen.add(v)
            if v not in match or augment(match[v],seen):
                match[v]=u;return True
        return False
    for u in L:need(augment(u,set()),'matching')
    for v,u in match.items():A[v].add(u);A[u].add(v)
    need(len(A)==2*(d*d-d+1) and all(len(z)==d and all(c(u)!=c(v) for v in z) for u,z in A.items()),'completed degrees')
    print('completed bipartite vertices/degree/matched pairs:',len(A),d,len(match))
def comparison(q,same):
    d=q+1;t=d//4;n=2*(d*d-d+1);m=2*d;n2=n if same else 4*m*t
    need(n2>n or same,'order')
    need(1820*2 <= (1 << (4*t)) and ((n-1)*(1<<5) < (1<<(d+1))) and n>d+1+5,'coarse powers')
    need(Fraction(1820*2**(d-4*t),t)==Fraction(455,512)<Fraction(15,16),'strict coefficients')
    print('Moore, competitor, degree, gap-coefficients:',n,n2,d,'455/512 < 480/512')
if __name__=='__main__':
    exact_plane()
    for q in (4,8):same_order(q)
    need(all(8191%i for i in range(2,isqrt(8191)+1)),'8191 prime')
    comparison(8191,False);comparison(2**14,True)
    print('PASS')
