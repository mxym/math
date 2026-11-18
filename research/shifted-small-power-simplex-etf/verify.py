"""Exact checks for the abstract bound and a nonmaximal, nonorthogonal real ETF.
Run with Python 3, standard library. These finite checks do not prove the theorem.
"""
from fractions import Fraction as F
from itertools import combinations
from math import comb


def require(q, why):
    if not q:
        raise ValueError(why)


def choose2(v):
    return v*(v-1)//2


for l in range(2, 17):
    for N in range(l, 9*l+1):
        k, m = divmod(N, l)
        s = [k+int(i < m) for i in range(l)]
        M = (l-m)*comb(k, 2)+m*comb(k+1, 2)
        b = 4*l*l*(M+1)
        eta, p = F(1,b*b), F(1,8*l*l*(M+1)**2)
        require(M == sum(map(choose2, s)), 'balanced count')
        require(1-2*p*b == F(M,M+1), 'endpoint')
        require(p < F(1,2) and l*l*eta < 1, 'forbidden clique')
        require(2*l*(l-1)*eta < 1 and 2*M*l*(l-1) < b, 'transversal cost')
print('PASS exact constants and balanced counts for 15 simplex sizes and all tested multiplicities')


def mult9(u,v):
    a,b=divmod(u,3); c,d=divmod(v,3)
    return 3*((a*c-b*d)%3)+(a*d+b*c)%3


def sub9(u,v):
    a,b=divmod(u,3); c,d=divmod(v,3)
    return 3*((a-c)%3)+(b-d)%3


# Symmetric Paley conference matrix on {infinity} union GF(9).
squares={mult9(u,u) for u in range(1,9)}
def entry(i,j):
    if i==j:return 0
    if 9 in (i,j):return 1
    return 1 if sub9(i,j) in squares else -1


l,d=10,5
C=[[entry(i,j) for j in range(l)] for i in range(l)]
H=[[3*(i==j)+C[i][j] for j in range(l)] for i in range(l)]
for i in range(l):
    for j in range(l):
        require(C[i][j]==C[j][i], 'symmetry')
        require(sum(C[i][a]*C[a][j] for a in range(l))==9*(i==j), 'conference identity')
        require(sum(H[i][a]*H[a][j] for a in range(l))==6*H[i][j], 'rank-five tight frame')
# G=H/3 has diag 1, G^2=2G, trace 10. Thus G is a real PSD rank-5 Gram
# matrix, not an assumed combinatorial parameter set. l=10<5*6/2.
alpha2=F(l-d,d*(l-1))
require(alpha2==F(1,9) and l<d*(d+1)//2, 'nonmaximal positive coherence')
for m in range(l):
    for k in (1,2,3):
        ids=list(range(l))*k+list(range(m))
        ones=0
        for i,j in combinations(ids,2):
            t=F(H[i][j],3)
            lift=(d*t*t-1)/(d-1)
            D=(1+(l-1)*lift)/l
            require(D==(t*t-alpha2)/(1-alpha2)==int(i==j), 'projector/contact identity')
            ones+=int(D)
        require(ones==(l-m)*choose2(k)+m*choose2(k+1),'actual repeated ETF cost')
print('PASS Paley (10,5) real ETF, coherence squared 1/9: exact Gram, lifts, all residues and 3 multiplicities')
