#!/usr/bin/env python3
"""Independent small exact controls for the Padé and gap algebra (not a finite search proof)."""
from fractions import Fraction as Q
from math import lcm
def need(b):
    if not b: raise RuntimeError("control failed")
def choose(x,n):
    u=Q(1)
    for j in range(n): u*=Q(x-j,j+1)
    return u
def solve(A,Y):
    Z=[list(row)+[y] for row,y in zip(A,Y)]
    n=len(Z)
    for i in range(n):
        a=next(j for j in range(i,n) if Z[j][i])
        Z[a],Z[i]=Z[i],Z[a];piv=Z[i][i];Z[i]=[v/piv for v in Z[i]]
        for j in range(n):
            if j!=i:
                v=Z[j][i];Z[j]=[a-v*b for a,b in zip(Z[j],Z[i])]
    return [z[-1] for z in Z]
def pade(g,r,s):
    # H_0=1; direct independent linear solve for coefficients H then G.
    C=[choose(Q(1,g),j)*(-1)**j for j in range(r+s+2)]
    A=[[C[j-i] if j>=i else Q(0) for i in range(1,r+1)] for j in range(s+1,r+s+1)]
    H=[Q(1)]+solve(A,[-C[j] for j in range(s+1,r+s+1)])
    GH=[sum(H[i]*C[j-i] for i in range(min(j,r)+1)) for j in range(r+s+2)]
    need(all(x==0 for x in GH[s+1:-1]) and GH[-1]!=0)
    G=GH[:s+1]; den=lcm(*(v.denominator for v in H+G))
    return [[int(v*den) for v in L] for L in (G,H)]
def evaluate(L,z):
    return sum(v*z**i for i,v in enumerate(L))
def controls():
    n=0
    for g in [2,3,4,5,7,11]:
        for s in [1,2,3]:
            for t in [1,2,3,5]:
                for flip in [0,1]:
                    r=t+s
                    R,S=(r,s) if not flip else (s,r)
                    G,H=pade(g,R,S);J,K=pade(g,R+1,S+1)
                    # Consecutive determinants are exactly c*z^(r+s+1).
                    det=[0]*(r+s+2)
                    for a,A in enumerate(G):
                        for b,B in enumerate(K): det[a+b]+=A*B
                    for a,A in enumerate(H):
                        for b,B in enumerate(J): det[a+b]-=A*B
                    need(all(x==0 for x in det[:-1]) and det[-1]!=0)
                    for p,e,u in [(3,1,1),(3,3,2),(5,2,1),(17,1,3)]:
                        P=p**e; z=Q(1,P); M=p**(t*e+min(u,e-1))
                        U=M+2
                        for j,(F,L) in enumerate([(G,H),(J,K)]):
                            if flip:F,L=L,F
                            D=P**(s+j)*(U*evaluate(F,z)-M*evaluate(L,z))
                            need(D.denominator==1)
                    n+=1
    for j in range(2,103):
        a=choose(2*j,j)/4**j
        need(a.denominator%4==0)
    print("PASS direct Pade systems, orders, adjacent determinants and asymmetric integrality:",n,"; dyadic boundaries: 101")
if __name__=='__main__':controls()
