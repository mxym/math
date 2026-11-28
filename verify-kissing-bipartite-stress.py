#!/usr/bin/env python3
"""Exact controls for the bipartite-stress argument; standard Python."""
from itertools import combinations
from fractions import Fraction as F

def bip(A):
    col={}
    for i in range(len(A)):
        if i in col:continue
        col[i]=0;q=[i]
        while q:
            u=q.pop()
            for j in A[u]:
                if j in col and col[j]==col[u]:return False
                if j not in col:col[j]=1-col[u];q.append(j)
    return True
def main():
    cert=0
    for n in (4,5,6):
        ed=list(combinations(range(n),2))
        for mask in range(1<<len(ed)):
            A=[set()for _ in range(n)]
            for k,(i,j) in enumerate(ed):
                if mask>>k&1:A[i].add(j);A[j].add(i)
            if any(A[i]&A[j] for i,j in ed if j in A[i]):continue
            B=bip(A)
            if n==4:assert B
            if n==6:assert any(all(j not in A[i]for i,j in combinations(t,2))for t in combinations(range(n),3))
            for v in range(n):
                T=set(range(n))-A[v]-{v}
                if all(not(A[t]&T)for t in T):
                    cert+=1;assert B
    for n in range(4,21):
        m=(n+1)//2
        assert m<=n-2 and F(n+4,6)<=4
        # A trace-free diagonal input S verifies Tr Tr* at every diagonal,
        # and its nonzero symmetric off-diagonal entry checks a second basis type.
        def S(i,j):return (int(i==j==0)-int(i==j==1)+int((i,j)in((0,1),(1,0))))
        for i,j in combinations(range(n),2):
            for a,b in [(i,j),(i,i),(j,j)]:
                total=0
                for k in range(n):
                    p=[a,b,k,k]
                    for u,v in combinations(range(4),2):
                        c,d=[t for t in range(4)if t not in (u,v)]
                        total+=(p[u]==p[v])*S(p[c],p[d])
                assert total==(n+4)*S(a,b)
        axes=[j//2 for j in range(n)]
        w=[F(1,m*axes.count(j))for j in axes]
        assert sum(w)==1 and sum(F(3,4)*w[i]*w[j]for i in range(n)for j in range(n)if axes[i]==axes[j])==F(3,4*m)
    assert F(1,216)<F(1,16)
    print('PASS:',cert,'local rank-one bipartition controls; n=4..20 trace and baseline')
if __name__=='__main__':main()
