#!/usr/bin/env python3
"""Small, exact replays of the finite slack and an atom-filter variation. No dependencies."""
from itertools import permutations, combinations, product
from math import prod
from collections import Counter

def need(b, data):
    if not b:
        raise ArithmeticError(data)

def cnt(p):
    return sum(p[i] < p[k] < p[j] < p[l] for i,j,k,l in combinations(range(len(p)),4))

def layered(p):
    return all(not (p[j]>p[i]>p[k] or p[i]>p[k]>p[j])
               for i,j,k in combinations(range(len(p)),3))

def clone(p,keep,drop):
    # Working at doubled scales keeps the two coordinates distinct.
    pts=[(2*i,2*v) for i,v in enumerate(p) if i != drop]
    pts.append((2*keep+1,2*p[keep]-1))
    return tuple(v for _,v in sorted(pts))

def finite():
    tests=0
    for n in range(4,9):
        best=-1; opts=0; unlayered=0
        for p in permutations(range(n)):
            count=cnt(p)
            if count>=best:
                if count>best:
                    opts=unlayered=0;best=count
                opts+=1;unlayered+=not layered(p)
            if n<=7:
                D=[{j for j in range(i) if p[j]<p[i]} for i in range(n)]
                U=[{j for j in range(i+1,n) if p[j]>p[i]} for i in range(n)]
                for u,v in combinations(range(n),2):
                    if p[u]<p[v]:continue
                    slack=(len(D[u])*len(U[u])+len(D[v])*len(U[v])
                           -2*len(D[u]&D[v])*len(U[u]&U[v]))
                    need(slack>=0 and cnt(clone(p,u,v))+cnt(clone(p,v,u))-2*count==slack,(p,u,v))
                    tests+=1
        need(unlayered==0,(n,unlayered))
        print('order',n,'maximum',best,'optimizers',opts,'nonlayered',unlayered)
    print('finite two-clone slack identities:',tests)

def variations():
    # Antidiagonal block inflations with rational masses. Work homogeneously:
    # base masses w_j / sum(w); perturbation direction v_j/sum(w) of sum zero.
    # For ranks repeated in a sample the draws in that block form a decreasing run.
    tests=pairtests=0
    for p in permutations(range(4)):
        ix=range(4);w=[1,3,2,4]
        def ind(order):
            blocks=sorted(order)
            return int(blocks[0]!=blocks[1] and blocks[2]!=blocks[3]
                       and p[blocks[0]]<p[blocks[2]]<=p[blocks[1]]<p[blocks[3]])
        tuples=[s for s in product(ix,repeat=4) if ind(s)]
        def lift(weights):
            return sum(prod(weights[k] for k in s) for s in tuples)
        F=[[sum(w[k]*w[l]*ind((i,j,k,l)) for k,l in product(ix,repeat=2)) for j in ix] for i in ix]
        for i in ix:
            for j in range(i,4):
                if i!=j and p[i]<p[j]:continue
                down=sum(w[k] for k in ix if k<min(i,j) and p[k]<min(p[i],p[j]))
                up=sum(w[k] for k in ix if k>max(i,j) and p[k]>max(p[i],p[j]))
                need(F[i][j]==2*down*up,(p,i,j));pairtests+=1
        for i in ix:
            for mask in range(1,16):
                B=[j for j in ix if mask>>j&1];W=sum(w[j] for j in B)
                v=[(W if j==i else 0)-(w[j] if j in B else 0) for j in ix]
                E=lambda s:lift([a+s*b for a,b in zip(w,v)])
                # Exact degree-four interpolation of coefficient of s^2.
                times24=16*(E(1)+E(-1)-2*E(0))-(E(2)+E(-2)-2*E(0))
                predicted=W*W*F[i][i]-2*W*sum(w[j]*F[i][j] for j in B)+sum(w[j]*w[k]*F[j][k] for j,k in product(B,repeat=2))
                need(times24==24*6*predicted,(p,i,mask));tests+=1
    print('weighted two-root intersection identities:',pairtests)
    print('weighted quartic second-variation identities:',tests)

if __name__=='__main__':
    finite();variations()
