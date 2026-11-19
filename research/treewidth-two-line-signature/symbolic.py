#!/usr/bin/env python3
"""Exact alternate replay, via simultaneous constraint multipliers and matrix-range reduction.
Requires SymPy. It neither imports nor calls the one-coordinate verifier.
"""
import sympy as s
from itertools import product
from collections import Counter
T=s.Rational;M=s.Matrix;zero=s.zeros
def ck(a,label):
    if not a: raise ValueError(label)
# State = (C, K, B) where K imposes K^T z=0 and B is a two-by-two form.
def full(c,a,b,d):return(c,zero(2,0),M([[a,b],[b,d]]))
def equal(c,h,sgn):return(c,M([-sgn,1]),s.diag(h,0))
Y=(0,T(2,3),2,4)
def seeds():
    P=[full(i+j-1,Y[i],0,Y[j]) for i,j in product(range(4),repeat=2)]
    for j in (0,1,3):
        for e in [-1,1]:
            P.append(equal(j,2+Y[j],e))
            for side in set((0,1)) if j else (0,):
                a,d=((1+Y[j],1) if side else (1,1+Y[j]));P.append(full(j,a,e,d))
    for c,a,b in [(-1,-T(1,2),T(3,2)),(1,T(3,4),T(1,4))]:
        for e in [-1,1]:P.append(full(c,a,e*b,a))
    ck(len(P)==36,'orientation count');return P
def columns(v,n):return M.hstack(*v) if v else zero(n,0)
def inertia(A):
    # all roots real; Descartes' sign variation gives exact positive count.
    q=[s.sign(x) for x in A.charpoly().all_coeffs() if x];p=sum(x!=y for x,y in zip(q,q[1:]))
    return p,A.rank()-p
def key(K):
    # normalized column space; symmetric-state Q may differ on the orthogonal complement
    return tuple(tuple(x for x in row) for row in K.T.rref()[0].tolist() if any(row))
def encode(c,K,B):
    k=key(K)
    if not k:return(c,k,tuple(B[:]))
    N=columns(K.T.nullspace(),2)
    return (c,k,tuple((N.T*B*N)[:]))
def simple_dom(A,B):
    # Uses general nullspace intersections, exact positive index in dimensions 0,1,2.
    c,K,P=A;d,L,Q=B;K=K.row_join(L); W=columns(K.T.nullspace(),2)
    loss=2*((2-A[1].rank())+(2-L.rank())-2*W.cols)
    if c-d<loss:return False
    pos,_=inertia(W.T*(P-Q)*W)
    return c-d>=loss+4*pos
def add(G,i,j,a):
    c,K,B=a;P=zero(2,G.rows);P[0,i]=1;P[1,j]=1
    return c,P.T*B*P,P.T*K
def collapse(C,G,K,internal):
    G=G.row_join(K).col_join(K.T.row_join(zero(K.cols)))
    J=tuple(internal)+tuple(range(3,3+K.cols))
    A=G[:2,:2];E=G.extract([0,1],J);D=G.extract(J,J)
    rank_ix=list(D.rref()[1]);D0=D.extract(rank_ix,rank_ix)
    miss=E*columns(D.nullspace(),len(J))
    if rank_ix:
        P=E[:,rank_ix];A-=P*D0.inv()*P.T;p,q=inertia(D0);C-=2*(p-q)
    return C,miss,A
def get(a,b,op):
    G=zero(3);ci,Hi,Ki=add(G,0,2 if op in ('S','F') else 1,a)
    if op=='S':
        cj,Hj,Kj=add(G,2,1,b);G[2,2]-=2;J=[2]
    elif op=='P':
        cj,Hj,Kj=add(G,0,1,b);cj+=3;J=[]
    elif op=='F':
        cj=0;Hj=zero(3);Kj=zero(3,0);G[2,2]-=2;J=[2]
    else:
        cj,j=b;Hj=zero(3);Kj=zero(3,0);G[j,j]+=Y[cj];J=[]
    return collapse(ci+cj,G+Hi+Hj,Ki.row_join(Kj),J)
def main():
    P=seeds();one=[full(j,Y[j],0,0) for j in range(4)]
    seen={};cnt=Counter()
    def check(t,out,op):
        k=(op=='F',encode(*t))
        if k not in seen:
            ck(any(simple_dom(t,o) for o in out),(op,k));seen[k]=True
        cnt[op]+=1
    for a,b in product(P,repeat=2):
        for op in ('S','P'):check(get(a,b,op),P,op)
    for a,j,i in product(P,range(4),range(2)):check(get(a,(j,i),'D'),P,'D')
    for a in P:check(get(a,None,'F'),one,'F')
    ck(sum(cnt.values())==2916,'all checks')
    print('PASS multiplier/nullspace and characteristic-polynomial replay')
    print('series=%d parallel=%d decorations=%d forget=%d, distinct emitted states including output arity=%d'%(cnt['S'],cnt['P'],cnt['D'],cnt['F'],len(seen)))
if __name__=='__main__':main()
