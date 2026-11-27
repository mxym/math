#!/usr/bin/env python3
"""Construct actual normalized Choi coefficients independently from gates."""
from fractions import Fraction as F
from itertools import product

# Pauli representatives I, X, Z, XZ; phases are immaterial.
ST=[[0,1],[1,0],[0,1],[1,0]]
SG=[[1,1],[1,1],[1,-1],[1,-1]]


def outer(v,w):
    return [[a*b for b in w] for a in v]


def matvec(M,v):
    return [sum(x*y for x,y in zip(row,v)) for row in M]


def matmul(A,B):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]


def dot(x,y):
    return sum(a*b for a,b in zip(x,y))


def vec(d,gate):
    V=[[0]*4 for _ in range(d*d)]
    for a,b in product(range(d),range(2)):
        outa,outb,sign=gate(a,b)
        V[a*d+outa][2*b+outb]=sign
    assert sum(dot(x,x) for x in V)==2*d
    return V


def swap_basis(d,kind):
    if kind=='identity':
        return vec(d,lambda a,b:(a,b,1))
    if kind=='cz':
        return vec(d,lambda a,b:(a,b,(-1)**(a*b)))
    if kind=='swap':
        assert d==2
        return vec(d,lambda a,b:(b,a,1))
    if kind=='cnot':
        assert d==2
        return vec(d,lambda a,b:(a,b^a,1))
    if kind=='controlled-white':
        return vec(d,lambda a,b:(a,ST[a%4][b],SG[a%4][b]))
    if kind=='conditioner-qutrit':
        return vec(d,lambda a,b:((a+b)%d,b,1))
    raise ValueError(kind)


def mover(g,side):
    M=[[0]*4 for _ in range(4)]
    for i,j in product(range(2),repeat=2):
        u,v=(ST[g][i],j) if side=='input' else (i,ST[g][j])
        # A transpose only changes a global sign in the XZ case.
        s=SG[g][i] if side=='input' else SG[g][j]
        M[2*u+v][2*i+j]=s
    return M


def trans(M):
    return [list(col) for col in zip(*M)]


def char(h,g):
    return (-1)**((h&g).bit_count()%2)


def phase_data(V):
    Bell=[matvec(mover(i,'output'),[1,0,0,1]) for i in range(4)]
    E=[matvec(V,b) for b in Bell]
    assert all(dot(Bell[i],Bell[j])==2*(i==j) for i,j in product(range(4),repeat=2))
    assert all(dot(E[i],E[j])==0 for i,j in product(range(4),repeat=2) if i!=j)
    return Bell,E


def reflect(h,B):
    n=len(B[0])
    D=[[F(i==j) for j in range(n)] for i in range(n)]
    for g,ray in enumerate(B):
        den=dot(ray,ray)
        if den and char(h,g)==-1:
            R=outer(ray,ray)
            D=[[x-F(2*z,den) for x,z in zip(a,b)] for a,b in zip(D,R)]
    assert matmul(D,D)==[[F(i==j) for j in range(n)] for i in range(n)]
    return D


def check_local(V):
    Bell,E=phase_data(V)
    H=outer([1,2,-1,3],[1,2,-1,3])
    H_twirl=[[F(0)]*4 for _ in range(4)]
    for h in range(4):
        DX,DY=reflect(h,E),reflect(h,Bell)
        for side,g in product(('input','output'),range(4)):
            W=matmul(V,trans(mover(g,side)))
            act=matmul(matmul(DX,W),DY)
            assert act==[[char(h,g)*x for x in row] for row in W]
        HH=matmul(matmul(DY,H),DY)
        H_twirl=[[x+y/4 for x,y in zip(row,row1)] for row,row1 in zip(H_twirl,HH)]
    Btr=lambda A:[[sum(A[2*i+k][2*j+k] for k in range(2))
                    for j in range(2)] for i in range(2)]
    assert Btr(H)!=[[F(15,2),0],[0,F(15,2)]]
    assert Btr(H_twirl)==[[F(15,2),0],[0,F(15,2)]]
    return 32


def certify_6040():
    U,V=swap_basis(2,'identity'),swap_basis(2,'cz')
    XA=[[1,0,0,1],[1,0,0,-1]]
    # Actual Choi vector projection coefficients are these entries
    # divided by 2*sqrt(2), not assumed from the analytic support SDP.
    q,r=([dot(x,[M[i][j] for i in range(4)]) for x,j in product(XA,(0,3))]
         for M in (U,V))
    assert q==[2,2,0,0] and r==[2,0,0,2]
    W=[[F(3*a+2*b,40) for a,b in zip(u,v)]
       for u,v in zip(outer(q,q),outer(r,r))]
    # Check the exact channel witness via an independently expanded
    # dominance test, and the genuine reduced input marginal.
    w=(12,2,-3,8)
    assert 2*dot(w,matvec(W,w))/dot(w,w)==F(1388,1105)
    v=(3,1,-1,3)
    E=[[F(18,25),F(6,25)],[F(6,25),F(12,25)]]
    assert matvec(W,v)==matvec(E,list(v[:2]))+matvec(E,list(v[2:]))
    assert E[0][0]!=E[1][1]


def main():
    cases=[(1,'identity'),(2,'identity'),(2,'cz'),(2,'swap'),(2,'cnot'),
           (3,'controlled-white'),(4,'controlled-white')]
    total=sum(check_local(swap_basis(d,g)) for d,g in cases)
    certify_6040()
    print(f"Choi check: {len(cases)} actual gate cases, {total} exact input/output-Pauli character actions")
    print("Choi check: character-averaged input marginal, negative untwirled control, and exact 60:40 vector lifting PASS")


if __name__=='__main__':
    main()
