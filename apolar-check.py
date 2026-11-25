"""Exact final checks for the Lovitz symmetric border lower bound."""
from itertools import combinations_with_replacement as monomials
from sympy import Matrix, zeros

def points():
    K=[]
    for block in range(2):
        for r in range(3):
            for s in range(3):
                w=[int(j==r) for j in range(3)] + [-2*int(j==s) for j in range(2)]
                v=[0]*9
                v[0]=w[0]
                v[1+4*block:5+4*block]=[x-w[0]*y for x,y in zip(w[1:],[1,-2,1,1])]
                K.append(v)
    return K

def evaluations(P,d):
    mons=list(monomials(range(len(P[0])),d))
    return Matrix([[point[a]*point[b] for a,b in mons] for point in P])

def products(Q,n):
    """Rows are x_i times the polynomials Q_r, ordered by (i,r)."""
    quad=list(monomials(range(n),2))
    cubic={e:i for i,e in enumerate(monomials(range(n),3))}
    M=zeros(n*len(Q),len(cubic))
    for i in range(n):
        for j,w in enumerate(quad):
            a=cubic[tuple(sorted([i,*w]))]
            for k,q in enumerate(Q):
                M[i*len(Q)+k,a]=q[j]
    return M

if __name__=="__main__":
    p=points()
    c=[1]+[0]*8
    F=evaluations(p,2)
    assert F.rank()==18
    assert products(F.nullspace(),9).rank()==147
    Fc=evaluations([*p,c],2)
    assert Fc.rank()==19
    assert products(Fc.nullspace(),9).rank()==144
    gf=evaluations([v[:5] for v in p[:9]]+[c[:5]],2)
    local=gf.nullspace()
    assert len(local)==5
    syz=products(local,5).T.nullspace()
    assert len(syz)==1
    assert syz[0].reshape(5,5).det()==-16
    print("Global prolongation dimensions 18 and 21; local syzygy full coefficient rank 5.")
