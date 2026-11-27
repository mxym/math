#!/usr/bin/env python3
"""Recover all extensions using direct sum-rank over F4[b]/(b^2+b+w)."""
from itertools import combinations, product

if not __debug__:
    raise RuntimeError("Run without -O; assertions are the checks.")

S=((0,0,0,0),(0,1,2,3),(0,2,3,1),(0,3,1,2)) # F4, w=2
F=tuple(range(4))
K=tuple(range(16))
def mult(x,y):
    a,b=x%4,x//4
    c,d=y%4,y//4
    bd=S[b][d]
    # b_generator^2 = b_generator + w.
    return (S[a][c]^S[2][bd])+4*(S[a][d]^S[b][c]^bd)

M=[[mult(x,y) for y in K] for x in K]
INV=[0]+[M[x].index(1) for x in K[1:]]
assert all(M[x][i]==1 for x,i in enumerate(INV) if x)

def mulvec(x,v):
    return tuple(M[x][a] for a in v)

def plus(u,v):
    return tuple(a^b for a,b in zip(u,v))

def unit(v):
    return mulvec(INV[next(x for x in v if x)],v)

def dot(l,x):
    out=0
    for a,b in zip(l,x):
        out^=M[a][b]
    return out

def line_samples():
    # On a standard K-projective line every rank-two F4-subspace, up to a
    # common K scalar, has a normalized first vector and some nonzero scaling
    # of a distinct normalized projective ray as second vector.
    rays=[(1,a) for a in K]+[(0,1)]
    U={}
    for a,b in combinations(rays,2):
        for lam in K[1:]:
            beta=mulvec(lam,b)
            pts=tuple(sorted({b}|{unit(plus(a,mulvec(t,beta))) for t in F}))
            assert len(pts)==5
            U.setdefault(pts,(a,beta))
    assert len(U)==68
    return list(U.values())

def deficit(codeword1,codeword2):
    if not codeword1 and not codeword2:
        return 2
    if not codeword1 or not codeword2:
        return 1
    return int(M[codeword1][INV[codeword2]] in F)

def main():
    # The quotient field has b_generator=4, b_generator^4=b_generator+1.
    theta=4
    bar=M[M[theta][theta]][M[theta][theta]]
    assert bar==theta^1
    A=((bar,0,theta),(1,0,1))
    B=((0,bar,theta),(0,1,1))
    normals=[(1,y,z) for y,z in product(K,repeat=2)]+[(0,1,z) for z in K]+[(0,0,1)]

    def weight_vector(cols):
        a,b=cols
        return [deficit(dot(n,a),dot(n,b)) for n in normals]

    fixed=[a+b for a,b in zip(weight_vector(A),weight_vector(B))]
    assert max(fixed)==2
    assert max(a+b for a,b in zip(fixed,weight_vector(A)))>2
    witnesses=[]
    subspaces=line_samples()
    for l in normals:
        rays=[v for v in normals if dot(l,v)==0]
        assert len(rays)==17
        u,v=rays[:2]
        for a,b in subspaces:
            def lift(w):
                return plus(mulvec(w[0],u),mulvec(w[1],v))
            X,Y=lift(a),lift(b)
            if any(d+deficit(dot(n,X),dot(n,Y))>2
                   for d,n in zip(fixed,normals)):
                continue
            witnesses.append((l,weight_vector((X,Y))))
    assert len(witnesses)==7 and len({l for l,v in witnesses})==6
    min_distances={6-max(a+b for a,b in zip(fixed,v)) for l,v in witnesses}
    assert min_distances=={4}
    four_block_distances=[8-max(x+y+z for x,y,z in zip(fixed,v,w))
                          for (_,v),(_,w) in combinations(witnesses,2)]
    assert len(four_block_distances)==21 and max(four_block_distances)<6
    print("Rank: 273 message rays; 68 sublines per support; 7 admissible triples")
    print("All triple distances are 4; no extension to a 4-block distance 6 code")
    print("Duplicated-block negative control PASS")

if __name__=="__main__":
    main()
