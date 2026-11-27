#!/usr/bin/env python3
"""Exact rational checks for the quartic Gaussian transport expansion."""
from fractions import Fraction as F
from itertools import product


def mm(A, B):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]


def plus(A, B):
    return [[a+b for a,b in zip(r,s)] for r,s in zip(A,B)]


def qform(A, x):
    return sum(x[i]*A[i][j]*x[j] for i,j in product(range(len(x)),repeat=2))


def trace(A):
    return sum(A[i][i] for i in range(len(A)))


def invsolve(A, b):
    aug = [list(map(F,row))+[F(y)] for row,y in zip(A,b)]
    n = len(A)
    for j in range(n):
        k = next(k for k in range(j,n) if aug[k][j])
        aug[j], aug[k] = aug[k], aug[j]
        v = aug[j][j]
        aug[j] = [x/v for x in aug[j]]
        for k in range(n):
            if k != j:
                c = aug[k][j]
                aug[k] = [u-c*v for u,v in zip(aug[k],aug[j])]
    return [row[-1] for row in aug]


def lyapunov(C, M):
    n = len(C)
    indices = tuple(product(range(n),repeat=2))
    A = [[(i==a)*C[b][j]+C[i][a]*(j==b) for a,b in indices] for i,j in indices]
    sol = invsolve(A, [M[i][j] for i,j in indices])
    return [sol[k:k+n] for k in range(0,n*n,n)]


def gram(A):
    return mm(A, list(zip(*A)))


def check_covariances():
    count = 0
    for C, M in (
        ([[1]], [[F(1,12)]]),
        ([[2,1],[1,3]], [[F(1,12),0],[0,F(1,3)]]),
        (gram([[2,1,0],[0,2,1],[1,0,3]]),
         gram([[2,0,1],[1,3,1],[0,1,2]])),
        ([[2,0,0],[0,7,0],[0,0,5]],
         gram([[2,0,1],[1,3,1],[0,1,2]])),
    ):
        n = len(C)
        I = [[int(i==j) for j in range(n)] for i in range(n)]
        cols = [invsolve(C,e) for e in I]
        K = list(map(list,zip(*cols)))
        D = lyapunov(C,M)
        assert D == list(map(list,zip(*D))) and plus(mm(D,C),mm(C,D)) == M
        assert trace(mm(K,M)) == 2*trace(D)
        assert trace(mm(mm(D,C),D)) == trace(mm(D,M))/2 > 0
        if n == 1:
            assert trace(mm(mm(D,C),D)) == F(1,576)
        if all(C[i][j]==0 for i,j in product(range(n),repeat=2) if i!=j):
            assert trace(mm(mm(D,C),D)) == sum(M[i][j]**2/F(2*(C[i][i]+C[j][j]))
                                                for i,j in product(range(n),repeat=2))
        for x in product(range(-2,3),repeat=n):
            a = trace(D)-qform(mm(D,K),x)
            b = (qform(mm(mm(K,M),K),x)-trace(mm(K,M)))/2
            assert a+b == 0
            count += 1
    assert mm([[2,1],[1,3]],[[1,0],[0,4]]) != mm([[1,0],[0,4]],[[2,1],[1,3]])
    return count


def clip(poly,a,b,c):
    if not poly:
        return []
    val = lambda p: a*p[0]+b*p[1]-c
    ans = []
    for x,y in zip(poly, poly[1:]+poly[:1]):
        vx,vy = val(x),val(y)
        if vx<=0:
            ans.append(x)
        if vx*vy<0:
            t = vx/(vx-vy)
            ans.append(tuple((1-t)*u+t*v for u,v in zip(x,y)))
    return ans


def voronoi(B):
    poly=[(F(-2),F(-2)),(F(2),F(-2)),(F(2),F(2)),(F(-2),F(2))]
    for i,j in product(range(-2,3),repeat=2):
        if i or j:
            a,b = [2*(row[0]*i+row[1]*j) for row in B]
            poly=clip(poly,a,b,qform(B,(i,j)))
    return poly


def moment(poly):
    area, xx, yy, xy = [F(0) for _ in range(4)]
    for (x,y),(u,v) in zip(poly,poly[1:]+poly[:1]):
        d = x*v-u*y
        area += d/2
        xx += d*(x*x+x*u+u*u)/12
        yy += d*(y*y+y*v+v*v)/12
        xy += d*(2*x*y+x*v+u*y+2*u*v)/24
    return area, [[xx/area,xy/area],[xy/area,yy/area]]


def geometry():
    A0,M0=moment(voronoi([[1,0],[0,1]]))
    assert A0==1 and M0==[[F(1,12),0],[0,F(1,12)]]
    count = 0
    for k,a,b,c in product((32,64,128,256),(-1,0,2),(-1,1),(0,1)):
        eps=F(1,k)
        B=[[1+eps*a,eps*b],[eps*b,1+eps*c]]
        P=voronoi(B)
        # The test instance has spectrum between 3/4 and 5/4 by row
        # sums; vertices below have norm <=1, so all omitted shifts
        # (of Euclidean norm >=3) satisfy their bisector constraints.
        assert all(x*x+y*y<=1 for x,y in P)
        A,M=moment(P)
        assert A==1 and 0 <= trace(M)-trace(M0) <= 20*eps*eps
        count += 1
    return count


if __name__ == "__main__":
    print(f"PASS: {check_covariances()} exact Lyapunov cancellations, "
          f"{geometry()} rational planar Voronoi moment perturbations")
