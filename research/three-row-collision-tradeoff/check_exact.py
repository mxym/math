#!/usr/bin/env python3
"""Exact independent regression for all-width 3-row collision energies.

Standard Python 3.10+. No floating arithmetic, solver, random-number generator,
optimizer or assert-based checks. All matrices have Gaussian-rational entries.
"""
from fractions import Fraction as Q
from itertools import combinations, permutations
from dataclasses import dataclass


@dataclass(frozen=True)
class Z:
    x: Q
    y: Q = Q(0)

    def __add__(self, b):
        return Z(self.x + b.x, self.y + b.y)

    def __sub__(self, b):
        return Z(self.x - b.x, self.y - b.y)

    def __mul__(self, b):
        return Z(self.x * b.x - self.y * b.y, self.x * b.y + self.y * b.x)

    def conj(self):
        return Z(self.x, -self.y)

    def norm2(self):
        return self.x * self.x + self.y * self.y


def z(x=0, y=0):
    return Z(Q(x), Q(y))


ZERO, ONE = z(), z(1)
PERMS3 = tuple(permutations(range(3)))


def check(ok, context):
    if not ok:
        raise RuntimeError("FAILED: " + context)


def equal(x, y, context):
    check(x == y, context + " [" + str(x) + " != " + str(y) + "]")


def inner(a, b):
    return sum((ai * bi.conj() for ai, bi in zip(a, b)), ZERO)


def squared(a):
    return sum((ai.norm2() for ai in a), Q(0))


def perm3(a):
    return sum((a[0][p[0]] * a[1][p[1]] * a[2][p[2]] for p in PERMS3), ZERO)


def sign(p):
    return -1 if sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p))) % 2 else 1


def det3(a):
    ans = ZERO
    for p in PERMS3:
        term = a[0][p[0]] * a[1][p[1]] * a[2][p[2]]
        ans = ans + term if sign(p) == 1 else ans - term
    return ans


def energies3(U):
    n = len(U[0])
    check(len(U) == 3 and all(len(v) == n for v in U), "matrix dimensions")
    ps = ds = Q(0)
    for cols in combinations(range(n), 3):
        M = [[row[j] for j in cols] for row in U]
        ps += perm3(M).norm2()
        ds += det3(M).norm2()
    return ps, ds


def perm2(u, v, j, k):
    return u[j] * v[k] + u[k] * v[j]


def det2(u, v, j, k):
    return u[j] * v[k] - u[k] * v[j]


def energies2(u, v):
    p = d = Q(0)
    for j, k in combinations(range(len(u)), 2):
        p += perm2(u, v, j, k).norm2()
        d += det2(u, v, j, k).norm2()
    return p, d


def Gram3(U):
    return [[inner(U[i], U[j]) for j in range(3)] for i in range(3)]


def bosonic_collision(U):
    G = Gram3(U)
    P = perm3(G).x
    S, W = energies3(U)
    check(det3(G).y == 0 and perm3(G).y == 0, "Gram per/det real")
    equal(det3(G).x, W, "Cauchy Binet")
    check(P >= S, "bosonic collision nonnegative")
    triple_sum = Q(0)
    for j in range(len(U[0])):
        u, v, w = U
        qj = [u[j] * v[j] * w[k] + u[j] * w[j] * v[k] + v[j] * w[j] * u[k] for k in range(len(u))]
        triple_sum += squared(qj)
    Dformula = 2 * triple_sum - 12 * sum(
        (U[0][j] * U[1][j] * U[2][j]).norm2() for j in range(len(U[0]))
    )
    equal(P - S, Dformula, "collision coefficient identity")
    return S, W, P


def phase_sample(n, shift):
    pool = [
        z(1), z(-1), z(0, 1), z(0, -1),
        z(Q(3, 5), Q(4, 5)), z(Q(3, 5), -Q(4, 5)),
        z(Q(5, 13), Q(12, 13)), z(-Q(5, 13), Q(12, 13)),
    ]
    return [[pool[(i * 7 + j * (i + 2) + shift * (i + 1) * (j + 3)) % len(pool)]
             for j in range(n)] for i in range(3)]


def flat_bound_checks():
    count = 0
    for n in range(3, 11):
        A = Q(1) - Q(6, n) + Q(12, n*n)
        B = Q(1) - Q(4, n)
        C = Q(6 * (n-1) * (n-2), n*n)
        d = C-A
        for seed in range(16):
            U = phase_sample(n, seed)
            P, D, PP = bosonic_collision(U)
            denom = n**3
            P, D = P/denom, D/denom
            G = Gram3(U)
            a, b, e = G[0][1], G[1][2], G[2][0]
            s = (a.norm2() + b.norm2() + e.norm2())/n**2
            t = (a*b*e).x/n**3
            equal(P, A + B*s + 2*t, "flat permanent formula n=%s seed=%s" % (n,seed))
            equal(D, 1-s+2*t, "flat Gram determinant formula")
            for c in (Q(0), Q(1), Q(7,3), d, d+1, Q(5), Q(13,2)):
                check(P+c*D <= max(C, A+c), "flat objective n=%s seed=%s c=%s" % (n,seed,c))
                count += 1
        # Parallel witness attains C at all widths
        parallel = [[ONE for j in range(n)] for i in range(3)]
        S, W = energies3(parallel)
        equal(S/n**3, C, "parallel sharp endpoint")
        equal(W, 0, "parallel determinant")
        count += 1
        if n % 4 == 0:
            i = z(0,1)
            row = [ONE,i,z(-1),z(0,-1)]
            orth = [[ONE]*n, [ONE if j%2 == 0 else z(-1) for j in range(n)],
                    [row[j%4] for j in range(n)]]
            S, W = energies3(orth)
            equal(S/n**3, A, "Fourier orthogonal permanent endpoint")
            equal(W/n**3, Q(1), "Fourier orthogonal determinant endpoint")
            count += 1
    return count


def coordinate_checks():
    count = 0
    for n in range(3, 11):
        for shift in range(7):
            U = phase_sample(n,shift)
            U[0] = [ONE if k == shift % n else ZERO for k in range(n)]
            S,W = energies3(U)
            j = shift % n
            p, q = [[x for k,x in enumerate(row) if k!=j] for row in U[1:]]
            Ps, Ws = energies2(p,q)
            equal(S,Ps,"coordinate reduction S")
            equal(W,Ws,"coordinate reduction W")
            for c in (Q(0),Q(1),Q(7,3),Q(5)):
                check(S+c*W <= max(Q(2)-Q(2,n-1),1+c)*squared(p)*squared(q),
                      "coordinate two-row sharp")
                count+=1
    return count


def johnson_checks():
    count = 0
    for n in range(3, 10):
        edges = list(combinations(range(n),2))
        tris = list(combinations(range(n),3))
        edge_set = list(map(set,edges))
        for shift in range(7):
            U = phase_sample(n,shift)
            U[0] = [ONE]*n
            S,_ = energies3(U)
            v,w = U[1:]
            y = {e:v[e[0]]*w[e[1]]+v[e[1]]*w[e[0]] for e in edges}
            value = sum((sum((y[e] for e in combinations(T,2)),ZERO).norm2() for T in tris),Q(0))
            equal(S,value,"Johnson minor-incidence identity")
            count+=1
        for idx,E in enumerate(edges):
            for jdx,F in enumerate(edges):
                B2 = sum(set(E).issubset(T) and set(F).issubset(T) for T in tris)
                C2 = len(edge_set[idx].intersection(edge_set[jdx]))
                equal(B2, (n-4)*(idx==jdx)+C2,"Johnson exact Gram identity")
                count+=1
    return count


def high_weight_checks():
    count = 0
    for n in range(3, 9):
        for shift in range(12):
            U = phase_sample(n,shift)
            if shift % 4 == 0:
                U[0] = [ONE if j==0 else ZERO for j in range(n)]
            if shift % 4 == 1:
                U[1] = [ONE if j==1 else ZERO for j in range(n)]
            S, W = energies3(U)
            prod = squared(U[0])*squared(U[1])*squared(U[2])
            for c in (Q(5),Q(6),Q(17,2)):
                check(S+c*W <= (1+c)*prod,"global high-weight theorem")
                count+=1
    # Distinct supports including nonsingletons give exact equality for any weight.
    U = [[ONE,z(2),ZERO,ZERO,ZERO,ZERO],
         [ZERO,ZERO,ONE,z(0,2),ZERO,ZERO],
         [ZERO,ZERO,ZERO,ZERO,ONE,z(-3)]]
    S,W = energies3(U)
    prod = squared(U[0])*squared(U[1])*squared(U[2])
    equal(S,prod,"nonmonomial high-weight equality permanent")
    equal(W,prod,"nonmonomial high-weight equality determinant")
    count+=1
    return count


def shortcut_negative_control():
    U = [[ZERO]+[ONE]*5,[ONE]+[ZERO]*5,[ZERO]+[ONE]*5]
    S,W,PP=bosonic_collision(U)
    scale=Q(25)
    equal(S/scale,Q(8,5),"negative witness S")
    equal(PP/scale,Q(2),"negative witness Gram permanent")
    equal(W,Q(0),"negative witness determinant")
    gap=Q(9)*S/scale-Q(5)*PP/scale-Q(4)*W/scale
    equal(gap,Q(22,5),"negative witness Gram shortcut gap")
    check(gap>0,"invalid stronger conjecture correctly rejected")
    return gap



def check_two_flat_general_formula():
    """Independent complex-rational replay of the general identity (27)."""
    count = 0
    for n in range(3, 9):
        for seed in range(8):
            U = [[z(Q((3*i+2*j+seed)%9-4, 5),
                    Q((i*i+j*seed+2)%7-3, 4))
                  for j in range(n)] for i in range(3)]
            u, v, w = U
            S, W, P = bosonic_collision(U)
            aa = inner(u, v)
            pu = [x.norm2() for x in u]
            pv = [x.norm2() for x in v]
            nu, nv = squared(u), squared(v)
            rhs = 2 * sum(pu[j]*pv[j] for j in range(n))*squared(w)
            rhs += 2 * sum((pu[j]*nv+pv[j]*nu)*w[j].norm2() for j in range(n))
            rhs -= 12 * sum(pu[j]*pv[j]*w[j].norm2() for j in range(n))
            rhs += 4 * sum(
                ((u[j]*v[j].conj())*aa.conj()).x*w[j].norm2()
                for j in range(n))
            pw = [z(pu[j])*v[j] for j in range(n)]
            qw = [z(pv[j])*u[j] for j in range(n)]
            rhs += 4 * (
                inner(pw,w)*inner(v,w).conj()+
                inner(qw,w)*inner(u,w).conj()).x
            equal(P-S, rhs, "general collision expansion n=%s seed=%s" % (n, seed))
            count += 1
    return count


def two_flat_critical_checks():
    """Two flat rows, fully arbitrary complex-rational third row."""
    count = 0
    for seed in range(176):
        u, v = phase_sample(6,seed)[:2]
        w = [
            z(Q((j+3*seed)%13-6,7), Q((j*j+2*seed)%11-5,9))
            for j in range(6)]
        if seed%3 == 0:
            w[seed%6] = ZERO
        if seed%5 == 0:
            u = [ui*z(2,1) for ui in u]
        if seed%7 == 0:
            v = [vi*z(3,-2) for vi in v]
        U = [u,v,w]
        S, W = energies3(U)
        G = Gram3(U)
        aa,bb,dd = G[0][1], G[1][2], G[2][0]
        cyc = (aa*bb*dd).x
        P = perm3(G).x
        deficit = P-S
        check(deficit >= Q(8,3)*cyc, "two-flat collision Theorem 7")
        prod = squared(u)*squared(v)*squared(w)
        check(S+Q(7,3)*W <= Q(10,3)*prod, "two-flat critical Corollary 8")
        if seed%5 != 0 and seed%7 != 0:
            # Original unnormalized collision identity with two unit-phase rows.
            rhs = 24*squared(w) + 4*(inner(u,w).norm2()+
                                    inner(v,w).norm2()) + 4*sum(
                ((u[j]*v[j].conj())*aa.conj()).x*w[j].norm2()
                for j in range(6))
            equal(deficit, rhs, "two-flat quadratic polynomial identity")
        count += 1
    flat = [[ONE]*6 for _ in range(3)]
    S, W = energies3(flat)
    G=Gram3(flat)
    delta = perm3(G).x-S
    cyc = (G[0][1]*G[1][2]*G[2][0]).x
    equal(delta,Q(8,3)*cyc,"sharp universal two-flat coefficient")
    check(delta < (Q(8,3)+Q(1,100))*cyc,
          "sharp collision coefficient negative control")
    equal(S+Q(7,3)*W,Q(10,3)*Q(6**3),
          "sharp two-flat critical endpoint")
    return count+1


def check_rank_one_factorization():
    """Exact bivariate integer polynomial verification of equation (36)."""
    def const(c):
        return {(0,0):int(c)} if c else {}
    def plus(P,Q):
        R=P.copy()
        for k,v in Q.items():
            R[k]=R.get(k,0)+v
            if R[k]==0:del R[k]
        return R
    def neg(P):
        return {k:-v for k,v in P.items()}
    def minus(P,Q):
        return plus(P,neg(Q))
    def mul(P,Q):
        R={}
        for (i,j),a in P.items():
            for (k,l),b in Q.items():
                h=(i+k,j+l)
                R[h]=R.get(h,0)+a*b
        return {k:v for k,v in R.items() if v}
    def scale(P,n):
        return {k:n*v for k,v in P.items() if n*v}
    one=const(1);m={(1,0):1};A={(0,1):1}
    m2=mul(m,m)
    den=mul(m2,minus(mul(plus(const(5),scale(m2,4)),A),const(3)))
    k=minus(one,mul(plus(one,scale(m2,2)),A))
    fourm2=minus(scale(m2,4),one)
    left=minus(den,mul(fourm2,minus(mul(A,den),mul(k,k))))
    right=mul(mul(minus(one,m2),
                  plus(one,mul(minus(scale(m,2),one),A))),
              minus(mul(plus(scale(m,2),one),A),one))
    equal(left,right,"exact bivariate polynomial factorization (36)")
    return len(left)

def main():
    print("Gaussian-rational independent replay; integers/Fraction only")
    print("flat-formula/objective checks:",flat_bound_checks())
    print("coordinate-row checks:",coordinate_checks())
    print("Johnson-incidence checks:",johnson_checks())
    print("all-width high-determinant checks:",high_weight_checks())
    print("general three-row collision formula checks:",check_two_flat_general_formula())
    print("sharp two-flat critical checks:",two_flat_critical_checks())
    print("rank-one inversion factor identity monomials:",check_rank_one_factorization())
    print("stronger Gram shortcut is false, exact gap:",shortcut_negative_control())
    print("PASS: exact all-n formula checks and two-flat six-column tests; unrestricted six-row case OPEN")


if __name__=="__main__":
    main()
