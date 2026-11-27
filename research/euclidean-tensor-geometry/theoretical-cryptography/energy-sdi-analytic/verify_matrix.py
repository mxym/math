#!/usr/bin/env python3
"""Independent exact matrix checks: block inequalities and finite state model."""
from fractions import Fraction as F
from itertools import combinations, permutations


def mat(n, m, f):
    return [[F(f(i, j)) for j in range(m)] for i in range(n)]


def eye(n):
    return mat(n, n, lambda i, j: i == j)


def trn(a):
    return [list(row) for row in zip(*a)]


def add(a, b):
    return mat(len(a), len(a[0]), lambda i, j: a[i][j]+b[i][j])


def sc(a, s):
    return mat(len(a), len(a[0]), lambda i, j: s*a[i][j])


def sub(a, b):
    return add(a, sc(b, -1))


def mm(a, b):
    assert len(a[0]) == len(b)
    return mat(len(a), len(b[0]), lambda i, j: sum(x*y for x, y in zip(a[i], (r[j] for r in b))))


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def ex(a, rho):
    return trace(mm(a, rho))


def kron(a, b):
    n, m = len(b), len(b[0])
    return mat(len(a)*n, len(a[0])*m, lambda i, j: a[i//n][j//m]*b[i%n][j%m])


def det(a):
    n = len(a)
    z = F(0)
    for p in permutations(range(n)):
        d = F((-1)**sum(p[i] > p[j] for i in range(n) for j in range(i+1, n)))
        for i in range(n):
            d *= a[i][p[i]]
        z += d
    return z


def psd(a):
    return (a == trn(a) and all(det([[a[i][j] for j in ids] for i in ids]) >= 0
                                for k in range(1, len(a)+1)
                                for ids in combinations(range(len(a)), k)))


def rot(n, i, j, u):
    c, s = (1-u*u)/(1+u*u), 2*u/(1+u*u)
    v = eye(n)
    v[i][i] = v[j][j] = c
    v[i][j], v[j][i] = -s, s
    assert mm(v, trn(v)) == eye(n)
    return v


def conj(a, u):
    return mm(mm(u, a), trn(u))


def ket(v):
    a = [[F(s)] for s in v]
    return mm(a, trn(a))


def marg(a, d, m):
    return mat(m, m, lambda i, j: sum(a[k*m+i][k*m+j] for k in range(d)))


def function(a, lam, c):
    # Spectral f and positive part derived independently for rational eigenpairs.
    # Here a = U diag(a_0,a_1) U^t with U supplied from the known projector.
    u, vals = a
    f = [lam*z/(lam-1+z) for z in vals]
    return tuple(conj([[x, F(0)], [F(0), y]], u)
                 for x, y in ((f[0], f[1]), (max(0, f[0]-c), max(0, f[1]-c))))


id2, id4 = eye(2), eye(4)
P = kron([[1, 0], [0, 0]], id2)
Q = sub(id4, P)
ms = []
checks = 0
for s, t, ii, jj in ((F(1, 2), F(1, 3), 1, 0), (F(2, 3), F(3, 4), 1, 1),
                      (F(1, 7), F(2, 5), 0, 1), (F(0), F(2, 3), 1, 1),
                      (F(3, 7), F(0), 0, 1)):
    u, v = rot(2, 0, 1, F(1, 4)), rot(2, 0, 1, F(2, 5))
    change = [u[0]+[F(0), F(0)], u[1]+[F(0), F(0)], [F(0), F(0)]+v[0], [F(0), F(0)]+v[1]]
    basis = mm(rot(4, 0, 2, s), rot(4, 1, 3, t))
    a0, a1 = basis[0][0]**2, basis[1][1]**2
    diag = mat(4, 4, lambda i, j: (ii, jj, 0, 0)[i] if i == j else 0)
    R = conj(diag, mm(change, basis))
    N = sub(id4, R)
    assert mm(R, R) == R and R == trn(R)
    vals = (ii*a0, jj*a1)
    A = [row[:2] for row in R[:2]]
    B = [row[:2] for row in R[2:]]
    T = [row[2:] for row in R[2:]]
    assert A == conj([[vals[0], F(0)], [F(0), vals[1]]], u)
    assert mm(trn(B), B) == mm(A, sub(id2, A))
    assert mm(T, B) == mm(B, sub(id2, A))
    ms.append(N)
    for lam, ts in ((F(15, 13), F(1, 3)), (F(3, 2), F(3, 8)),
                    (F(32, 19), F(1, 11)), (F(4), F(0))):
        h = lam*ts/(lam-1+lam*ts)
        c, b = h*h, lam*(lam-1)/(lam-1+lam*ts)**2
        k = b+1-c
        fa, jb = function((u, vals), lam, c)
        fP = kron([[1, 0], [0, 0]], fa)
        assert psd(sub(add(sc(Q, lam), fP), R))
        L = sub(kron(id2, jb), sc(Q, k))
        assert psd(sc(mm(mm(N, L), N), -1))
        assert psd(add(L, sc(id4, k))) and psd(sub(sc(id4, 1-c), L))
        checks += 1
assert not psd([[F(1), F(2)], [F(2), F(1)]])
print(f"two-projection PSD and compression tests: {checks} PASS (negative control detected)")


def bound(w, d, e):
    assert 0 <= w < F(1, 3) and 0 <= d <= 1 and 0 <= e <= F(1, 2)
    c = (2*w/(1-w))**2
    f = w*(5-9*w)/(1-w)
    C = 2*(2-w)*(1-3*w)/(1-w)**2
    x = d-f-(1-c)*e
    assert x <= 0 or x*x <= C*C*e
    return d > f


n = strict = 0
for a, b in ((F(1, 8), F(1, 14)), (F(1, 9), F(1, 10)), (F(1, 13), F(1, 16))):
    # Two Eve flags, with different entangled preparations and a mixed local
    # channel on the second input. Eve's optimal flag reading is classical here.
    pair = []
    for g, (u, q) in enumerate(((a, F(1, 3)), (b, F(2, 3)))):
        a0, a1 = (1-u*u)/(1+u*u), 2*u/(1+u*u)
        rho = sc(ket([a0, 0, 0, (-1)**g*a1]), q)
        sig = add(sc(conj(rho, kron(rot(2, 0, 1, F(1, 14)), id2)), F(4, 5)),
                  sc(conj(rho, kron(rot(2, 0, 1, F(-1, 21)), id2)), F(1, 5)))
        assert psd(rho) and psd(sig) and trace(rho) == trace(sig) == q
        assert marg(rho, 2, 2) == marg(sig, 2, 2)
        pair.append((rho, sig))
    w = max(sum(ex(Q, x[j]) for x in pair) for j in (0, 1))
    for N in ms:
        e = sum(min(ex(N, x), trace(x)-ex(N, x)) for x, _ in pair)
        d = abs(sum(ex(N, sub(x, y)) for x, y in pair))
        strict += bound(w, d, e)
        n += 1
for co, si in ((F(12, 13), F(5, 13)), (F(24, 25), F(7, 25))):
    x, y = ket([co, F(0), si, F(0)]), ket([co, F(0), -si, F(0)])
    N = kron([[F(1, 2), F(1, 2)], [F(1, 2), F(1, 2)]], id2)
    d, e = ex(N, sub(x, y)), 1-ex(N, x)
    assert d == 2*co*si and marg(x, 2, 2) == marg(y, 2, 2)
    strict += bound(si**2, d, e)
    n += 1
print(f"finite shared-marginal model: {n} PASS; {strict} nonzero certificates")

# Compress a qutrit message into levels 0,1; level 2 is replaced by 1.
# The M register uses a four-dimensional index (two qubits, viewed as M,E).
def source_compress(rho):
    y = [row[:8] for row in rho[:8]]
    for i in range(4):
        for j in range(4):
            y[i+4][j+4] += rho[i+8][j+8]
    return y


r = [F(0)]*12
r[0], r[10] = F(12, 13), F(5, 13)
rho = ket(r)
sig = conj(rho, kron(rot(3, 1, 2, F(1, 4)), eye(4)))
for z in (rho, sig, sc(add(rho, sig), F(1, 2))):
    zz = source_compress(z)
    vac = lambda x: sum(x[i][i] for i in range(4))
    assert trace(zz) == trace(z) == 1 and zz == trn(zz)
    assert vac(zz) == vac(z) == F(144, 169)
    assert marg(zz, 2, 4) == marg(z, 3, 4) == marg(rho, 3, 4)
print("vacuum-population and joint ME marginal under compression: 3 PASS")
