"""Exact finite periodic-sieve certificates for quadratic orders.

Standard-library only. This checks a supplied finite candidate; it does not run
an unbounded search. Successful certificates are sufficient independently of the
analytic sieve proof. Coefficient model: omega**2 = u*omega + v.
"""
if not __debug__:
    raise RuntimeError("Run this certificate checker without Python optimization flags")

from math import isqrt
from collections import deque
import json


def prime(p):
    return isinstance(p, int) and p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def norm(x, u, v):
    a, b = x
    return a*a + u*a*b - v*b*b


def kernel_row(alpha, p, u, v):
    a, b = alpha
    # Adjugate rows annihilate the multiplication matrix modulo its determinant.
    for row in ((a + u*b, -v*b), (-b, a)):
        row = tuple(z % p for z in row)
        if row != (0, 0):
            assert (row[0]*a + row[1]*b) % p == 0
            assert (row[0]*v*b + row[1]*(a+u*b)) % p == 0
            return row
    raise ValueError('Multiplication matrix is zero modulo p')


def prepare(data):
    u, v = data['u'], data['v']
    assert isinstance(u, int) and isinstance(v, int)
    disc = u*u + 4*v
    assert disc < 0 or isqrt(disc)**2 != disc, 'Not a quadratic field'
    steps = [tuple(d) for d in data['steps']]
    assert all(len(d) == 2 and all(isinstance(x, int) for x in d) for d in steps)
    assert (0, 0) not in steps and len(set(steps)) == len(steps)
    assert all((-a, -b) in steps for a, b in steps), 'Steps must be symmetric'
    Q, maps, seen = 1, [], set()
    for entry in data['primes']:
        p, alpha = entry['p'], tuple(entry['alpha'])
        assert prime(p) and p not in seen
        assert len(alpha) == 2 and all(isinstance(x, int) for x in alpha)
        assert abs(norm(alpha, u, v)) == p
        a, b = alpha
        rows = (kernel_row(alpha, p, u, v), kernel_row((a+u*b, -b), p, u, v))
        assert (rows[0][0]*rows[1][1]-rows[0][1]*rows[1][0]) % p, 'Conjugate kernels coincide'
        maps.append((p, rows))
        seen.add(p)
        Q *= p
    allowed = {(a, b) for a in range(Q) for b in range(Q)
               if all((r[0]*a+r[1]*b) % p for p, rows in maps for r in rows)}
    return Q, steps, allowed


def edges(r, Q, steps, allowed):
    for d in steps:
        target = ((r[0]+d[0]) % Q, (r[1]+d[1]) % Q)
        if target in allowed:
            voltage = ((r[0]+d[0]-target[0])//Q, (r[1]+d[1]-target[1])//Q)
            yield target, voltage


def make_certificate(data):
    Q, steps, allowed = prepare(data)
    potentials = {}
    for root in sorted(allowed):
        if root in potentials:
            continue
        potentials[root] = (0, 0)
        queue = deque([root])
        while queue:
            r = queue.popleft()
            for s, k in edges(r, Q, steps, allowed):
                h = (potentials[r][0]+k[0], potentials[r][1]+k[1])
                if s in potentials:
                    if potentials[s] != h:
                        return None  # A nonzero-voltage closed walk exists.
                else:
                    potentials[s] = h
                    queue.append(s)
    return {'Q': Q, 'potentials': [[*r, *potentials[r]] for r in sorted(potentials)]}


def verify_certificate(data, certificate):
    # Independently checks every directed edge equation, without reusing BFS.
    Q, steps, allowed = prepare(data)
    assert certificate['Q'] == Q
    rows = certificate['potentials']
    assert all(len(row) == 4 and all(isinstance(x, int) for x in row) for row in rows)
    potentials = {tuple(row[:2]): tuple(row[2:]) for row in rows}
    assert len(potentials) == len(rows) and set(potentials) == allowed
    for r in allowed:
        for s, k in edges(r, Q, steps, allowed):
            assert potentials[s] == (potentials[r][0]+k[0], potentials[r][1]+k[1])
    return True


def uniform_bound(data, certificate):
    verify_certificate(data, certificate)
    Q = certificate['Q']
    B = Q*Q
    Delta = len(data['steps'])
    if not data['primes']:
        return B
    M = max(x['p'] for x in data['primes'])
    H = max((abs(x) for d in data['steps'] for x in d), default=0)
    # Every passage between exceptional vertices uses at most B+1 steps.
    difference_bound = (2*(B+1)*H + 1)**2 - 1
    exceptional_bound = max(1, 8*M*M*difference_bound)
    return max(B, exceptional_bound*(1+Delta*B))


def self_test():
    # With no offsets every lattice vertex is isolated, even with no sieve.
    empty = {'u': 0, 'v': -1, 'primes': [], 'steps': []}
    cert = make_certificate(empty)
    assert verify_certificate(empty, cert) and uniform_bound(empty, cert) == 1
    # Modulus-one quotient has a nonzero-voltage loop: the infinite line.
    line = dict(empty, steps=[[1, 0], [-1, 0]])
    assert make_certificate(line) is None
    # Gaussian split prime 5, horizontal unit steps: periodically broken rows.
    gaussian = dict(line, primes=[{'p': 5, 'alpha': [2, 1]}])
    cert = make_certificate(gaussian)
    assert cert is not None and verify_certificate(gaussian, cert)
    assert uniform_bound(gaussian, cert) > 0
    broken = json.loads(json.dumps(cert))
    broken['potentials'][0][2] += 1
    try:
        verify_certificate(gaussian, broken)
    except AssertionError:
        pass
    else:
        raise AssertionError('Tampered potential certificate accepted')
    # Unit multiples of 5 preserve residue classes and give infinite lines.
    infinite = dict(gaussian, steps=[[5, 0], [-5, 0]])
    assert make_certificate(infinite) is None
    # Real quadratic order Z[sqrt(2)] and a norm-seven generator.
    real = {'u': 0, 'v': 2, 'primes': [{'p': 7, 'alpha': [3, 1]}],
            'steps': [[1, 0], [-1, 0]]}
    cert = make_certificate(real)
    assert cert is not None and verify_certificate(real, cert)
    # Ramified norm-two generator has coincident kernels and is rejected.
    try:
        prepare(dict(empty, primes=[{'p': 2, 'alpha': [1, 1]}]))
    except AssertionError:
        pass
    else:
        raise AssertionError('Ramified generator accepted')
    print('Seven exact certificate tests passed.')


if __name__ == '__main__':
    self_test()
