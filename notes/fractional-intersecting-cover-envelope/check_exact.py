"""Independent standard-library checker of fixed rational certificates.

No optimization or solver status is trusted. The universal theorem is
proved in paper.md; finite replay supplies diagnostics and boundary cases.
"""
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def phi(c):
    if c <= 1:
        return c / 2
    k = (c.numerator + c.denominator - 1) // c.denominator
    return F(k*(k-1), k*k+k-1-c)


def envelope(r, m):
    k = (m+r-1)//r
    if k == 1:
        return F(m+1, 2)
    return F(k*(k-1)*r*r+(2*k-1)*r+1-m, (k*k+k-1)*r+1-m)


def check_case(case):
    edges = [frozenset(e) for e in case['edges']]
    r, m = len(edges[0]), len(edges)
    require(r >= 2 and len(set(edges)) == m, 'invalid uniform/simple input')
    require(all(len(e) == r for e in edges), 'nonuniform input')
    require(all(e & f for e, f in combinations(edges, 2)), 'not intersecting')
    vertices = set().union(*edges)
    primal = {int(v): F(z) for v, z in case['primal'].items()}
    dual = list(map(F, case['dual']))
    require(set(primal) == vertices and len(dual) == m, 'certificate domain mismatch')
    require(all(z >= 0 for z in primal.values()) and all(y >= 0 for y in dual),
            'negative certificate weight')
    require(all(sum(primal[v] for v in e) >= 1 for e in edges), 'primal infeasible')
    require(all(sum(dual[i] for i, e in enumerate(edges) if v in e) <= 1
                for v in vertices), 'dual infeasible')
    value = sum(primal.values())
    require(value == sum(dual), 'primal/dual objective mismatch')
    bound = envelope(r, m)
    require(value <= bound, 'finite bound failed')
    k = (m+r-1)//r
    linear = all(len(e & f) == 1 for e, f in combinations(edges, 2))
    degk = all(sum(v in e for e in edges) == k for v in vertices)
    if k >= 2:
        equality = m == (k-1)*r+1 and linear and degk
        require((value == bound) == equality, 'equality classification failed')
    # Independently replay both weighted observations.
    Y, b = sum(dual), max(dual)
    p = dual.index(b)
    require(Y <= r-(r-1)*b, 'star weighted count failed')
    if k >= 2 and b > F(1,k+1):
        t = (1-b)/k
        G = [i for i,y in enumerate(dual) if y > t]
        require(p in G and len(G) <= (k-1)*r+1, 'threshold count failed')
        require(all(sum(v in edges[i] for i in G if i != p) <= k-1
                    for v in edges[p]), 'local threshold capacity failed')
        g = (k-1)*r+1
        require(Y <= g*b+(m-g)*t, 'threshold mass failed')
    return r, m, value, bound


def main():
    count = 0
    for r in range(2, 81):
        for m in range(1, 8*r+1):
            k = (m+r-1)//r
            c = F(m,r)
            if k >= 2:
                g = (k-1)*r+1
                require(g <= m <= k*r, 'ceiling domain')
                N = k*(k-1)*r*r+(2*k-1)*r+1-m
                Q = (k*k+k-1)*r+1-m
                require(Q > 0, 'denominator')
                require((k+1)*N-m*Q == (m-(k+1)*g)*(m-k*r-1) > 0,
                        'small-peak factorization')
                require(envelope(r,m) <= r*phi(c)+F(1,k), 'finite error')
                theta = c-k+1
                h = F(k-1,k+1)+c/F(k*(k+1))
                gap = theta*(1-theta)/(k*(k+1)*(k*k-theta))
                require(h-phi(c) == gap >= 0, 'rational interpolation gap')
            count += 1
    print(f'{count} exact parameter/factorization diagnostics PASS')
    gaps = 0
    for k in range(2,10):
        for j in range(1,16):
            theta = F(j,16)
            c = k-1+theta
            p = phi(c)
            a = k-1-theta/k
            b, t = 1-p, p/k
            d = b-t
            e = min(t/4,d/4,(k-1)*d/(4*(k+1)))
            delta = min(a*d/(8*(k+1)),k*t/4)
            M = (F(2)/t).numerator//(F(2)/t).denominator+1
            if F(2)/t == M-1:
                M -= 1
            zeta = min(delta,theta/((a+1)*(2*M/d+(M+1)/e)))
            require(min(a,d,e,delta,zeta) > 0, 'noninteger gap positivity')
            require(p-c/(k+1) == a*k*d/(k+1) > delta, 'small-peak gap')
            bmin, bmax = b-delta/a, b+delta
            require((k+1)*(bmin-e) > 1, 'high threshold margin')
            require(k*(bmin-e)+(1-bmin)/k-e > 1, 'mixed threshold margin')
            require((1-bmax)/k-e >= t/2, 'low positive-weight bound')
            require(bmin-(1-bmin)/k >= d/2, 'threshold separation')
            require(M >= F(2)/t, 'low-edge capacity')
            gaps += 1
    print(f'{gaps} rational noninteger-gap constant diagnostics PASS')
    data = json.loads((ROOT/'results/certificates.json').read_text())
    for case in data['cases']:
        r,m,value,bound = check_case(case)
        print(f"{case['name']}: r={r}, m={m}, tau*={value}, bound={bound} PASS")
    bad = json.loads(json.dumps(data['cases'][0]))
    bad['dual'][0] = '2'
    try:
        check_case(bad)
    except RuntimeError:
        pass
    else:
        raise RuntimeError('infeasible-dual negative control escaped')
    fano = next(c for c in data['cases'] if c['name'] == 'projective plane order 2')
    r,m,value,bound = check_case(fano)
    require(value > r*phi(F(m,r)), 'missing-correction negative control')
    e = list(map(set, fano['edges']))
    vertices = sorted(set().union(*e))
    require(all(not all(set(pair) & E for E in e) for pair in combinations(vertices,2)),
            'Fano integer boundary')
    require(all(set(e[0]) & E for E in e), 'Fano three-cover')
    require(F(3) > bound, 'integer-promotion negative control')
    print('Infeasible dual, omitted correction and integer-promotion negative controls PASS')


if __name__ == '__main__':
    main()
