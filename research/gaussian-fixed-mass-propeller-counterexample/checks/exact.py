#!/usr/bin/env python3
"""Independent Q(sqrt(2)) replay of the counterexample's algebra/geometry.

Gaussian integral inequalities and exact volume selection are analytic
proofs in paper.md; this checker does not approximate Gaussian integrals.
"""
from fractions import Fraction as F
import json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


class Q2:
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    def __add__(self, other):
        q = other if isinstance(other, Q2) else Q2(other)
        return Q2(self.a + q.a, self.b + q.b)

    __radd__ = __add__

    def __neg__(self):
        return Q2(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-other if isinstance(other, Q2) else Q2(-other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        q = other if isinstance(other, Q2) else Q2(other)
        return Q2(self.a*q.a + 2*self.b*q.b, self.a*q.b + self.b*q.a)

    __rmul__ = __mul__

    def inverse(self):
        norm = self.a*self.a - 2*self.b*self.b
        need(norm != 0, 'zero denominator')
        return Q2(self.a/norm, -self.b/norm)

    def __truediv__(self, other):
        q = other if isinstance(other, Q2) else Q2(other)
        return self * q.inverse()

    def __eq__(self, other):
        q = other if isinstance(other, Q2) else Q2(other)
        return self.a == q.a and self.b == q.b

    def positive(self):
        a, b = self.a, self.b
        if b == 0:
            return a > 0
        if a == 0:
            return b > 0
        if a > 0 and b > 0:
            return True
        if a < 0 and b < 0:
            return False
        return a*a > 2*b*b if a > 0 else 2*b*b > a*a


def add(x, y):
    return tuple(a+b for a, b in zip(x, y))


def scale(s, x):
    return tuple(s*a for a in x)


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


V = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))
SQRT2 = Q2(0, 1)
NORMAL = (Q2(), SQRT2/2, SQRT2/2)
TANGENT = (Q2(1), Q2(), Q2())


def check(A, B):
    need(0 < A < B, 'positive ordered facet domain')
    ell = 2*SQRT2
    moments = []
    for i in range(4):
        moment = (Q2(), Q2(), Q2())
        for j in range(4):
            if i == j:
                continue
            weight = A if 0 in (i, j) else B
            moment = add(moment, scale(Q2(weight)/ell,
                                       add(V[i], scale(-1, V[j]))))
        moments.append(moment)
    need(sum((m[0] for m in moments), Q2()) == 0 and
         sum((m[1] for m in moments), Q2()) == 0 and
         sum((m[2] for m in moments), Q2()) == 0, 'total moment zero')
    difference = add(moments[0], scale(-1, moments[1]))
    need(dot(difference, TANGENT) == SQRT2*(A-B), 'tangent identity')
    need(dot(difference, NORMAL) == 3*A+B, 'normal identity')
    need((SQRT2*F(1)-F(7, 5)).positive(), 'sqrt2 lower bound')
    eta = (B-A)/(100*(A+B))
    need(0 < eta < F(1, 100), 'exchange radius')
    worst = SQRT2*(B-A) - 2*eta*(3*A+B) - 5*eta*(A+B)
    need((worst - (B-A)).positive(), 'strict swap margin')

    # t=1 is the fixed geometric input; all comparisons are exact.
    apex = V[0]
    q = add((2, 1, 1), scale(-eta, NORMAL))
    r = add((3, 1, 1), scale(eta, NORMAL))
    for label, center in ((1, q), (0, r)):
        relative = add(center, scale(-1, apex))
        for j in range(4):
            if label == j:
                continue
            distance = dot(add(V[label], scale(-1, V[j])), relative)/ell
            need((distance - eta/2).positive(), 'ball contained in its actual cell')
    delta_vector = (Q2(F(1, 13)), Q2(F(-2, 17)), Q2(F(3, 19)))
    before = dot(moments[0], moments[0]) + dot(moments[1], moments[1])
    m1 = add(moments[0], delta_vector)
    m2 = add(moments[1], scale(-1, delta_vector))
    after = dot(m1, m1) + dot(m2, m2)
    need(after-before == 2*dot(difference, delta_vector) +
         2*dot(delta_vector, delta_vector), 'exact exchange identity')
    w = (Q2(F(1, 7)), Q2(F(2, 9)), Q2(F(-1, 11)))
    centered = sum(dot(add(m, scale(-1, w)), add(m, scale(-1, w))) for m in moments)
    need(centered == sum(dot(m, m) for m in moments)+4*dot(w, w), 'centering constant')


def main():
    for a in range(1, 13):
        for b in range(1, 13):
            A = F(a, 7)
            check(A, A+F(b, 11))
    try:
        check(F(2), F(1))
    except RuntimeError:
        pass
    else:
        raise RuntimeError('reversed facet order was accepted')
    print(json.dumps({'status': 'PASS', 'exact_facet_parameter_cases': 144,
        'field': 'Q(sqrt(2))', 'fixed_apex': [1, 1, 1],
        'negative_controls_rejected': 1,
        'scope': 'algebra and ball-containment controls; no numerical Gaussian integrals'},
        indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
