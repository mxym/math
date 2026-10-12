#!/usr/bin/env python3
"""Exact regressions for global-next.md; no assertions disabled by python -O."""
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import factorial


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def det3(vs):
    a, b, c = vs
    return (a[0]*(b[1]*c[2]-b[2]*c[1])
            -b[0]*(a[1]*c[2]-a[2]*c[1])
            +c[0]*(a[1]*b[2]-a[2]*b[1]))


def cofactors(vs):
    return [abs(det3(vs[:j]+vs[j+1:])) for j in range(4)]


def phi(vs):
    return min(cofactors(vs))


def det_any(vs):
    rows = [list(row) for row in zip(*vs)]
    value = F(1)
    for j in range(len(rows)):
        pivot = next((i for i in range(j,len(rows)) if rows[i][j]),None)
        if pivot is None:
            return F(0)
        if pivot!=j:
            rows[j], rows[pivot] = rows[pivot], rows[j]
            value = -value
        p = rows[j][j]
        value *= p
        for i in range(j+1,len(rows)):
            multiplier = rows[i][j]/p
            for k in range(j+1,len(rows)):
                rows[i][k] -= multiplier*rows[j][k]
    return value


def multiply(xs):
    value = F(1)
    for x in xs:
        value *= x
    return value


parameters = [F(1,2), F(1,3), F(1,4), F(1,5), F(1,8),
              F(1,16), F(2,7), F(3,11)]
total_tuples = 0
product_dimension_cases = 0
for e in parameters:
    zero = F(0)
    one = F(1)
    zs = [(one,zero,zero), (zero,one,zero), (zero,zero,one),
          (one,e,zero), (zero,one,e)]
    V = 8-4*e+e**2-e**3/3
    cs = [2-e/2, 2-e, 4-3*e+e**2-e**3/2,
          2-e/2, 2-e+e**2/2]
    ps = [2*c/(3*V) for c in cs]
    require(sum(ps)==1, "cone masses do not sum to one")
    require(ps[3]>=F(1,8) and ps[4]>=F(1,8), "uniform pair mass")
    A = sum(6*ps[i]*ps[j]*ps[k]*abs(det3([zs[i],zs[j],zs[k]]))
            for i,j,k in combinations(range(5),3))
    Af = 6*(ps[0]*ps[1]*ps[2]+e*ps[0]*ps[1]*ps[4]
            +e*ps[0]*ps[2]*ps[3]+ps[0]*ps[2]*ps[4]
            +e**2*ps[0]*ps[3]*ps[4]+ps[1]*ps[2]*ps[3]
            +e*ps[1]*ps[3]*ps[4]+ps[2]*ps[3]*ps[4])
    require(A==Af and A>0, "determinant expectation")
    Ephi = F(0)
    Delta = F(0)
    for types in product(range(5),repeat=4):
        vs = [zs[i] for i in types]
        weight = ps[types[0]]*ps[types[1]]*ps[types[2]]*ps[types[3]]
        cofs = cofactors(vs)
        M = sum(cofs)
        averaged = sum(abs(sum(s*c for s,c in zip(signs,cofs)))
                       for signs in product([-1,1],repeat=4))/16
        defect = M/2-averaged
        require(defect>=0, "balanced defect negative")
        require(all(2*c<=M for c in cofs), "cofactor balance")
        exceptional = set(types)=={0,2,3,4}
        require(min(cofs)==(e**2 if exceptional else 0), "fourth cofactor")
        require(defect==(e**2/2 if exceptional else 0), "defect classification")
        Ephi += weight*min(cofs)
        Delta += weight*defect
        total_tuples += 1
    pp = ps[0]*ps[2]*ps[3]*ps[4]
    require(Ephi==24*pp*e**2, "fourth-cofactor expectation")
    require(Delta==12*pp*e**2, "deficit expectation")
    require(Delta/(4*A)==3*pp*e**2/A, "scalar invariant normalization")
    q_section = sum(ps[i]*phi(zs[:3]+[zs[i]]) for i in range(5))
    for j in range(3):
        base = zs[:j]+zs[j+1:3]
        q_section += sum(ps[i]*ps[k]*phi(base+[zs[i],zs[k]])
                         for i,k in product(range(5),repeat=2))
    require(q_section==2*ps[3]*ps[4]*e**2, "simultaneous section cost")
    costs = [ps[4]*e, ps[3]*e, (ps[3]+ps[4])*e, (ps[3]+ps[4])*e]
    require(min(costs)==e*min(ps[3],ps[4]) and min(costs)>=e/8,
            "coordinate product cost")

    for d in range(3,7):
        vectors = [tuple(v)+(F(0),)*(d-3) for v in zs]
        vectors += [tuple(F(i==j) for i in range(d)) for j in range(3,d)]
        probabilities = [F(3,d)*p for p in ps]+[F(1,d)]*(d-3)
        require(sum(probabilities)==1, "product cone mass")
        Ad = sum(factorial(d)*multiply(probabilities[i] for i in inds)
                 *abs(det_any([vectors[i] for i in inds]))
                 for inds in combinations(range(d+2),d))
        phid = F(0)
        Deltad = F(0)
        for inds in combinations(range(d+2),d+1):
            points = [vectors[i] for i in inds]
            cofs = [abs(det_any(points[:j]+points[j+1:])) for j in range(d+1)]
            mass = factorial(d+1)*multiply(probabilities[i] for i in inds)
            averaged = sum(abs(sum(s*c for s,c in zip(signs,cofs)))
                           for signs in product([-1,1],repeat=d+1))/2**(d+1)
            phid += mass*sorted(cofs,reverse=True)[3]
            Deltad += mass*(sum(cofs)/2-averaged)
        require(Ad==F(factorial(d)*27,6*d**d)*A, "product determinant mass")
        require(phid==F(factorial(d+1)*81,d**(d+1))*pp*e**2,
                "product fourth cofactor")
        require(Deltad/((d+1)*Ad)==F(3,d)*Delta/(4*A),
                "product scalar deficit")
        require(min(probabilities)>=F(3,8*d), "product minimum pair mass")
        product_dimension_cases += 1

print(json.dumps({"status":"PASS", "rational_parameters":len(parameters),
                  "ordered_four_type_tuples":total_tuples,
                  "sign_averages_per_tuple":16,
                  "product_dimension_cases":product_dimension_cases,
                  "section_and_block_formulas":"PASS"},sort_keys=True))
