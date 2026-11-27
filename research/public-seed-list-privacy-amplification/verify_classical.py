#!/usr/bin/env python3
"""Exact finite probability checks; no entropy estimate uses floating point."""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product


def law(rows):
    p = defaultdict(F)
    for outcome, mass in rows:
        p[outcome] += mass
    return p


def tv(p, q):
    assert sum(p.values()) == sum(q.values()) == 1
    return sum(abs(p[z] - q[z]) for z in p.keys() | q.keys()) / 2


def erase(rows, projection):
    return [(projection(z), p) for z, p in rows]


def error(rows, repair, m):
    # First coordinate is the key, the rest is the true side.
    real = law(erase(rows, repair))
    ideal = law(((v, *side), p / m)
                for (_, *side), p in real.items() for v in range(m))
    return tv(real, ideal)


def witness_formula():
    e = F(1, 16)
    for k, L, ell, b in ((32, 2, 17, 34), (8, 1 << 16, 10, 10)):
        assert ell <= k + (L.bit_length() - 1) - 2*4 - 3
        assert 1 - F(2**k, 2**b) == F(3, 4) > 4*e
    # A fixed or biased private seed is not a uniform private seed.
    raw = [(0, F(7, 9)), (1, F(2, 9))]
    assert error([((x,), p) for x, p in raw], lambda z: z, 2) == F(5, 18)
    # An independent uniform private bit can increase the support by two.
    augmented = [((2*x+s,), p/2) for x, p in raw for s in range(2)]
    assert len(law(augmented)) == 4 and max(p for _, p in augmented) == F(7, 18)
    print("public-seed arithmetic: both paper-condition witnesses yield 3/4 > 1/4")
    print("private-resource control: fixed seed is not a hidden uniform seed; independent bit doubles support")


def all_small():
    funcs = list(product(range(2), repeat=4))
    seeds = list(product(range(len(funcs)), repeat=2))
    for x, y in combinations(range(4), 2):
        assert sum(tuple(funcs[s][x] for s in f) == tuple(funcs[s][y] for s in f)
                   for f in seeds) * 4 == len(seeds)
    cases = 0
    for subset in chain_subsets():
        q = F(2, 7)
        # A deterministic readable side flag; support statements are checked per flag.
        rows = [((funcs[f[0]][x], funcs[f[1]][x], f, x//2),
                 F(1, len(seeds)*len(subset))) for f in seeds for x in subset]
        jnt = error(rows, lambda z: (2*z[0]+z[1], z[2], z[3]), 4)
        nmax = max(sum(x//2 == side for x in subset) for side in (0,1))
        assert jnt >= 1-F(nmax, 4)
        no = tuple(error(rows, lambda z: (z[j],z[2],z[3]), 2) for j in range(2))
        off = tuple(error(rows, lambda z: (z[j],z[2],z[3],z[1-j]),2) for j in range(2))
        pick = [((z[j],j,z[2],z[3],z[1-j]), p*qj)
                for z,p in rows for j,qj in enumerate((q,1-q))]
        assert error(pick, lambda z:z[:-1], 2) == q*no[0]+(1-q)*no[1]
        assert error(pick, lambda z:z, 2) == q*off[0]+(1-q)*off[1]
        hidden = [((2*funcs[f[0]][x]+funcs[f[1]][x], x, x//2), F(1,len(seeds)*len(subset)))
                  for f in seeds for x in subset]
        assert error(hidden,lambda z:z,4) == 0
        cases += 1
    # Equal fair keys illustrate why revealing the other output matters.
    duplicate = [((x,x),F(1,2)) for x in range(2)]
    assert error(duplicate,lambda z:(z[0],),2) == 0
    assert error(duplicate,lambda z:z,2) == F(1,2)
    assert error(duplicate,lambda z:(2*z[0]+z[1],),4) == F(1,2)
    print(f"small deterministic maps: {cases} readable-flat sources x {len(seeds)} public pairs; collision, hidden-seed, direct-sum checks PASS")
    print("correlated-key control: selected-only 0, off-list 1/2, joint 1/2")


def marginal_control():
    # Key lengths 2 and 1; move mass across complementary key bins.
    t = F(1,32)
    rows = [((x,y),F(1,8) + (t if y==0 else -t) * (x==0))
            for x,y in product(range(4),range(2))]
    joint = error(rows,lambda z:(2*z[0]+z[1],),8)
    selected = error(rows,lambda z:z,4)
    off_margin = error(rows,lambda z:(z[1],),2)
    assert joint == off_margin == t
    assert selected == F(3,2)*joint > joint
    assert selected <= joint+off_margin
    print("actual-marginal control: joint t, selected with other key 3t/2; two-term bound PASS")


def chain_subsets():
    for k in range(1,5):
        yield from combinations(range(4),k)


def equality():
    models = ((2,2),(2,4,8),(8,2))
    n = 0
    for sizes in models:
        lengths = [m.bit_length()-1 for m in sizes]
        b = sum(lengths)
        for q in (F(0),F(1,97),F(2,7),F(7,9),F(1)):
            p = [((1,*key),q/2**b) for key in product(*(range(m) for m in sizes))]
            p += [((0,*([0]*len(sizes))),1-q)]
            errs = [error(p,lambda z,j=j: (z[j+1],z[0],*z[1:j+1],*z[j+2:]),m)
                    for j,m in enumerate(sizes)]
            assert errs == [(1-q)*(1-F(1,m)) for m in sizes]
            assert sum(l*(1-e/(1-F(1,m))) for l,e,m in zip(lengths,errs,sizes)) == q*b
            n += 1
    # Distinct activation probabilities attain an arbitrary vector
    # on the entropy boundary, not just equal normalized errors.
    q = (F(1,7),F(3,5),F(4,9))
    sizes = (2,4,8)
    rows = []
    for flag in product(range(2),repeat=3):
        mass = F(1)
        for active,v,m in zip(flag,q,sizes):
            mass *= v/m if active else 1-v
        for key in product(*(range(m) if active else (0,) for active,m in zip(flag,sizes))):
            rows.append(((flag,*key),mass))
    errs = [error(rows,lambda z,j=j:(z[j+1],z[0],*z[1:j+1],*z[j+2:]),m)
            for j,m in enumerate(sizes)]
    assert errs == [(1-v)*(1-F(1,m)) for v,m in zip(q,sizes)]
    assert sum((j+1)*(1-d/(1-F(1,m))) for j,(d,m) in enumerate(zip(errs,sizes))) == sum((j+1)*v for j,v in enumerate(q))
    # Flat 2p-bit source; independently public permutation balances error
    # across all three positions without changing any conditional guarantee.
    for p in range(4):
        perm = list(permutations(range(3)))
        pz = [(tuple((parts+(0,)*(3-p))[j] for j in s), s)
              for s in perm for parts in product(range(4),repeat=p)]
        rows = [((k,s),F(1,len(pz))) for k,s in pz]
        errs = [error(rows,lambda z,j=j: (z[0][j],z[1],*z[0][:j],*z[0][j+1:]),4)
                for j in range(3)]
        assert errs == [F(3-p,3)*F(3,4)]*3
        assert sum(2*(1-d/F(3,4)) for d in errs) == 2*p
    print(f"sharpness: {n} flagged unequal/equal models, 1 distinct-error vector and 4 flat public-permutation models PASS")


if __name__ == "__main__":
    witness_formula()
    all_small()
    marginal_control()
    equality()
