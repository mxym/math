"""Finite tests of exploration infrastructure, not of Ryser's conjecture."""
import itertools
import random
from search import cover_at_most
from verify_witness import check_edges


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def expect_rejection(edges):
    try:
        check_edges(edges)
    except ValueError:
        return
    raise RuntimeError('invalid certificate accepted')


def main():
    rng = random.Random(20261007)
    checks = 0
    for n in range(1, 9):
        for _ in range(8):
            edges = sorted(set(tuple(rng.randrange(2) for _ in range(6))
                               for _ in range(n)))
            vertices = sorted({6*c+v for e in edges for c, v in enumerate(e)})
            for k in range(1, 6):
                found, _ = cover_at_most(edges, k)
                brute = any(all(any(6*c+v in subset for c, v in enumerate(e))
                                for e in edges)
                            for size in range(k+1)
                            for subset in itertools.combinations(vertices, size))
                require((found is not None) == brute, 'oracle/brute discrepancy')
                if found is not None:
                    require(len(set(found)) <= k and
                            all(any(6*c+v in found for c, v in enumerate(e))
                                for e in edges), 'invalid returned cover')
                checks += 1
                wider, _ = cover_at_most(edges, k, width=7)
                require((wider is not None)==brute,'wider-universe oracle discrepancy')
    q = 5
    plane = [tuple((y-a*x) % q for a in range(q)) + (x,)
             for x, y in itertools.product(range(q), repeat=2)]
    require(all(any(a == b for a, b in zip(e, f))
                for e, f in itertools.combinations(plane, 2)), 'affine intersection')
    require(cover_at_most(plane, 4)[0] is None and
            cover_at_most(plane, 5)[0] is not None, 'affine cover number five')
    require(check_edges(plane, forbidden_size=4)==58905,
            'independent complete four-subset enumeration')
    expect_rejection(plane)
    expect_rejection([])
    expect_rejection([[0]*6, [1]*6])
    expect_rejection([[0]*6, [0]*6])
    expect_rejection([[False, 0, 0, 0, 0, 0]])
    expect_rejection([[6, 0, 0, 0, 0, 0]])
    expect_rejection([[0]*5])
    print(f'{checks} exact oracle/brute comparisons PASS')
    print('Affine-plane complete four-subset enumeration and rejection controls PASS')


if __name__ == '__main__':
    main()
