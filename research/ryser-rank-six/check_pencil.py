"""Complete exact enumeration of a restricted F_5 pencil-split obstruction."""
import itertools
from collections import Counter


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def intercept(point, direction):
    x, y = point
    return (y-direction*x) % 5 if direction < 5 else x


def main():
    pairs = list(itertools.combinations(range(1, 5), 2))
    triples = list(itertools.combinations(range(1, 5), 3))
    index = {pair: i for i, pair in enumerate(pairs)}
    triangle_masks = [sum(1 << index[p] for p in itertools.combinations(t, 2))
                      for t in triples]
    masks, geometric = {}, {}
    for g in range(6):
        for d in range(6):
            if g == d:
                continue
            coefficient = (g-d) % 5 if g < 5 and d < 5 else 1
            inverse = pow(coefficient, -1, 5)
            masks[g, d] = [1 << index[tuple(sorted((a*inverse % 5, b*inverse % 5)))]
                           for a, b in pairs]
            # Independent forward-coordinate reconstruction: no inverse or masks.
            points = {t: (t, g*t % 5) if g < 5 else (0, t)
                      for t in range(1, 5)}
            geometric[g, d] = [{(s, t) for s, t in pairs
                                if intercept(points[s], d) in merged and
                                intercept(points[t], d) in merged}
                               for merged in pairs]
    histogram = Counter()
    for choices in itertools.product(range(6), repeat=6):
        good = 0
        for g in range(6):
            mask, restored = 0, set()
            for d in range(6):
                if g != d:
                    mask |= masks[g, d][choices[d]]
                    restored.update(geometric[g, d][choices[d]])
            fast = any(mask & t == t for t in triangle_masks)
            direct = any(all(pair in restored for pair in itertools.combinations(t, 2))
                         for t in triples)
            require(fast == direct, 'coordinate/mask reconstruction discrepancy')
            good += direct
        histogram[good] += 1
    expected = {0: 5248, 1: 480, 2: 6720, 3: 8720, 4: 16320, 5: 9168}
    require(dict(histogram) == expected, 'full histogram mismatch')
    require(sum(histogram.values()) == 46656 and histogram[6] == 0,
            'pencil exclusion failed')
    print('All 46656 merged-pair choices checked by inverse masks and forward coordinates')
    print('Feasible-ray histogram:', dict(sorted((k,v) for k,v in histogram.items() if v)))
    print('No choice admits retained triangles on all six rays')


if __name__ == '__main__':
    main()
