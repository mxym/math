"""Numerical diagnostics for the analytic facet-order proof; no dependencies."""
import itertools
import math

S2, SQRT_TAU = math.sqrt(2), math.sqrt(math.tau)


def phi(x):
    return math.exp(-x*x/2) / SQRT_TAU


def Phi(x):
    return math.erfc(-x / S2) / 2


def I(b, i, l):
    # Uniform translation of all scores only translates the t-integral.
    others = [c for m, c in enumerate(b) if m not in (i, l)]
    lo, hi = min(b)-12, max(b)+12
    n = 4096
    h = (hi-lo)/n
    def integrand(x):
        return phi(x-b[i])*phi(x-b[l])*math.prod(Phi(x-c) for c in others)
    return h / 3 * math.fsum(
        (1 if j in (0, n) else 4 if j % 2 else 2)*integrand(lo+j*h)
        for j in range(n+1)
    )


def require(cond, message):
    if not cond:
        raise RuntimeError(message)


def main():
    tests = 0
    for b in [(-1.0, .2, .8), (1., 0., 0.), (0., 0., 0.),
              (1., -.1, .25, -.65), (.4, .4, .4, -1.2),
              (-2., .25, 1.5, -.125, .375)]:
        k = len(b)
        pairs = list(itertools.combinations(range(k), 2))
        vals = {tuple(sorted((i,l))): I(b,i,l) for i,l in pairs}
        for i,j,l in itertools.permutations(range(k), 3):
            a, c = vals[tuple(sorted((i,l)))], vals[tuple(sorted((j,l)))]
            if b[i] > b[j]:
                require(a > c + 1e-8, 'ordered distinct offsets')
            if b[i] == b[j]:
                require(abs(a-c) < 1e-12, 'equal offset control')
            if k == 3:
                exact = math.exp(-(b[i]-b[l])**2/4)/(2*math.sqrt(math.pi))*Phi((b[i]+b[l]-2*b[j])/math.sqrt(6))
                require(math.isclose(exact, a, rel_tol=1e-11, abs_tol=1e-13), 'closed k=3 formula')
            tests += 1
        shift = [x+7.125 for x in b]
        require(abs(I(shift,0,1)-vals[(0,1)]) < 1e-12, 'common offset')
        require(abs(I(tuple(reversed(b)),k-1,k-2)-vals[(0,1)]) < 1e-12, 'relabeling')
    print(f'PASS: {tests} ordered triple cases; closed-form and symmetry controls. Not a proof.')


if __name__ == '__main__':
    main()
