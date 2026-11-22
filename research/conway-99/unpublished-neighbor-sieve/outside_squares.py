"""Find short odd-vector certificates, then check every rejection with integer arithmetic.

Requires python-flint and fpylll. The certificate check alone just uses Python integers.
"""
from collections import Counter
from fpylll import Enumeration, EnumerationError, GSO, IntegerMatrix
from positive_edge import neighborhoods
from three_positive import signature, survivors
from three_positive_supports import parent_pairs, spectral, support_graphs, valid_pairs


def moments(core):
    degree = [14-m.bit_count() for m in core]
    residual = [[12*int(i==j)+2-((r>>j)&1)-(r&s).bit_count()
                 for j,s in enumerate(core)] for i,r in enumerate(core)]
    return degree,residual


def certificate_norm(degree,residual,odd,coefficients):
    assert odd%2==1 and len(coefficients)==len(degree)
    nonzero = [(i,c) for i,c in enumerate(coefficients) if c]
    return (71*odd**2 + 4*odd*sum(c*degree[i] for i,c in nonzero)
            +4*sum(c*d*residual[i][j] for i,c in nonzero for j,d in nonzero))


def short_certificate(core):
    degree,residual = moments(core)
    n = len(core)
    # The small added diagonal makes the search nonsingular even with dependent
    # rows. Every result is retested against the original, unmodified residual.
    gram = IntegerMatrix.from_matrix([[500*c+int(i==j) for j,c in enumerate(row)]
                                      for i,row in enumerate(residual)])
    gs = GSO.Mat(gram,gram=True)
    if not gs.update_gso():
        return None
    signs = [-1]*3+[1]*25
    offsets = [sum(signs[j]*(1 if j==i else gs.get_mu(j,i)) for j in range(i,n))/8
               for i in range(n)]
    for odd in (1,3):
        try:
            points = Enumeration(gs).enumerate(0,n,7975,0,
                                                target=tuple(-odd*x for x in offsets))
        except EnumerationError:
            continue
        for _,point in points:
            coefficients = [int(round(t)) for t in point]
            if certificate_norm(degree,residual,odd,coefficients)<71:
                return odd,coefficients
    return None


def main():
    totals = Counter()
    for g,size,neg in survivors():
        tested = eliminated = 0
        for core in support_graphs(g,neg):
            if not valid_pairs(core) or not spectral(core):
                continue
            if not all(parent_pairs(core,p) for p in range(3)):
                continue
            if g[0] and not all(next(neighborhoods(core,size,neg,p),None) is not None
                                for p in (0,1)):
                continue
            tested += 1
            proof = short_certificate(core)
            if proof is not None:
                degree,residual = moments(core)
                assert certificate_norm(degree,residual,*proof)<71
                eliminated += 1
        totals['tested'] += tested
        totals['excluded'] += eliminated
        print(signature(g,size,neg),tested,eliminated,tested-eliminated,flush=True)
    print('Totals',totals,'remaining',totals['tested']-totals['excluded'])


if __name__=='__main__':
    main()
