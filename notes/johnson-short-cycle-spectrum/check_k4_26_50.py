#!/usr/bin/env python3
"""Exact, optimizer-free verification of fixed S_n four-subset certificates.

Checks n=26,...,50 using only Python standard-library integers and fractions.
The input is a literal JSON list of six support cycle-statistic vectors per n.
All primal and dual rational weights are independently reconstructed from
the fixed integer moment matrix; no floating-point LP data is used.
"""
import json
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path

from transfer import moment, short_types


def rational_solve(A, b):
    d = len(b)
    assert len(A) == d and all(len(row) == d for row in A)
    matrix = [[Q(z) for z in A[i]] + [Q(b[i])] for i in range(d)]
    for j in range(d):
        p = next((i for i in range(j, d) if matrix[i][j]), None)
        assert p is not None, 'support matrix is singular'
        matrix[j], matrix[p] = matrix[p], matrix[j]
        pivot = matrix[j][j]
        matrix[j] = [z/pivot for z in matrix[j]]
        for i in range(d):
            if i != j:
                factor = matrix[i][j]
                matrix[i] = [matrix[i][h]-factor*matrix[j][h]
                             for h in range(d+1)]
    answer = [matrix[i][-1] for i in range(d)]
    assert all(sum(Q(a)*x for a,x in zip(A[i], answer)) == b[i]
               for i in range(d))
    return answer


def class_size(n, short_counts):
    residual = n-sum((j+1)*v for j, v in enumerate(short_counts))
    assert residual == 0 or residual >= 5
    d = residual if residual else 1
    for j,v in enumerate(short_counts,1):
        d *= j**v * factorial(v)
    size,rem=divmod(factorial(n),d)
    assert rem==0 and size>0
    return size


def verify_record(r):
    n = r['n']
    assert isinstance(n,int) and 26 <= n <= 50
    assert set(r) == {'n', 'C', 'P', 'Q'}
    positive = [(n,0,0,0)] + [tuple(a) for a in r['P']]
    negative = [tuple(a) for a in r['Q']]
    assert len(positive) == len(negative) == 3
    support = positive + negative
    assert len(set(support)) == 6
    assert all(len(a) == 4 and all(isinstance(v,int) and v>=0 for v in a)
               for a in support)
    assert all((n-sum((j+1)*v for j,v in enumerate(a))) in (0,)
               or (n-sum((j+1)*v for j,v in enumerate(a))) >= 5
               for a in support)

    f = [moment(n,4,a) for a in support]
    B = [[1,0,*row[:4]] for row in f[:3]] + [
        [0,1,*(-v for v in row[:4])] for row in f[3:]]
    primal = rational_solve(list(map(list,zip(*B))), [1,1,0,0,0,0])
    dual = rational_solve(B,[1,0,0,0,0,0])
    assert all(v>0 for v in primal)
    assert sum(primal[:3]) == sum(primal[3:]) == 1
    for j in range(5):
        assert sum(primal[i]*f[i][j] for i in range(3)) == \
               sum(primal[i+3]*f[i+3][j] for i in range(3))

    expected = Q(r['C'])
    assert 0 < expected < 1
    upper,lower = dual[0],-dual[1]
    assert expected == upper-lower == primal[0]

    def dual_at(a):
        stats=moment(n,4,a)
        return Q(int(a==(n,0,0,0)))-sum(dual[j+2]*stats[j]
                                       for j in range(4))
    assert all(dual_at(a)==upper for a in positive)
    assert all(dual_at(a)==lower for a in negative)

    # Exact exhaustive dual bound: Lemma B makes this a complete partition
    # of all S_n conjugacy classes by their sufficient short-cycle data.
    count=0
    for a in short_types(n,4):
        h=dual_at(a)
        assert lower<=h<=upper,(n,a,h,lower,upper)
        count+=1

    # Convert the rational central class weights into an actual strictly
    # positive marginal-preserving perturbation about uniform measure.
    sizes=[class_size(n,a) for a in support]
    delta=min(Q(sizes[i],2*factorial(n)*primal[i])
              for i in range(3,6))
    assert delta>0
    for i in range(3,6):
        assert Q(1,factorial(n))-delta*primal[i]/sizes[i]>0
    assert delta*(primal[0]-0) == delta*expected
    return count,expected


def main():
    path=Path(__file__).resolve().parent / 'certificates' / 'k4_n26_50.json'
    data=json.loads(path.read_text(encoding='utf-8'))
    assert data['scope']=='S_n on 4-subsets, n=26..50'
    assert len(data['records']) == 25
    assert [r['n'] for r in data['records']] == list(range(26,51))
    total=0
    for r in data['records']:
        count,c=verify_record(r)
        total+=count
        print('PASS n=%d compressed types=%d C=%s'%(r['n'],count,c),
              flush=True)
    print('ALL 25 EXACT RANK-FIVE CERTIFICATES n=26..50 PASSED; types=%d'%total)


if not __debug__:
    raise RuntimeError('Run without -O: optimized Python disables assert checks')

if __name__=='__main__':
    main()
