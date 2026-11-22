"""Exact finite arithmetic for the unpublished neighbor sieve."""
from fractions import Fraction as Q
from itertools import product
from math import comb


def solve(A, b):
    a = [[Q(t) for t in row] + [Q(r)] for row, r in zip(A, b)]
    for j in range(len(a)):
        i = next(i for i in range(j, len(a)) if a[i][j])
        a[i], a[j] = a[j], a[i]
        v = a[j][j]
        a[j] = [x / v for x in a[j]]
        for i in range(len(a)):
            if i != j:
                a[i] = [x - a[i][j] * y for x, y in zip(a[i], a[j])]
    return [row[-1] for row in a]


def multiply(a, b):
    return [sum(a[i] * b[n-i] for i in range(n+1)) for n in range(5)]


def main():
    E4 = [1] + [240 * sum(d**3 for d in range(1,n+1) if n % d == 0) for n in range(1,5)]
    delta = [0,1,0,0,0]
    for j in range(1,5):
        factor = [(-1)**(i//j)*comb(24,i//j) if i%j == 0 else 0 for i in range(5)]
        delta = multiply(delta,factor)
    theta = [x-720*y for x,y in zip(multiply(E4,multiply(E4,E4)),delta)]
    assert theta == [1,0,196560,16773120,398034000]
    assert theta[4] == 48 * (2**24-1-theta[2]//2-theta[3]//2)
    assert Q(11*20*79,99) > 120
    G = [[4,1,0,1],[1,4,-1,0],[0,-1,4,1],[1,0,1,Q(8,9)]]
    for k, nums, den in [(5,[50,86,122,230],63),(9,[10,22,26,46],7)]:
        found = set()
        for s in product((-1,1), repeat=3):
            w = [*s,Q(k,9)]
            found.add(sum(x*y for x,y in zip(w,solve(G,w))))
        required = 12 - Q(99,7) * (1-Q(k,9)**2)
        assert found == {Q(t,den) for t in nums}
        assert required not in found
    print("Verified both coset counts and all sixteen projection cases.")


if __name__ == "__main__":
    main()
