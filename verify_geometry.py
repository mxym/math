"""Solve the lift from original subspace point sets, without the trace criterion or Gram lemma."""
from itertools import combinations


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def test(degree, modulus):
    size = 1 << degree
    dim = 2 * degree + 1

    # Polynomial convolution, then polynomial long division. The trace is
    # the trace of the matrix of multiplication, not a Frobenius power sum.
    def product(a, b):
        bits = 0
        for i in range(degree):
            for j in range(degree):
                if ((a >> i) & (b >> j) & 1):
                    bits ^= 1 << (i + j)
        while bits.bit_length() > degree:
            bits ^= modulus << (bits.bit_length() - 1 - degree)
        return bits

    times = [[product(a, b) for b in range(size)] for a in range(size)]
    for row in times[1:]:
        require(len(set(row)) == size, "field law")
    tr = [sum((times[a][1 << j] >> j) & 1 for j in range(degree)) & 1
          for a in range(size)]
    spaces = [{times[b][times[x][x]] ^ (x << degree) ^
               (tr[times[b][x]] << (2*degree)) for x in range(size)}
              for b in range(size)]
    spaces.append(set(range(size)))  # U_infinity
    require(all(len(s) == size and 0 in s for s in spaces), "invalid input space")

    def set_rank(eqs):
        basis = {}
        for raw in eqs:
            row = set(raw)
            while row:
                lead = min(row)
                if lead not in basis:
                    basis[lead] = row
                    break
                row ^= basis[lead]
        return len(basis)

    eqs = []
    for i, j in combinations(range(len(spaces)), 2):
        # Original unrestricted lift variables: one element of the WHOLE V
        # for each space; equality in the outer coset is detected by the
        # unique GF(2)-linear functional annihilating the pairwise sum.
        s = {x ^ y for x in spaces[i] for y in spaces[j]}
        require(spaces[i] & spaces[j] == {0} and len(s) == 1 << (dim-1),
                "pair does not span a hyperplane")
        nz = [k for k in range(dim) if (1 << k) not in s]
        normal = sum(1 << k for k in nz)
        require(normal and all((v & normal).bit_count() % 2 == 0 for v in s),
                "incorrect hyperplane normal")
        eqs.append({index * dim + k for index in (i, j) for k in nz})
    r = set_rank(eqs)
    ra = set_rank(row | {len(spaces) * dim} for row in eqs)
    require((r == ra) == (degree <= 3), "unexpected decision from geometry")
    print(f"n={degree}, original subspaces={len(spaces)}, pair hyperplanes={len(eqs)}, "
          f"unnormalized lift ranks={r}/{ra}")

    if degree == 3:
        # Construct actual point sets in the larger W, and check all pair
        # intersections. The inverse map is represented in OUR field basis.
        inv = [0] + [times[a].index(1) for a in range(1, size)]
        shifts = [v | (1 << (2*degree)) for v in inv] + [0]
        w = [u | {v ^ shift ^ (1 << dim) for v in u}
             for u, shift in zip(spaces, shifts)]
        require(all(len(z) == 2*size and
                    all((x ^ y) in z for x in z for y in z) for z in w),
                "a lift is not a subspace")
        require(all({v for v in z if v < (1 << dim)} == u
                    for z, u in zip(w, spaces)), "wrong hyperplane restriction")
        require(all(x & y == {0} for x, y in combinations(w, 2)),
                "lifted pair intersects")
        print(f"n=3 direct witness: {len(w)} disjoint four-spaces with the required sections")


if __name__ == "__main__":
    for n, mod in [(2, 0b111), (3, 0b1101), (4, 0b11001), (5, 0b101001)]:
        test(n, mod)
