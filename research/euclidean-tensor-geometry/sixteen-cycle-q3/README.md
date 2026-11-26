# Exact alternating quantum max-flow for the periodic sixteen-cycle in dimension three

**Yongxian Zhang.** AI-assisted proof development and independent internal replay; no external peer review claimed.

Let F16(q) be the largest rank of the odd-even flattening of the one-site translation-invariant periodic trace tensor on C16, when both physical and virtual dimensions are q. In the model of [Gesmundo–Landsberg–Walter, §II](https://arxiv.org/html/1801.09106#S2), over the complex numbers,

    F16(3) = 3^8 - 1 = 6560.

GLW Theorem I.3 explicitly treats half-length d = 2 mod 4, not d = 8. The same rotation-skew argument applies here; the new part is the explicit matching lower bound. The published square-dimension case, and binary estimates, are different dimension regimes. A targeted literature search for this exact case found no duplicate, not an exhaustive priority claim.

## Rotation upper bound (all q = 3 mod 4)

For length-eight words a,b, use M[a,b]=tr(A[b7] A[a7] ... A[b0] A[a0]). Define R to move first letter to last, with Re_b=e_(Rb). Then M commutes with R and M^T = M R: cyclically re-starting the trace one letter later exchanges the roles of the two words, leaving one word rotated. On the minus-one eigenspace of R the flattening is skew for the standard bilinear form. That eigenspace is nondegenerate and orthogonal to the other eigenspaces, since R is orthogonal and the inverse of -1 is itself.

The determinant of a swap of adjacent factors of (C^q)^⊗8 is (-1)^(q^6 binom(q,2)), by exchanging the two distinct letters and freely choosing the other six. An 8-cycle is a product of seven swaps, so det(R) = -1 for q = 3 mod 4. Reciprocal non-real roots-of-unity eigenvalues pair and contribute determinant 1, so the minus-one eigenspace has odd dimension. Consequently F16(q) ≤ q^8−1 for all q = 3 mod 4; in particular F16(3) ≤ 6560.

## Integral witness and exact replay

With physical labels 0,1,2, take slices (matrix rows separated by semicolon):

    A0 = [1,3,7; 17,5,13; 37,19,11]
    A1 = [4,9,8; 18,25,16; 14,20,12]
    A2 = [29,23,30; 22,35,21; 31,36,38]

Their entries are integers. Work modulo 41, where z=3 is a primitive eighth root: 3^4=-1. The eigenspace of R with eigenvalue z^j has an orbit basis: for each cyclic orbit of length m with 8 dividing jm, normalize the coefficient at its least base-3 integer word to 1 and give the r-th rotation coefficient z^(-jr). Evaluating at the representative recovers its coefficient. Thus the entry of the j-block for row representative u and column representative v is Σ_r z^(-jr) M[u,R^r v], summing once over the orbit. Since (Mv)_u is computed this way and M commutes with R, these are the exact block matrices without any rescaling factors. The orbit test gives a complete basis since division by 8 is valid modulo 41 and the primitive root splits R.

The standard bilinear form pairs the eigenvalue z^j space perfectly with the space z^(-j); the equality M^T=M R therefore pairs the ranks for j and -j. The independent block dimensions and ranks found by elementary row elimination are:

    j                       0    1    2    3    4
    dimension             834  810  828  810  831
    rank modulo 41        834  810  828  810  830

The block dimensions can also be derived from tr(R^r)=3^gcd(8,r) by character projection. The total rank modulo 41 is 6560, so a size-6560 minor of the integer flattening is nonzero modulo 41 and remains nonzero over the complex numbers. The upper bound concludes equality.

To replay, compile and run:

    g++ -std=c++17 -O3 check.cpp -o check
    ./check

The program precomputes all length-eight matrix products, obtains each alternating trace by splitting the sixteen interleaved letters into two chunks, and performs modular row elimination. Expected output is run.txt.
