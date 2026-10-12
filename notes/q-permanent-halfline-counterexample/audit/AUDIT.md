# Independent audit of a counterexample to da Fonseca's half line conjecture

Audit date: 8 October 2026 UTC. Exact-arithmetic and mathematical verification report.

## Verdict

**PASS.** The proposed rational matrix is strictly positive definite and its q-permanent decreases between 49 and 50. This refutes the positive-definite half-line conjecture attributed to da Fonseca in the verified primary 2018 manuscript and the 2020 published paper, and matches the 2010 Conjecture 1 as reproduced by its full-text mirror. The stronger theorem for every fixed evaluation point t > 1 and the minimal-order claim also pass independent mathematical review.

This audit does not claim a solution to Bapat's original [-1,1] conjecture, formal proof-assistant verification, peer review, or worldwide novelty. No prior disproof of the exact positive-definite half-line statement was found in the searches below. That is a bounded negative search result.

## 1 Source identity and scope

The relevant original publication is C. M. da Fonseca, *The mu-permanent of a tridiagonal matrix, orthogonal polynomials, and chain sequences*, Linear Algebra and its Applications 432 (2010), 1258–1266, DOI [10.1016/j.laa.2009.10.036](https://doi.org/10.1016/j.laa.2009.10.036). The [publisher record](https://www.sciencedirect.com/science/article/pii/S0024379509005503) verifies the title, bibliographic details, definition by permutation inversion number, and the distinction between the proposed general conjecture and the proved Jacobi case. Full publisher text was not retrievable in this audit.

The [full-text mirror of the published article](https://www.academia.edu/103682178/The_%CE%BC_permanent_of_a_tridiagonal_matrix_orthogonal_polynomials_and_chain_sequences), p.1259, defines A > 0 as **real symmetric positive definite**, then states Conjecture 1 in Section 2 before specializing to tridiagonal matrices. Its OCR damages the endpoint inequality glyph; it is consistent with epsilon <= -1. That exact glyph was not independently established from an original-page image. The present counterexample refutes both epsilon <= -1 and epsilon < -1, so this uncertainty cannot change the verdict.

The author's [primary nine-page arXiv manuscript, 1804.02231v1](https://arxiv.org/pdf/1804.02231), p.1, defines the inversion count as the number of pairs i < j with sigma(i) > sigma(j). Section 4, Conjecture 2, p.6, unambiguously uses epsilon < -1 and monotonicity on (epsilon,+infinity), citing the 2010 article as reference [7]. This is separate from its Conjecture 1 on [-1,1]. The manuscript notes that a shortened letter would appear in the journal; its nine-page contents must not be attributed blindly to that two-page version.

Lon Mitchell's [published 2020 paper](https://files.ele-math.com/articles/oam-14-56.pdf), *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14, 915–919, DOI 10.7153/oam-2020-14-56, confirms in the Remark across pp.917–918 that da Fonseca's statement concerns **every non-diagonal positive-definite matrix**, with an endpoint r < -1. Mitchell gives a failure for a singular positive-semidefinite analogue but explicitly says those examples do not appear to produce positive-definite counterexamples. Accordingly, that remark is not an existing disproof of the statement audited here.

The 2010/2018 displayed conjectures omit a non-diagonal qualifier locally, although the surrounding context and Mitchell's restatement include it. Diagonal matrices have constant q-permanents, so the meaningful intended statement excludes them. The candidate is non-diagonal, so the omission is immaterial here.

## 2 Exact matrix certificate

The tested matrix is

A = [[1, -99/100, 0, 1/500],
     [-99/100, 1, 0, 1/8],
     [0, 0, 1, 0],
     [1/500, 1/8, 0, 1]].

It is real symmetric and non-diagonal. Independent Leibniz determinant calculations in rational arithmetic give its leading principal minors as

1, 199/10000, 199/10000, 59/15625.

All are positive, so Sylvester's criterion establishes strict positive definiteness. For redundancy all 15 nonempty principal minors were computed and are positive. The nontrivial principal block on indices {1,2,4} has determinant 59/15625.

All 24 permutations were independently enumerated, without importing the main verifier or using numerical search code. There are six nonzero terms:

| One line permutation | Inversions | Product of entries |
|---|---:|---:|
| 1234 | 0 | 1 |
| 1432 | 3 | 1/64 |
| 2134 | 1 | 9801/10000 |
| 2431 | 4 | -99/400000 |
| 4132 | 4 | -99/400000 |
| 4231 | 5 | 1/250000 |

Therefore

P_q(A) = 1 + (9801/10000)q + (1/64)q^3 - (99/200000)q^4 + (1/250000)q^5.

Exact evaluations are

P_49(A) = 81807513/500000,
P_50(A) = 7969/50,
P_49(A) - P_50(A) = 2117513/500000 > 0.

Since 49 < 50 and both points belong to every (epsilon,infinity) with epsilon <= -1, no such interval supports strict increase for this A. This finite difference is sufficient, without an appeal to numerical derivatives.

As an independent certificate of local decrease,

P'_50(A) = -10831/2500 < 0.

The polynomial derivative is continuous, so it is negative throughout an open neighborhood of 50.

Endpoint consistency checks also pass: P_-1(A) = det(A) = 59/15625 and P_1(A) = per(A) = 997617/500000.

## 3 Why this does not touch Bapat's interval

For -1 <= q <= 1,

P'_q(A) = 9801/10000 + (3/64)q^2 - (99/50000)q^3 + (1/50000)q^4
         >= 9801/10000 - 99/50000
         = 24453/25000 > 0.

Thus this particular example actually satisfies strict monotonicity on all of [-1,1]. The disproof concerns the extension to an unbounded right half-line.

The position of the isolated third coordinate is essential to the displayed q-polynomial. Positive definiteness is invariant under simultaneous row/column permutation, but the inversion-weighted permanent generally is not. One may permute indices to check positive definiteness; one may not silently replace the polynomial by that of a contiguous 3-by-3 block.

## 4 Minimal dimension

The proof that every non-diagonal Hermitian positive-definite matrix of order at most three is strictly increasing on the entire real line is correct, including its exceptional derivative-zero case.

After positive diagonal normalization, order two gives 1 + |a_12|^2 q. For order three put a = a_12, b = a_13, c = a_23, and r = Re(a c conjugate(b)). Then

P'_q = |a|^2 + |c|^2 + 4 r q + 3 |b|^2 q^2.

When b is nonzero, completing the square leaves the remainder

|a|^2 + |c|^2 - 4r^2/(3|b|^2)
>= |a|^2 + |c|^2 - (4/3)|a|^2|c|^2
>= (|a|^2 + |c|^2)/3,

using |a|,|c| <= 1 and 2xy <= x+y for x,y in [0,1]. This is positive unless a=c=0. In that exception P_q = 1+|b|^2 q^3 remains strictly increasing although its derivative vanishes at zero. If b=0, non-diagonality gives a positive constant derivative. Consequently order four is minimal in the intended non-diagonal class. The reasoning even applies to positive-semidefinite Hermitian matrices with positive diagonal. No novelty claim is made for this low-order fact.

## 5 Every right endpoint enlargement fails in some dimension

The universal construction was audited symbolically. With n >= 4, m = 2n-5, and only the off-diagonal pairs (1,2), (1,n), (2,n) nonzero, assigned a,b,c respectively, direct permutation analysis gives

P_q = 1+a^2q+c^2q^m+2abcq^(m+1)+b^2q^(m+2).

The exponents 1,m,m+1,m+2 are correct. Full independent permutation enumeration also checked this identity for n=4,...,8 with rational test entries.

Fix t > 1. Choose an odd m >= 3 with t^(m-1) > 32(m+1)^2(m+2), and set

delta = 1/[2(m+1)^2],
a = -sqrt(1-delta),
c = sqrt(delta/8),
b = -a(m+1)c/[(m+2)t].

The choice is possible because exponential growth dominates polynomial growth along the odd integers. Here 0 < b < c and |a| < 1. The determinant of the 3-by-3 nontrivial block equals

delta - (b^2+c^2+2|a|bc) > delta - 4c^2 = delta/2 > 0.

The other two Sylvester minors are 1 and delta. Thus the whole matrix is strictly positive definite.

At the fixed t, substitution x=bt/c=-a(m+1)/(m+2) into the derivative yields

m + 2(m+1)a x + (m+2)x^2 = -1/[2(m+2)],

and hence

P'_t = 1-delta - t^(m-1)/[32(m+1)^2(m+2)] < -delta < 0.

There is no illegitimate differentiation of t-dependent entries: t is fixed first, the matrix is then fixed, and q is the differentiation variable.

Positive definiteness and strict negativity of this derivative are open conditions on the finite-dimensional real symmetric matrices with diagonal fixed to 1. Rational off-diagonal vectors avoiding every zero-coordinate hyperplane are dense in that space. A sufficiently small such perturbation therefore provides a rational, fully nonzero off-diagonal example at the same t. This argument is valid even for irrational t.

Taking t=1+epsilon/2 and using derivative continuity gives failure of monotonicity on [1,1+epsilon], for every epsilon>0, in a possibly epsilon-dependent dimension. This does not assert failure at t=1 and does not settle the original interval.

## 6 Optional explicit dense variant

To remove any concern over the sparse example's reducibility, replace a_13,a_23,a_34 and their symmetric partners by 1/10000, keeping every other entry unchanged. Independent exact computation gives leading principal minors

1, 199/10000, 99499801/5000000000, 377596520689/100000000000000,

and P'_50 = -2707509509/625000000 < 0. This fully nonzero real rational correlation matrix is another strict-positive-definite counterexample. Irreducibility is not required by the verified conjecture, so the simpler sparse certificate suffices.

## 7 Existing corrections and novelty limits

The primary [de Sa 2015 letter manuscript](https://www.mat.uc.pt/preprints/ps/p1519.pdf) was read in full. It attacks formulas and intermediate assertions in da Fonseca's **2005** paper, using counterexamples to purported algebraic identities. It neither states nor disproves the 2010 positive-definite half-line conjecture. Its eventual [journal record](https://www.tandfonline.com/doi/full/10.1080/03081087.2018.1466861) is *Letter to the editor*, Linear and Multilinear Algebra 67 (2019), 1711–1712. The full final typeset text was not obtained in this audit, so no identity of its contents with the preprint is assumed.

Two additional primary manuscripts were screened: [de Sa 2017, Noncrossing partitions, noncrossing graphs and q-permanental formulas](https://www.mat.uc.pt/preprints/ps/p1722.pdf), especially pp.12–14; and [de Sa 2018, q-Permanent expansions](https://www.mat.uc.pt/preprints/ps/p1809.pdf), especially p.21. The former corrects the 2005 derivative identity and proves special cases on [-1,1]; the latter characterizes when cycle-expansion formulas hold. No half-line positive-definite disproof was found there.

Searches through 8 October 2026 used variants of the original title, DOI, da Fonseca plus q-/mu-permanent, monotonicity, counterexample, and date-restricted terminology. A recent [2026 q-permanent paper](https://arxiv.org/html/2605.24349v1) concerned Pólya conversion and preservers; its text search did not reveal a monotonicity result. Secondary status pages were not treated as proof of openness. Search incompleteness, unindexed work, and inaccessible final texts remain genuine limitations. Before any priority claim, broader bibliographic checking or expert review is appropriate.

## 8 Reproducibility

Run with Python 3, no third-party packages:

- python verify_exact.py
- python verify_family.py

The first writes exact_results.json containing every permutation and every principal minor. The second writes family_results.json containing spaced-triangle enumeration checks, three exact rational-invariant checks of the radical construction, and the optional dense matrix certificate. The core 24-permutation audit script was independently implemented without importing the main verifier. The family-check script uses different rational test entries and also imports no code from the main verifier. Finite computational checks supplement, rather than replace, the general symbolic argument.
