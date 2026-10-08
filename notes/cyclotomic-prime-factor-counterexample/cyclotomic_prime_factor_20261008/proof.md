# A counterexample to the prime-order-factor conjecture for unimodal CGFs

## Exact scope

Billey and Swanson, *Cyclotomic Generating Functions*, Electronic Journal of Combinatorics 31(4) (2024), P4.4, DOI https://doi.org/10.37236/12687, Conjecture 48 (printed page 32) predicts that every nonconstant unimodal basic cyclotomic generating function has a prime-order cyclotomic factor.

The latest arXiv record checked on 2026-10-08 is https://arxiv.org/abs/2305.07620v3 (2024-09-13, described as the final version). Definitions 1, 3, and 45 and Conjecture 48 are available at https://arxiv.org/html/2305.07620v3. The journal PDF is https://www.combinatorics.org/ojs/index.php/eljc/article/download/v31i4p4/pdf/.

The conjecture quantifies over all elements of the unimodal basic-CGF monoid other than 1. It does not impose irreducibility, squarefreeness, primitivity, or a restriction on powers. The predicted factor is Phi_p with p prime, not Phi_(p^a) with arbitrary a. Basic CGFs have no additional constant multiplier or monomial factor; the example below is monic with constant term 1.

## Theorem

Let Phi_n(q) be the nth cyclotomic polynomial. Then

F(q) = (Phi_4(q) Phi_9(q) Phi_25(q) Phi_30(q))^6

is a basic cyclotomic generating function of degree 216, with positive integer coefficients strictly increasing from degree 0 through degree 108 and strictly decreasing from degree 108 through degree 216. No Phi_p(q) with p prime divides F(q).

Consequently, F is a counterexample to Conjecture 48 in its full stated form.

## Proof

Set B = Phi_4 Phi_9 Phi_25 Phi_30. The four factors are

- Phi_4 = 1 + q^2
- Phi_9 = 1 + q^3 + q^6
- Phi_25 = 1 + q^5 + q^10 + q^15 + q^20
- Phi_30 = 1 + q - q^3 - q^4 - q^5 + q^7 + q^8

In particular, B and F are monic integer polynomials. Every root of F is a root of unity. Also,

B(q) = [4]_q [9]_q [25]_q [30]_q / ([1]_q [6]_q [10]_q [15]_q),

where [n]_q = 1 + q + ... + q^(n-1). Thus F has the required basic rational form, with no scalar or monomial multiplier.

Write F(q) = sum_(j=0)^216 a_j q^j. Every displayed cyclotomic factor is reciprocal, so a_j = a_(216-j). Exact multiplication gives the following centered q-integer expansion:

F(q) = sum_(j=0)^108 d_j q^j [217-2j]_q.

Here d_0 = a_0 = 1 and d_j = a_j - a_(j-1) for 1 <= j <= 108. The complete list of d_j follows. All entries are positive.

| Indices j | Values d_j in increasing index order |
| --- | --- |
| 0–9 | 1, 5, 15, 35, 64, 96, 126, 150, 180, 238 |
| 10–19 | 326, 426, 501, 531, 567, 701, 991, 1371, 1692, 1866 |
| 20–29 | 1980, 2326, 3071, 4023, 4806, 5124, 5250, 5856, 7269, 9147 |
| 30–39 | 10585, 11189, 11655, 13079, 15982, 19290, 21585, 22779, 24183, 27587 |
| 40–49 | 32545, 36825, 39095, 40213, 43527, 50235, 57570, 62100, 62948, 64882 |
| 50–59 | 72555, 84635, 95020, 97758, 96567, 100479, 113595, 130975, 140138, 138138 |
| 60–69 | 135060, 142464, 162645, 180663, 184173, 177591, 176555, 194149, 218922, 230692 |
| 70–79 | 223826, 212586, 221560, 248612, 269481, 265241, 241396, 232836, 254723, 286675 |
| 80–89 | 295956, 268346, 238156, 241074, 275394, 304410, 288381, 244691, 218995, 235689 |
| 90–99 | 273250, 275390, 232581, 184211, 174619, 208125, 227485, 197435, 138246, 102744 |
| 100–108 | 124275, 158475, 150360, 91356, 28794, 23500, 59600, 78150, 38406 |

For completeness, this identity can be checked using only the four displayed factors and integer polynomial multiplication; the accompanying standard-library verifier reconstructs both sides independently. The expansion implies a_j = sum_(i=0)^j d_i for 0 <= j <= 108, so all first-half coefficients are positive and strictly increasing. Reciprocity supplies the other half. This proves positivity and unimodality for the whole polynomial, with no numerical-root or asymptotic argument.

The cyclotomic polynomials are irreducible over Q and distinct cyclotomic polynomials are relatively prime. The complete factorization of F therefore has only orders 4, 9, 25, and 30. None is prime. Hence Phi_p does not divide F for any prime p. This also follows directly from root orders: a primitive pth root cannot be a primitive nth root for any n in {4,9,25,30}.

The degree is 6(2+6+20+8)=216>0, so F is not 1. The theorem and the negation of Conjecture 48 follow. QED.

## Exact certificate and reproducibility

Run `python verify_counterexample.py` in this directory. The script uses only Python's standard library and integer arithmetic. It independently:

1. Constructs Phi_n recursively from q^n-1 and verifies the four factor formulas.
2. Checks the q-integer numerator/denominator identity for B.
3. Expands B^6 and verifies all 217 coefficients and all 109 positive centered weights.
4. Reconstructs F from the centered q-integer expansion.
5. Checks directly that F has nonzero remainder modulo [p]_q for every prime p <= 217. Primes p > 217 are excluded by degree, because deg(Phi_p)=p-1>216.

The coefficient sum is 30^6 = 729000000. The unique peak is a_108=11434392. The minimum of a_j-a_(j-1), 1<=j<=108, is 5. The JSON certificate contains the full coefficient list, the centered weights, and every finite prime-order remainder.

Certificate SHA-256: 64b10e5427ecaaaf9076e5d8b592831393db9fcb2b412c5894fd928d5fd4dfad.

## Status and limitations

This is a full counterexample to the original universal conjecture, not a finite verification offered as evidence for a universal positive result. The candidate is frozen; no minimal-degree claim is made. No proof-assistant formalization or outside peer review is claimed here. Independent review is pending.

A current literature search found no prior resolution of Conjecture 48. The latest arXiv version, journal version, journal landing page, and the relevant 2026 follow-ups were checked. This is an evidence-based novelty check, not a proof that no prior result exists. The 2026 paper arXiv:2603.22226 explicitly resolves Billey--Swanson Problem 60 (HSOP membership), which is different from Conjecture 48. The 2026 overview arXiv:2608.30979 treats CGF monoids but no resolution of the prime-order-factor conjecture was found. A separate source audit records the searches.
