# A finite exact counterexample to Bapat's q-permanent monotonicity conjecture

Date: 2026-10-08. This note gives a finite exact counterexample and two independently implemented integer verifiers. The statement concerns the original interval [-1,1]. No claim of historical priority or proof-assistant certification is made.

The matrices in this construction are complex Hermitian, including the positive-definite perturbation. They disprove the original Hermitian assertion, but the argument does not settle the real-symmetric restriction. This is a separate construction from counterexamples to a proposed extension beyond q=1.

## 1. Statement and exact data

For an n by n matrix A, define

P_q(A) = sum_{sigma in S_n} q^{inv(sigma)} product_i A_{i,sigma(i)}.

Bapat conjectured that this is strictly increasing for -1 <= q <= 1 whenever A is Hermitian positive definite and not diagonal. The complex-Hermitian formulation is explicitly stated on p.915 of Mitchell, *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14(4) (2020), 915–919, https://files.ele-math.com/articles/oam-14-56.pdf . Mitchell cites Bapat's original 1992 paper; Bapat–Lal (1994) is a subsequent source, not the first appearance.

Set n=200 and N=n(n-1)/2=19900. The accompanying CSV `counterexample_vectors_n200.csv` lists, in order, the four integer coordinates (Re a_i, Im a_i, Re b_i, Im b_i). Its SHA256 is

9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25.

All coordinates have absolute value at most 20. Define v_i=(a_i,b_i) in C^2, V to have these rows, and A=V V*. Thus A is Hermitian PSD and every diagonal entry is positive. The first two vectors are (13-5i,-6-13i) and (12-6i,-5-14i), and A_12=398-i, so A is not diagonal. Their determinant is 15-37i, so A has rank exactly two. Its entries have modulus at most 1600 by Cauchy–Schwarz.

Define the explicitly positive rational number

 epsilon = 1 / [4 N n! n 1601^{n-1}],

and B=A+epsilon I_n. This B is a completely specified non-diagonal Hermitian positive definite matrix. We prove below that

 P'_1(B) < 0.

This already disproves monotonicity on [-1,1], since the polynomial derivative remains negative just to the left of 1. An explicit rational subinterval is also given in Section 5.

## 2. An endpoint identity

For i<j and k<l, let A^{ij,kl} be the matrix formed by deleting rows i,j and columns k,l, retaining the other rows and columns in order. Counting inverted pairs in each permutation gives

 P'_1(A) = sum_{i<j, k<l} A_{i,l} A_{j,k} per(A^{ij,kl}).       (1)

For each of the N row pairs, expanding the permanent along those two rows gives

 N per(A) = sum_{i<j,k<l} [A_{i,k}A_{j,l}+A_{i,l}A_{j,k}] per(A^{ij,kl}).

Consequently

 2 P'_1(A) = N per(A) - H(A),                                 (2)

where

 H(A)=sum_{i<j,k<l} det A[{i,j},{k,l}] per(A^{ij,kl}).

These are identities for all complex matrices. The derivative in (1) is evaluated at q=1, so no inversion weight from the remaining permutation remains.

## 3. Rank-two reduction to integer polynomial arithmetic

Set ell_i(x,y)=a_i x+b_i y and

 F(x,y)=product_i ell_i(x,y),
 S(x,y)=sum_{i<j}(a_i b_j-b_i a_j) product_{r notin {i,j}} ell_r(x,y).

For a homogeneous binary form T(x,y)=sum_{k=0}^d t_k x^{d-k}y^k, use the Bargmann norm

 ||T||^2 = sum_{k=0}^d (d-k)! k! |t_k|^2.

The inner product of products of linear forms is the permanent of their cross-Gram matrix. This follows directly by expansion: matching identical monomials counts exactly all bijections of the factors. Hence

 per(A)=||F||^2.

Also

 det A[{i,j},{k,l}] = (a_i b_j-b_i a_j) conjugate(a_k b_l-b_k a_l).

Expanding ||S||^2 therefore gives H(A)=||S||^2. From (2),

 2 P'_1(A) = N ||F||^2 - ||S||^2.                             (3)

All coefficients of F and S are Gaussian integers for the specified V. If F_j and S_j use the first j rows, their exact recurrences are

 F_0=1, S_0=0,
 F_j=ell_j F_{j-1},
 S_j=ell_j S_{j-1}+b_j partial_x F_{j-1}-a_j partial_y F_{j-1}. (4)

The last two terms sum the new pairs (i,j), i<j, so (4) follows from the definitions without division or approximation.

## 4. The finite integer certificate

The standalone Python-standard-library verifier `verify_recurrence.py` reads only the CSV coordinates, constructs (4) using pairs of arbitrary-precision integers, and computes the factorial-weighted norms. It does not trust stored norms, an optimizer, numerical integration, floating-point arithmetic, or external packages.

Writing P=||F||^2 and D=||S||^2-N||F||^2, it verifies the strict integer inequalities

 P>0,
 23 N P < 1000 D < 24 N P.                                   (5)

In particular D is a positive integer (with 816 decimal digits), and (3) gives P'_1(A)=-D/2<0. The full exact D appears in `verification_recurrence_result.txt`; its size is not logically relevant, and (5) is checked directly by integer comparisons.

Reproduction command, from the directory containing the CSV and verifier:

 python verify_recurrence.py

A second independently implemented verifier, `verify_pairs.py`, constructs F, divides out every unordered pair of linear factors by exact Gaussian-integer synthetic division, and sums the defining terms of S directly. All 19,900 pair divisions have zero remainder, and all four large certificate integers agree. Neither verifier imports the other. The exact expected values are recorded in `expected_values.json`.

Numerical search helped find the vectors. It plays no role in the exact certificate (5) or the proof (1)–(4).

## 5. Positive-definite perturbation and an explicit interval

For any permutation sigma and 0<=t<=1, the product of n entries of A+tI differs from its value at t=0 in modulus by at most

 n t (1601)^{n-1}.

Indeed telescope the product and use |A_ij|<=1600 and |(A+tI)_ij|<=1601. Multiplying by inv(sigma)<=N and summing n! permutations yields

 |P'_1(A+tI)-P'_1(A)| <= N n! n t 1601^{n-1}.

For the specified epsilon this is at most 1/4. Since D>=1,

 P'_1(B) <= -D/2+1/4 <= -1/4.                                (6)

Hermitian symmetry makes P_q(B) real for real q: pair sigma with sigma^{-1}, which has the same inversion number and the conjugate product of entries.

Let

 K=N(N-1)n!1601^n,
 h=1/(8K),
 q_0=1-h.

For every q in [0,1], the second derivative satisfies |P''_q(B)|<=K, by termwise differentiation and inv(sigma)(inv(sigma)-1)<=N(N-1). Thus for q in [q_0,1], (6) gives

 P'_q(B) <= -1/4+Kh = -1/8.

Integrating gives

 P_{q_0}(B)-P_1(B) >= h/8 > 0,

where 0<q_0<1. This is a strict failure of increasing behavior inside the original interval, for the explicit positive definite B above.

## 6. Source scope and limitations of the novelty check

The exact conjecture is stated in Mitchell (2020), p.915; its PSD extension appears on p.917, and the bibliography on p.919 cites Bapat, *Interpolating the determinantal and permanental Hadamard inequality*, Linear and Multilinear Algebra 32 (1992), 335–337. Bapat–Lal (1994), *Inequalities for the q-permanent*, Linear Algebra and its Applications 197–198, 397–409, is an early follow-up: https://doi.org/10.1016/0024-3795(94)90497-9 .

The target was screened on 2026-10-08 around 11:03–11:05 UTC, before the main search. The review included the exact-name and title literature, proof/counterexample/erratum searches, Mitchell's primary journal article, the de Sá noncrossing special cases, and newer citations and public discussions. The source formulation and dated status searches were independently repeated after discovery, around 11:41–11:51 UTC. No prior general resolution was located. The independent public NLA problem audit dated 2026-09-10 also records the problem as unresolved in general:

https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-18/README.md

The Mitchell 2020 full journal text was obtained and checked. The 1994 publisher abstract was checked; the complete 1992 and 1994 original articles were not obtained in this audit. These access limits do not affect the explicitly stated formulation in the 2020 primary source.

This is a finite literature check, not proof of historical priority. Unindexed, unpublished, or newly appearing work could have been missed. Drury's known counterexamples to different Bapat–Sunder conjectures are not counterexamples to this inversion-weighted monotonicity statement. The argument here concerns the original interval [-1,1], not only a later proposed extension beyond 1.

## 7. Independent non-computational existence proof

The companion `asymptotic_existence_proof.md` provides a separate existence construction. Equidistributed points of CP1 are ordered after moving a product maximum to a pole; one additional factor makes the maximum unique. Adjacent repetition concentrates the endpoint ratio at that maximum. A real-projection Gini integral gives the strict lower asymptotic benchmark pi^2/8>1. That proof does not use the numerical witness or its finite integer calculation. The finite proof in Sections 1–5 does not rely on the asymptotic argument.
