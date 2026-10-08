# Independent audit: original Bapat q-permanent monotonicity conjecture

Date: 2026-10-08 (UTC).

Review provenance: an independent model-conducted mathematical and exact-arithmetic review, not anonymous journal peer review or proof-assistant certification. The historical references to the supplied drafts describe the inputs at the time of review; all three public verifiers and the complete independent certificate are included in this package.

## Verdict

**PASS for mathematical correctness of the finite counterexample.** The specified 200-row Gaussian-integer data, together with the stated positive diagonal perturbation, gives an explicitly defined non-diagonal Hermitian positive definite matrix B and an explicitly defined rational q0 in (0,1) for which P_q0(B) > P_1(B). This contradicts increasing monotonicity on the original interval [-1,1].

This is an independent rederivation and independent exact computation, not a blind review: the proposed proof and its data were supplied to the reviewer. No implementation from either supplied verifier was imported or run in the independent calculation. A new standard-library-only verifier uses direct pair deletion by exact polynomial division, rather than the author's incremental derivative recurrence or the second Koszul calculation.

**No substantive error was found.** The finite proof does not depend on the asymptotic mechanism, on a floating-point search, on a spectral version of a permanent conjecture, or on a formal proof assistant. Novelty is a separate question: the bounded literature search found no prior resolution of this exact original conjecture, but cannot establish priority. The 1992 full text and 1994 full text were not obtained in this audit; this limitation is stated explicitly below.

## 1. Exact object reviewed

For a matrix C of order n, the definition under review is

P_q(C) = sum over sigma in S_n of q^inv(sigma) product_i C[i,sigma(i)],

where inv(sigma) counts all pairs i<j with sigma(i)>sigma(j) in the fixed original ordering.

The reviewed CSV contains exactly 200 rows (Re a_i, Im a_i, Re b_i, Im b_i). Its byte-level SHA256 is

9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25.

Let v_i=(a_i,b_i), let V have these rows, and set A=VV*. The independent checks give:

- n=200 and N=binom(n,2)=19900.
- Every coordinate is an integer with absolute value at most 20.
- Every row is nonzero; in fact 374 <= A_ii <= 432.
- A_12=398-i, so A is non-diagonal.
- det(v_1,v_2)=15-37i, so A has rank exactly two.
- A is Hermitian positive semidefinite by its Gram construction.
- The claimed uniform bound |A_ij|<=1600 is valid. The smaller bound 432 also follows from the measured diagonal bound and Cauchy-Schwarz, but the proof deliberately keeps 1600.

The simultaneous row/column order is part of the example. Arbitrary permutation similarity need not preserve P_q. All computations used the CSV order without sorting or reindexing.

## 2. Derivation directly from the defining polynomial

Write w_sigma(C)=product_i C[i,sigma(i)]. Differentiate the finite sum at q=1:

P'_1(C)=sum_sigma inv(sigma) w_sigma(C).

Now mark one inversion in each summand. Fix its positions i<j and its two images k<l, so sigma(i)=l and sigma(j)=k. Once these four indices are fixed, sigma restricts to an arbitrary bijection from the remaining rows to the remaining columns. Thus

P'_1(C)=sum_{i<j,k<l} C[i,l] C[j,k] per(C with rows i,j and columns k,l deleted).    (2.1)

No inversion count of the smaller permutation is inserted. We differentiated first, marked an actual inversion of the full permutation, and then set q=1. This avoids the false general-q deletion formulas identified in the older literature.

For each fixed row pair i<j, every permutation uses exactly one unordered column pair k<l. Dividing according to whether those two images are increasing or decreasing gives

per(C)=sum_{k<l} (C[i,k]C[j,l]+C[i,l]C[j,k]) per(C with i,j;k,l deleted).

Summing over all N row pairs and subtracting twice (2.1) yields, for every complex matrix C,

N per(C)-2P'_1(C)
 = sum_{i<j,k<l} (C[i,k]C[j,l]-C[i,l]C[j,k]) per(C with i,j;k,l deleted).    (2.2)

There is no determinant cofactor sign on the complementary permanent. The complementary lists may be kept in increasing order; a permanent is also independently invariant under reordering its row list and column list. This does not assert any such invariance of a q-permanent.

### 2.1 Independent verification of the binary-form normalization

For a degree-d homogeneous binary form p=sum_k p_k x^(d-k)y^k define

<p,r> = sum_{k=0}^d (d-k)! k! p_k conjugate(r_k).

This convention is linear in the first argument. Let p=product_i(a_i x+b_i y), r=product_j(c_j x+d_j y), with d factors in each. Expand the permanent of M_ij=a_i conjugate(c_j)+b_i conjugate(d_j).

In each permutation summand, choose which k row factors use the second coordinate. An expansion term survives in the grouped coefficient sum precisely with a k-element choice on the column side too. For fixed row subset and column subset of size k, the number of bijections matching second-coordinate factors and first-coordinate factors is k!(d-k)!. This is exactly the coefficient weight in <p,r>. Consequently

per(M)=<p,r>.

In particular, for F=product_i(a_i x+b_i y), per(A)=||F||^2. The factorials are d! weights on the pure monomials, not reciprocals and not binomial coefficients alone.

### 2.2 Independent verification of the conjugations and determinant factor

Put delta_ij=a_i b_j-b_i a_j. Expanding the 2-by-2 Gram minor gives

A_ik A_jl-A_il A_jk = delta_ij conjugate(delta_kl).

Define f_ij=product over r other than i,j of (a_r x+b_r y). The preceding permanent identity gives <f_ij,f_kl>=per(A with i,j;k,l deleted). Therefore, for S=sum_{i<j} delta_ij f_ij,

||S||^2=sum_{i<j,k<l} delta_ij conjugate(delta_kl) per(A with i,j;k,l deleted).

Combining this with (2.2) proves

**2P'_1(A)=N||F||^2-||S||^2.**                                      (2.3)

This derivation never uses the Schur power matrix, a permanent-on-top conjecture, a conjecture about an F_A spectrum, or a replacement of inversion number by cycle count.

## 3. Independent exact computation

The new file `verify_by_pair_deletion.py` is self-contained apart from the accompanying CSV and Python's standard library. Gaussian integers are pairs of arbitrary-precision integers. Complex floating-point types, numerical quadrature, optimization output, and external packages are absent from the checked arithmetic.

### 3.1 Computational method

1. Multiply the 200 linear factors to obtain F.
2. For each i, divide F exactly by ell_i.
3. For every j>i, divide that result exactly by ell_j.
4. Add delta_ij times that quotient to S.
5. Apply the factorial-weighted sum of squared Gaussian-integer moduli to F and S.

All 19,900 pair contributions are explicitly accumulated. Synthetic division in ascending y-degree uses

q_0=p_0/a; q_k=(p_k-b q_(k-1))/a,

and checks the final equality p_d=b q_(d-1). Every Gaussian integer division separately asserts divisibility of both real and imaginary numerators by |a|^2. The zero-a case is implemented and tested as division by by. All a_i happen to be nonzero in this CSV.

This is a different computational dependency graph from the supplied recurrence S_j=ell_j S_(j-1)+b_j partial_x F_(j-1)-a_j partial_y F_(j-1). It is also different from a Koszul contraction calculation.

### 3.2 Results

Let P=||F||^2, Q=||S||^2, D=Q-NP. The independent calculation verifies

P>0, D>0, and 23NP < 1000D < 24NP.

Thus Q/(NP) lies strictly between 1.023 and 1.024; no rounded decimal is used to decide the sign. D is an even positive integer with 816 decimal digits. Equation (2.3) gives P'_1(A)=-D/2<0.

The full P, Q, D, the complete F and S coefficient lists, and the positive integer denominators of epsilon and h are recorded in `independent_certificate.json`. The complete console result is `verification_pair_deletion.txt`.

After the independent calculation finished, P, Q and D were compared against the author's certificate (its four summary integers are published here in `expected_values.json`); all three agree exactly. This comparison is not used as an input to the computation.

The SHA256 of the compact JSON serialization of the independently generated F and S lists (the exact serialization is specified in the script) is

b8f453959f6450751bc1fce7f5663fd2aae248a268fa02a8429564dc031acdb7.

### 3.3 Small-order adversarial checks

The verifier also performs 20 full-permutation tests on two-dimensional Gaussian-integer Gram matrices of orders 2 through 8, including zero coordinate factors and repeated factors. Each test checks:

- Every coefficient of the directly enumerated q-polynomial is real.
- Direct P_1 equals ||F||^2.
- Direct 2P'_1 equals N||F||^2-||S||^2.
- Pair-deletion forms agree coefficientwise with forms made by rebuilding every omitted-factor product from scratch.

Five further full-permutation tests on arbitrary complex matrices, one of each order 2 through 6, check (2.1) and (2.2) using separately enumerated complementary permanents. These matrices are not assumed Hermitian or Gram matrices. All tests passed.

These finite tests supplement the derivation; they do not replace it. No enumeration of 200! permutations was performed or claimed.

### 3.4 Reproduction

Run in this report's directory:

    python verify_by_pair_deletion.py

Or pass the CSV path explicitly as the first argument. Do not use Python's `-O` flag, which disables the script's assertion checks. A successful run ends in `All exact checks PASSED` and regenerates the independent certificate.

## 4. Positive definiteness and an explicit q inside the original interval

The singular Gram matrix alone already contradicts a PSD extension, but the original positive-definite formulation must also be addressed. The proposed explicit repair is correct.

Define

epsilon = 1 / (4 N n! n 1601^(n-1)),
B=A+epsilon I.

The denominator is a positive integer greater than 1, so 0<epsilon<1. For any nonzero column z,

z*Bz=||V*z||^2+epsilon ||z||^2>0.

Thus B is Hermitian positive definite. Its off-diagonal entry B_12=398-i remains nonzero.

For 0<=t<=1, compare the n factors of any permutation product of A+tI with those of A. Each factor changes by at most t; factors before or after replacement have modulus at most 1601. Telescoping proves a bound n t 1601^(n-1) for each product difference. Multiplying by inv(sigma)<=N and summing n! permutations gives

|P'_1(A+tI)-P'_1(A)| <= N n! n t 1601^(n-1).

At t=epsilon the right side is 1/4. Since D>=1,

P'_1(B) <= -D/2+1/4 <= -1/4.                              (4.1)

These quantities really are real: Hermitian symmetry conjugates a permutation product to its inverse-permutation product, and inv(sigma^-1)=inv(sigma). The same statement holds coefficientwise for the entire q-polynomial.

Set

K=N(N-1)n!1601^n, h=1/(8K), q0=1-h.

Then 0<q0<1. For 0<=q<=1, termwise polynomial differentiation gives |P''_q(B)|<=K. Terms of inversion degree 0 or 1 contribute zero to this derivative; there is no q=0 negative-power issue. From (4.1), for q0<=q<=1,

P'_q(B) <= P'_1(B)+K(1-q) <= -1/4+1/8 = -1/8.

Integration yields

**P_q0(B)-P_1(B) >= h/8 = 1/(64K) > 0.**                  (4.2)

This is an explicit rational q witness strictly within the original [-1,1] interval, not merely a sign at a point outside the conjectured domain. B has rational real and imaginary entries. The extremely small epsilon and h are mathematically valid; practical conditioning is irrelevant to this exact existence certificate.

## 5. Independent audit of the noncomputational mechanism

A separate detailed check appears in `asymptotic_audit.md`. Its proof is logically independent of the 200-row certificate. The key steps also pass the present review:

1. Contiguous replication L times gives F_L=F^L and S_L=L^2 F^(L-1)S. Noncontiguous replication would not justify this formula without another ordering argument.
2. The degree-d sphere integral is ||p||^2=(d+1)! integral_CP1 |p|^2. Both factorial losses for S_L, of degree nL-2, must be retained.
3. The exact ratio prefactor is 2L^2/[n^2(n^2L^2-1)], tending to 2/n^4.
4. At a unique projective maximum u of |F|, the weighted integral ratio tends to |S(u)/F(u)|^2. This remains valid despite poles at zeros of F: outside a neighborhood of u, the numerator is |F|^(2L-2)|S|^2 and is exponentially dominated.
5. Empirical projective equidistribution remains valid after the m-dependent rotation chosen at a maximizing point. Compactness of U(2), followed by weak convergence along a convergent subsubsequence of rotations, proves this; no independence of the rotation from the data is required.
6. All a_i are nonzero in peak coordinates because the maximum of a nonzero product is positive. The chart b/a has a single Haar-null exceptional point, so its real marginal weak limit is legitimate.
7. The real marginal density is 1/[2(1+x^2)^(3/2)], with CDF (1+x/sqrt(1+x^2))/2. Its independent-pair absolute difference has expectation pi/2. Bounded truncation min(|x-y|,T), rather than an unjustified moment-convergence assertion, gives liminf n^-2 sum_(i<j)|x_i-x_j| >= pi/4.
8. Appending u* z before rotation makes the selected peak unique. This factor has coefficient row conjugate(u); after rotating to the peak it is exactly (1,0). It changes the empirical measure by one atom and cannot invalidate the lower bound.
9. Sorting by Re(b_i/a_i) gives Re(S(u)/F(u))=sum_(i<j)|x_i-x_j|. This changes the matrix order deliberately; it does not claim the q-permanent is order-invariant.
10. Fix a number eta with 1/sqrt(2)<eta<pi/4. First choose and freeze a sufficiently large finite base configuration with score greater than eta n^2 and a unique peak. Only then let L tend to infinity. Its limiting replication ratio is greater than 2eta^2>1, so a finite L exists. No simultaneous unproved limit or numerical extrapolation is needed.

The constant pi^2/8 is a lower asymptotic benchmark for these base-configuration/repetition limits. The current argument does not establish that every chosen configuration has exact limit pi^2/8. Any statement calling it a universal exact limit should be replaced by the correct lower-limit statement. This is a precision issue, not a gap in the disproof.

## 6. Literature and scope audit

### 6.1 What the primary sources establish

The exact original target is explicit on p.915 of Lon Mitchell, *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14(4) (2020), 915–919. It is about non-diagonal Hermitian positive definite matrices and strict increase in q on [-1,1]. The paper's p.917 gives the PSD/no-zero-row extension; pp.916–918 discuss transfer to the PD case and distinguish the stronger da Fonseca extension. Reference [2] credits Bapat's 1992 article; reference [4] gives Bapat–Lal 1994. [Primary paper](https://files.ele-math.com/articles/oam-14-56.pdf).

The official publisher abstract of Bapat and Lal, *Inequalities for the q-permanent*, Linear Algebra and its Applications 197–198 (1994), 397–409, independently confirms the inversion statistic and the PD/non-diagonal strict monotonicity conjecture on [-1,1]. The abstract credits one of its authors with the earlier conjecture. [Official article record](https://www.sciencedirect.com/science/article/pii/0024379594904979).

Bapat's own survey, *Recent developments and open problems in the theory of permanents*, Math. Student 76 (2007), restates monotonicity for PSD matrices as Conjecture 7, attributes it to his earlier reference [3], and reports only n<=3 there. [Author-hosted manuscript, p.13](https://www.isid.ac.in/~rbb/imsperm.pdf), [journal issue, p.65](https://www.indianmathsoc.org/ms/mathstudent2007.pdf).

For the original citation, use Bapat, *Interpolating the determinantal and permanental Hadamard inequality*, Linear and Multilinear Algebra 32(3–4) (1992), 335–337. DOI: [10.1080/03081089208818174](https://doi.org/10.1080/03081089208818174). Some older bibliographic records label it 1991 or use the generic heading *Research problem*. **The original 1992 full text was not directly inspected here**: its attribution and date are corroborated by Mitchell, Bapat's own later survey, and de Sá. The 1994 full paper was also not obtained; only its official publisher abstract was directly inspected. Do not describe those two full texts as reviewed.

### 6.2 Corrections and nearby statements

De Sá's *Letter to the editor on flawed mu-permanental formulas* supplies counterexamples to general-q formulas and the tree-proof ingredients in da Fonseca's 2005 paper. It is not a counterexample to the original Bapat monotonicity statement. [Primary manuscript](https://www.mat.uc.pt/preprints/ps/p1519.pdf).

De Sá's *Noncrossing partitions, noncrossing graphs, and q-permanental equations* explains why arbitrary permutation similarity cannot be used in these arguments; see the discussion after Corollary 4.5. Its Theorems 6.1–6.2 establish special noncrossing cases rather than the unrestricted conjecture. [Primary manuscript](https://www.mat.uc.pt/preprints/ps/p1722.pdf), [official article](https://www.sciencedirect.com/science/article/pii/S0024379517306523).

Da Fonseca's *The mu-permanent revisited*, arXiv:1804.02231, explicitly distinguishes Conjecture 1 on [-1,1], Conjecture 2 extending past that interval, Conjecture 3 about subset-preserving permutations, and Conjecture 4 about Schur-power eigenvalues. Its section 3 corrects graph-labeling conditions. These are different statements; no solution of a neighboring statement substitutes for a resolution of Conjecture 1. [Primary manuscript, sections 3–5](https://arxiv.org/pdf/1804.02231).

The 2026 preprint *The limits of Schur multipliers in Polya conversion problems for the q-permanent function*, arXiv:2605.24349, concerns linear/multiplier conversion and preservers. Its inspected text does not discuss monotonicity and supplies no competing resolution of the present target. [Primary preprint](https://arxiv.org/html/2605.24349v1).

### 6.3 Bounded novelty check

Searches on 2026-10-08 included the exact conjecture name, q-permanent and mu-permanent monotonicity, proof, counterexample, erratum/corrigendum, and 2025–2026 date terms. Results were checked against primary papers where relevant. No prior proof or counterexample to the unrestricted original Hermitian statement was located.

This is a bounded discovery result. It does not rule out unindexed, unpublished, differently titled, or very recent work. The public OpenProblemsInNLA MI-18 entry, last checked 2026-09-10, also retains the problem as partially resolved; it is corroborating status evidence only, not mathematical evidence and not a proof of priority. [Catalog entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-18/README.md).

## 7. Referee recommendations and trust boundary

- The finite theorem is ready for further expert mathematical review as a genuine exact counterexample claim.
- Keep the full CSV and a short independent verifier with the exposition; preserve its exact row order and byte-level hash.
- State explicitly that the witness is complex Hermitian. This audit makes no claim to settle a separate restriction to real symmetric matrices.
- Keep the explicit PD perturbation and q0 witness. They avoid ambiguity about singular-only extensions and the original interval.
- Present the asymptotic proof as a separate proof, with the two limits in the specified order and the pi^2/8 statement phrased as a lower benchmark.
- Correct the draft's status line from “independent review pending” only to describe the actual review performed; do not imply journal peer review or a formal-kernel certificate.
- No Lean installation, Lean formalization, publication, repository push, or external submission was performed in this audit.
- The computation relies on the correctness of ordinary Python integer arithmetic and the short auditable program. The mathematical reduction and perturbation are proved in ordinary mathematics; the result is not machine-kernel formalized.

No mathematical revision is required to the supplied finite argument for the stated complex-Hermitian target. The remaining issues are exposition precision, full-text historical sourcing, and establishing novelty through the normal scholarly process.
