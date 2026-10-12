# Final-copy mathematical review

Date: 2026-10-08 (UTC).

## Verdict and frozen scope

**PASS.** I reread the complete final LaTeX source, independently checked the added short proofs and the integer-scaling conclusion, and rechecked the strict conditions and finite-choice order from the earlier adversarial review. I found no mathematical error, missing substantive hypothesis, or necessary mathematical revision in this copy.

The authoritative source inspected was:

- `paper.tex`: SHA256 `ac6983f69f78175ce119b253f22ae11336ba1e23af9e4c8b13b51d9b30e86411`

The corresponding reading copies present and checked were:

- `paper.pdf`: SHA256 `fcdf05b20799ec290db09a437fdce2b4d94fce636928a62caf14b318af7cdbdd`
- `proof.md`: SHA256 `20834610bc357b08ac69075d3102fc9e31df7bbebd2f6809114327a9ac4e2fa7`

The approval applies to these mathematical contents. Adding this report and updating package metadata/checksums does not change the mathematical source. Any subsequent mathematical edit requires review rather than silently inheriting these hashes' approval.

The final statement is a finite-existence theorem: some finite order N>4 admits a non-diagonal real symmetric positive-definite **integer** matrix B with P'_1(B)<0 and rational 0<q0<q1<1 with P_q0(B)>P_q1(B). There is no explicit dimension bound or numerical real witness. The intermediate PSD Gram matrix has rank at most four; the final PD matrix is full rank.

## 1. Integer scaling, equation (26)

Let the already constructed rational matrix be B, of the fixed finite order N, and choose a positive integer D divisible by every entry denominator. Each term in the defining q-permanent is a product of exactly N matrix entries. Therefore each coefficient in q is multiplied by D^N:

P_q(DB)=D^N P_q(B).

Since D is independent of q, differentiating this polynomial identity gives P'_q(DB)=D^N P'_q(B). No change to the inversion statistic, row order, q-parameters, or dimension occurs. Because D>0, D^N>0, so both strict inequalities survive at exactly the same rational q0,q1. Positive scalar multiplication also preserves real symmetry, non-diagonality, and quadratic-form positive definiteness. DB has integer entries by construction.

Thus equation (26) and the integer assertion in the abstract and theorem are correct. This is an exact scalar-multiplication corollary, not a newly computed counterexample. It imposes no requirement to make the original Gram rows integral.

## 2. Four added standard short proofs

### Deterministic equidistribution sequence

The compact metric sphere S^3 has a countable uniformly dense family of continuous functions. Apply the strong law to each function for independent Haar samples, intersect the countably many probability-one events, and fix one sample sequence in that intersection. Uniform approximation then proves convergence against every continuous function. The passage from the countable family to all continuous test functions is valid because empirical and Haar measures are probability measures. The manuscript therefore supplies the existence of the deterministic equidistributed sequence it uses; it makes no later independence assumption on the chosen sequence.

### Fischer pairing count

After expanding the two products of real linear forms, a given multi-index alpha specifies which occurrences carry each coordinate. For each coordinate a, there are alpha_a! bijections between the occurrences assigned to it in the two products. Their product alpha! is exactly the Fischer weight. Summing all such matchings is the cross-Gram permanent. The argument works for arbitrary real row lengths and for complementary products, including the empty products occurring when n=2. No determinant/cofactor sign or additional factorial is introduced.

### Complex projective monomial moments

Normalizing independent complex Gaussians produces a uniform complex unit vector. Its squared coordinate moduli are normalized independent exponential variables, hence Dirichlet(1,...,1). Coordinate phases kill distinct multi-indices, and the simplex monomial integral gives

integral |z^alpha|^2 dmu = alpha! (r-1)!/(d+r-1)!.

This yields the displayed Fischer-to-projective identity. In the ratio, the degrees are N-2 and N; for r=4 the factorial quotient is exactly (N+1)!/(N+3)! = 1/[(N+3)(N+2)]. The final copy retains these factors rather than inserting the rank-two normalization.

### Complex Cauchy Jacobian

With independent standard real Gaussian coordinates, each complex pair has density (2*pi)^(-1) exp(-|h|^2/2). The transformation (z,d) -> (zd,d) has real Jacobian |d|^2. If a=1+|z|^2, polar coordinates give

integral over C of |d|^2 exp(-a|d|^2/2) dd = 4*pi/a^2.

Multiplication by the joint density constant 1/(4*pi^2) gives 1/[pi(1+|z|^2)^2], exactly the stated density. The sphere-radius normalization and the balanced numerator/denominator factors 1/sqrt(2) cancel. No variance-convention discrepancy or missing factor remains.

## 3. Retained analytic and algebraic conditions

The final source preserves the following load-bearing conditions and arguments:

- The actual ordinary inversion-weighted q-permanent is explicitly defined. Marked inversions derive the endpoint identity, with increasing minors, no complementary cofactor signs, and one coordinate for each exterior basis pair a<b.
- Row repetition is contiguous. Same-block wedges vanish; pairs from distinct blocks yield the precise L^2 factor. The prefactor in the squared-norm ratio tends to 2/n^4 for a fixed base.
- The finite-product maximum is positive, so every denominator used at a maximizing point is nonzero.
- Phase changes are changes of the complex maximizing representative. Coordinate changes of the coefficient rows are real orthogonal, so reality of the rows is retained.
- The population logarithms are integrable even at the real endpoint. Strict concavity and symmetry force the unique balanced parameter t=1/2.
- The finite-cloud lower bound comes from exact O(4) averaging, not from an unjustified convergence of singular logarithmic potentials.
- The moving-maximizer upper bound uses the joint measures and the bounded continuous truncation log max(|v dot z|,exp(-K)). Compactness and integrability close the passage to the untruncated logarithm.
- Compactness of O(4) shows that the m-dependent real coordinate changes preserve weak equidistribution.
- The four-factor selector is proved on all of CP^3. Its unique modulus parameter and the equality phase condition leave precisely the distinct conjugate pair. It covers t=1/2 and requires only the eventually valid bound t<3/4.
- Multiplying by the selector preserves the original selected maximum and its conjugate, and removes all other global maxima.
- The limiting ratio is a quotient of independent complex Gaussian pairs. The appended four ratios are exactly zero and have vanishing empirical mass.
- The Gini calculation gives E|X-Y|=pi/2. The empirical conclusion uses bounded truncations and a lower limit, with the correct unordered-pair factor pi/4. It does not require uniform integrability or convergence of unbounded moments.
- Sorting is a choice of matrix index order. It is not asserted to preserve the q-permanent. The exact exterior-square transformation proves the full pointwise wedge norm is unchanged under the auxiliary unitary coordinates.
- The ordered real coefficients ensure equal g-values at the conjugate peaks without a second sorting. The quotient g is defined and continuous only on F!=0, at unit representatives.
- The strict threshold pi^2/16>1/2 is retained. In the concentration proof, zeros of F are handled by bounding the original numerator off the peaks. No global bound on g, nondegenerate Hessian, or equality of peak weights is assumed.

## 4. Quantifiers and the final perturbations

The source explicitly orders its choices correctly:

1. Fix the equidistributed sequence, then choose a sufficiently large but finite cloud, its four real selector rows, and the sorted base. Freeze that base.
2. Only then let the contiguous repetition number tend to infinity, and choose one finite L giving a strict negative endpoint derivative. Freeze N=nL.
3. Approximate finitely many row entries by rationals within an open neighborhood preserving the strict derivative and nonzero rows. No peak geometry or sorting property must survive this approximation.
4. Add a sufficiently small positive rational diagonal delta I. This preserves the strict derivative, gives positive definiteness, and changes no off-diagonal entry. Rank at most four and N>4 with positive diagonal ensure the preceding Gram matrix was non-diagonal.
5. Choose rational q0<q1 strictly within the interval to the left of 1 on which the derivative is negative.
6. Clear denominators with a positive integer scalar, keeping the same q0,q1.

All choices are finite. There is no simultaneous m,L limit or unsupported exchange of limits. The conclusion concerns parameters strictly inside the original interval, not merely q>1 or a singular PSD example.

## 5. Actual final-copy checks

I reran the following package programs under ordinary Python without optimization:

- `verification/check_exact_algebra.py`: PASS for 80 exact integer Gram/Fischer/marked-inversion cases; 9 exact contiguous-repetition identities; CP factorial quotients for r=2,...,6 and N=2,...,14; selector critical equations at five rational parameters.
- `verification/check_independent_algebra.py`: PASS for 90 exact arbitrary-rank endpoint/Fischer cases; 12 repetition/normalization cases; 6 selector cases.
- `verification/check_integer_scaling.py`: PASS for 30 rational Gram-plus-diagonal matrices of orders 2,...,6; coefficient-by-coefficient integer scaling; value and derivative scaling at four rational q-values.
- `verification/check_document_integrity.py`: PASS for nine extracted nonempty pages, page numbering, all 26 numbered equations and references, matching Markdown equation tags, absence of unresolved markers or replacement glyphs, absence of reported LaTeX box/reference problems, and extracted word bounding boxes inside the pages.

The Markdown version and extracted PDF text both contain the integer-scaling argument with equation (26) and the same conclusion. The source/PDF/Markdown hashes above were read after those checks. Pixel-level visual inspection is separately documented in `qa/QA_REPORT.md`; this report does not substitute an unperformed visual inspection for the mathematical and structural checks stated here.

These finite computations corroborate algebra and document consistency. They do not computationally certify the analytic limiting lemmas or produce a numerical real counterexample. This is an AI-assisted written mathematical review, not external human peer-review acceptance or a complete proof-assistant certificate.

## 6. Assertion-optimization safeguards and reproduction prerequisites

After the mathematical review, each of the three mathematical verifiers and the document-integrity verifier received an initial explicit `if not __debug__` guard. It writes a clear error and exits with status 2 before any success output if Python assertions are disabled. This packaging safeguard does not change the mathematical tests or any manuscript bytes.

I independently checked that removing the one added guard from each of the two original mathematical scripts recovers its original script byte for byte. I reran all three mathematical verifiers normally and obtained their original success results. I also independently tested all three under `-O`, `-OO`, `PYTHONOPTIMIZE=1`, and `PYTHONOPTIMIZE=2`: all 12 runs exited with status 2 and produced no PASS output.

Finally I inspected and ran `verification/check_optimization_guards.py`, whose decisions use explicit conditions rather than assertions. Its complete 16-case negative suite, including the document-integrity verifier, passed. A further normal run of the document-integrity verifier passed. The frozen `paper.tex`, `paper.pdf`, and `proof.md` hashes remained unchanged.

The three mathematical verifiers run directly from the distributed package with ordinary Python. Document QA additionally needs build artifacts: in particular `check_document_integrity.py` reads `paper.aux`, which is intentionally excluded from the compact distribution. Rebuild the LaTeX source first (two passes, or `build.sh`) before running that document checker, with its stated LaTeX/Poppler prerequisites. This dependency affects reproducibility instructions, not the proof or the correctness of the checks actually performed here.

## Final disposition

The final mathematical copy passes within its explicitly stated finite-existence scope, including the integer strengthening. No mathematical source edit is requested. The package may add this report and refresh its non-circular manifest and checksum files without changing the reviewed theorem or proof.
