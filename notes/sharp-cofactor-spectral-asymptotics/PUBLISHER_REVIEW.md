# Publication owner's independent final-copy review

Date: 8 October 2026. Verdict: **PASS within the stated mathematical scope**.

The publication owner separately read the final mathematical manuscript and stage summary, checked the analytical arguments below, and executed the exact finite verifiers in a fresh copy. All 23 frozen author files are retained byte for byte. This review records a separate analytical and executable check. The package has no Lean formalization, and the review is not an exhaustive novelty certification.

## 1. Statements and conventions

The domain is complex Hermitian PSD matrices with positive permanent. The cofactor matrix is C(A)[i,j] = a[i,j] per A(i|j), without transposing the deleted minor. Inner products are linear in the first argument, so the vector-valued Fock polynomial for a Rayleigh test uses conjugate(w[i]). The real extremum concerns real vectors for complex matrices, equivalently lambda_max(Re C(A)); it does not restrict A to real matrices.

The four logarithmic limits have leading constants 1 for complex vectors and 1/2 for real vectors. The lower examples are rank-exactly-two correlation matrices for every sufficiently large order. The positive-definite correlation assertion concerns the unrestricted-rank extrema. The ramp result is a limsup, and its universal upper bound has no rank restriction. The endpoint interpretation and its sharp pi^2/8 constant concern rank two.

## 2. Positivity and the binary indicator bound

The Gram/Fock identities give per A = norm(product ell_i)^2 and C(A) as the Gram matrix of v_i tensor product_{j!=i} ell_j. They prove cofactor PSD also for singular Gram matrices. Permanent expansion along each row gives C(A) 1 = per A 1.

For a subset of size a and complement of size b, average the two row tensors separately over S_a and S_b, obtaining symmetric tensors u and v. Permutations making j moves from each block to the other form a double coset of size a! b! binom(a,j) binom(b,j).

The representative partial swap coefficient is the sum over remaining-coordinate indices x,y of

    | sum_r u[x,r] conjugate(v[y,r]) |^2,

where r consists of the j contracted coordinates. Thus each class contribution t_j is nonnegative. Symmetry makes the representative coefficient constant on its double coset after averaging on both sides. A class contributes a-j internal directed matches, so the binary quadratic form is sum_j (a-j)t_j <= a sum_j t_j = a per A. This supplies the required k=1 inequality directly; no inaccessible all-k theorem is assumed.

## 3. Layer decomposition upper bounds

For a sorted nonnegative vector x, its nested-indicator decomposition gives

    norm(M^(1/2) x) <= sum_j x_j (sqrt(j)-sqrt(j-1))
                     <= sqrt(S_N) norm(x),

for M=C(A)/per A and S_N=sum_j (sqrt(j)-sqrt(j-1))^2. Splitting into positive and negative real parts gives squared bound 2 S_N; using the four real/imaginary positive parts gives 4 S_N. Since S_N=(1/4)log N+O(1), these are the correct leading upper constants. The manuscript's explicit harmonic bounds also follow termwise.

## 4. Sparse ring construction and sharp lower limits

The entropy lemma is valid for every subset of a geometrically separated sequence: the prefix/tail comparison implies a normalized tail at index k of at most b^(-k). Its mean index is at most 1/(b-1), and relative entropy against the geometric distribution gives the stated E(b).

The ring polynomial has the stated positive magnitude and an independent sign. Distinct subsets have orthogonal sign characters even when their degree sums coincide; the expectation of the squared coefficient therefore has the displayed subset sum. The binomial bound follows from h! <= e h (h/e)^h and (N)_h >= (N-h)^h. With h=2j <= delta N, each term is at most 2 e j q^j.

The subset generating function and the full integer-tail bounds make the expectation at most 1+eta once d_0 is fixed sufficiently large. Finite averaging selects a sign choice separately for each N. It does not require convergence of an infinite random sign sequence.

All parameters b, delta, eta, C and d_0 are fixed before N grows. The recurrence d_(k+1)=ceil(b d_k) gives K=log N/log b+O(1). The reserve rows and nonzero ring slopes guarantee rank two for every sufficiently large N. Ring sizes at least four guarantee sum z_i^2=0, hence sum (Im z_i)z_i=i norm(Im z)^2. Keeping the marked Fock coefficient gives the complex lower bound K/[C(1+eta)] and exactly half for the real test.

Only after taking the lower limit in N are the fixed parameters moved toward their endpoints. E(b)log b tends to e as b decreases to 1, recovering constants 1 and 1/2. The order of these quantifiers is sound.

## 5. Correlation normalization and positive-definite perturbation

Positive diagonal congruence multiplies both C(A) and per A by the same positive scalar. A PSD matrix with positive permanent has no zero diagonal entry, so correlation normalization is available.

At each finite order, (A+epsilon I)/(1+epsilon) is positive-definite correlation, and the normalized Rayleigh quotients are continuous as epsilon decreases to zero. This retains any strict smaller finite lower bound. This perturbation has full rank for orders greater than two; it is not used to preserve the rank-two assertion.

## 6. Ramp upper bound and lower limsup

Centered tail indicators u_j satisfy u_j^* M u_j <= j(N-j)/N and w=2 sum_j u_j. The triangle inequality gives exactly the manuscript's B_N, and the integral of sqrt(t(1-t)) on [0,1] is pi/8, producing 3 pi^2/16.

For the lower construction, rotation by projective maximizers preserves asymptotic Haar empirical distribution by compactness of the unitary group. The ratio map has a single Haar-null pole. Its real marginal has the stated density and distribution function; integrating 2 F(1-F) gives E|X-Y|=pi/2.

The passage to empirical pair distances first truncates the continuous distance, then increases the truncation. It needs only a lower limit and does not assume convergence of unbounded moments. Appending a row peaked at the chosen maximizer creates a unique projective maximum, adds a zero ratio, and leaves the lower pair-distance limit intact. Stationarity yields sum z_i=0.

For each fixed base, repeated-row compression has the exact factor L/(nL+1). Outside a neighborhood of the peak, cancellation by P/ell_i and P/ell_j controls the apparent poles and gives exponential tail decay. Thus K_L tends to (J+zz*)/n with the base fixed. The larger ramp compresses to L^(3/2) times the base ramp, and its limiting quotient is 3 |sum_i (2i-n-1)z_i|^2/n^4. Sorting real parts identifies its real sum with the unordered absolute pair sum. A diagonal sequence of finite bases and sufficiently large finite repetitions establishes a limsup, as claimed, rather than an all-order ramp limit.

## 7. Rank-two endpoint conversion

For binary row forms, the determinant polynomial S satisfies G_w=(-y,x)S. For its degree n-2, the Fock identity gives norm(xS)^2+norm(yS)^2=n norm(S)^2. Therefore the endpoint ratio is the ramp quotient times 2(n+1)/(3n), tending to 2/3. This converts 3 pi^2/16 into pi^2/8 and reproduces the displayed finite bound D_n.

Expanding the paired two-row determinants counts each permutation with coefficient binom(n,2)-2 inv(sigma), yielding 2 P'_1=binom(n,2)per A-norm(S)^2. This uses the rank-two binary-form determinant identity. The review approves no arbitrary-rank endpoint extension.

## 8. Finite exact reproduction

The publisher ran both normal primary cases (K,C)=(8,7),(10,5), the independent marked-product/recursive-weight program, and the rank-two threshold verifier. Every process exited zero. All six regenerated result/value JSON files match the frozen author files byte for byte.

The independent program additionally computed the order-eight Gaussian-integer Gram permanent, all 64 deleted cofactors and their row sums, and both full Rayleigh quotients. It matched the polynomial formulas exactly. The finite complex/real intervals are respectively (1.137,1.138)/(0.639,0.640) at order 512 and (1.991,1.992)/(1.094,1.095) at order 2048.

The analytic dyadic formulas and their integer scaling were checked separately in the read-through. The binary-coefficient and marked-product programs implement different coefficient recurrences and different factorial-weight calculations. These finite computations illustrate the formulas; they do not substitute for the asymptotic proof.

The publisher selected one necessary optimization-mode rejection per program: -O, -OO, and PYTHONOPTIMIZE=2. All three rejected with the expected message before changing any result JSON. The original author record of twelve negatives is retained and was not unnecessarily rerun in full.

## 9. Marcus stage barriers and James vectorization

The rank-at-most-two Jensen argument has the factor (N+1)! and expectation of log |<v,U>|^2 equal to -1. The block permanent matrix is a PSD Gram matrix; its diagonal entries are at most k!, and Cauchy--Schwarz gives per G <= m!(k!)^m. These prove the stated sufficient exclusion Q(m,k)>=1.

The monotonicity ratios in m and k were algebraically checked with m=block count and k=block size. The exact rational threshold program confirms (7,2),(4,3),(3,7). Its geometric-tail bound proves e<87/32. The remaining m>=3,k>=2 pairs have maximal order 18, so the stated rank-two order-at-least-19 exclusion is justified. The unexcluded low-order cases and growing rank remain outside this conclusion.

A separate publisher program in exact Q(sqrt(3),i) arithmetic verifies the James matrix is Hermitian, J^2=2sqrt(3)J, trace J=4sqrt(3), per J=24, and every deleted minor satisfies D=4sqrt(3)I+2conjugate(J). The two nonreal A4 characters evaluate to 0 and 24. These identities prove rank-two PSD and that D has positive eigenvalues 4sqrt(3),8sqrt(3).

For clarity, the stage summary's quadratic expression D^T tensor D uses **row-major vectorization** of E. With column-major vectorization it is D tensor D^T. The coefficient of E_ab conjugate(E_cd) is D_ac D_db in either convention after the corresponding index permutation; both Kronecker matrices are positive-definite. This is a notation convention, and does not change the local positive-gap conclusion.

The character off-diagonal terms are homogeneous of degree four, so their first pair contribution has order t^8, while the permanent has the strictly positive t^2 coefficient. This excludes the specified fixed-diagonal local coupling when PSD. It does not exclude remote couplings or moving diagonal blocks.

## 10. Source, status and document boundaries

The publisher checked the primary arXiv metadata/abstracts at:
- https://arxiv.org/abs/2202.01867v1
- https://arxiv.org/abs/2508.00111v1
- https://arxiv.org/abs/2608.21749
- https://arxiv.org/abs/2609.13412

The recent works have the stated finite partial scopes. These metadata checks are distinct from the author-side full-text readings recorded in SOURCE_AUDIT.md. No additional inaccessible Pate full-text premise was introduced.

All nine PDF pages were rendered and inspected as a page overview; dense ring, concentration and endpoint pages were also inspected at full reading scale. The supplied nine-page PDF and TeX remain unchanged. The typeset manuscript and SOURCE_AUDIT.md supply the complete reference labels; PROOF.md is their derivative text rendering.

The original arbitrary-subgroup Lieb and equal-block Marcus targets are unresolved. The missing legal subgroup/character realization is explicitly retained. The internal higher-compound calculation was not independently rerun, is outside this minimal certificate set, and is not a premise of the main theorems. The inaccessible Pate 2008 theorem has no certified full-text interpretation here; no error in that theorem is claimed. The finite literature search establishes no worldwide-first guarantee.

## Provenance and publication coverage

Input archive: sharp-cofactor-extrema.zip, 330828 bytes, SHA256 fac653bd1ab682991a222c908a08e2719a2fd9814e971334e8a7f269f2e517e7.

The original MANIFEST.json and SHA256SUMS are preserved. PUBLICATION_MANIFEST.json and PUBLICATION_SHA256SUMS cover the complete publication payload and the added publisher records, with the standard explicit exclusions needed to avoid self-hash cycles. The actual commit and Release records bind the complete file set, including those two control files.
