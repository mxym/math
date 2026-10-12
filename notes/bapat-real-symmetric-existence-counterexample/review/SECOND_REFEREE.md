# Second independent adversarial referee report

Date: 2026-10-08 (UTC).

Input: `../PROOF_DRAFT.md`, SHA-256
`78a5f7e5252c5ffac09a75d9254060275e9e8a94924e40382492468e71088357`.

## Verdict and exact scope

**PASS as a nonconstructive finite-existence theorem.** I independently rederived the analytic chain and finite algebra before reading the first referee's report. I did not treat that report's PASS as evidence for correctness. The subsequent comparison revealed no discrepancy in the mathematics.

The proved statement is:

> There exist a finite integer N, a non-diagonal matrix B in Sym_N(Q) which is positive definite, and rational numbers 0 < q0 < q1 < 1, such that P_q0(B) > P_q1(B), where
> P_q(A) = sum over permutations sigma of q^{inv(sigma)} product_i A_{i,sigma(i)},
> and inv is the ordinary inversion count in the chosen row/column order.

The proof supplies neither an explicit dimension bound nor an explicit numerical real matrix. The rank-at-most-four assertion applies to the intermediate positive-semidefinite Gram matrix, not to the final positive-definite matrix. No reduction from, or reliance on, the separate explicit complex example is needed. I found no missing generic-position, Hessian, uniform-integrability, or moment-convergence hypothesis.

The supplied wording still merits the small precision edits in Section 12. In particular, the quotient g is not claimed to be continuous at a zero of F. This is a wording correction, not a failure of the concentration argument, which correctly bypasses those zeros.

## 1. Independent endpoint derivation: the actual q-permanent

Let v_1,...,v_n be arbitrary real coefficient rows in R^r; normalization is unnecessary here. Put A_ij = v_i dot v_j. For an increasing pair I={i,j}, write D_I^{ab} = v_ia v_jb-v_ib v_ja, and write F_I for the product of all linear forms except those indexed by I. Thus S_ab = sum_I D_I^{ab} F_I.

Differentiating the defining permutation sum at q=1 counts marked inversions. For fixed i<j and k<l, a marked inversion assigns i to l and j to k, while all complementary assignments are unrestricted. Therefore

P'_1(A) = sum_{i<j,k<l} A_il A_jk per A[{i,j}^c,{k,l}^c].

For each row pair i<j, its two-row permanent expansion is

per A = sum_{k<l} (A_ik A_jl + A_il A_jk) per A[{i,j}^c,{k,l}^c].

Summing the second identity over row pairs and subtracting twice the first gives

binom(n,2) per A - 2P'_1(A)
= sum_{I,J} det A[I,J] per A[I^c,J^c].

There are no cofactor signs attached to complementary permanents. Cauchy–Binet for A=VV^T gives det A[I,J] = sum_{a<b} D_I^{ab}D_J^{ab}. The Fischer inner product of the two complementary products equals per A[I^c,J^c]; this follows by the coefficient/matching expansion. Consequently

2P'_1(A) = binom(n,2) ||F||_F^2 - sum_{a<b} ||S_ab||_F^2.

This derivation applies to the inversion-weighted polynomial, not a cycle-weighted alpha-permanent or another q-deformation. It also explains why row order can matter later. Using only a<b gives precisely one orthonormal exterior coordinate for each unordered coordinate pair: no extra factor of two occurs.

## 2. Contiguous repetition and the CP moment factors

Keep the base row order fixed. Make L consecutive copies of v_1, then L copies of v_2, and so forth. Within a block the wedge is zero; across two different blocks there are L^2 identically oriented terms. Direct expansion yields the polynomial identities

F_L=F^L, and S_L=L^2 F^(L-1) S.

An arbitrary interleaving of the repeated rows would not justify the latter identity. The prescribed contiguous order does.

Let mu be normalized unitary-invariant measure on CP^(r-1), and evaluate homogeneous polynomials on unit representatives. Coordinate phase integration kills unequal monomials, while the squared moduli have the Dirichlet(1,...,1) distribution. Hence, for |alpha|=d,

integral |z^alpha|^2 dmu = alpha! (r-1)!/(d+r-1)!,

and

||T||_F^2 = (d+r-1)!/(r-1)! integral |T|^2 dmu.

For N=nL, the degrees in numerator and denominator are N-2 and N. In particular, for r=4 their normalization constants are (N+1)!/6 and (N+3)!/6. Their ratio is exactly 1/[(N+3)(N+2)], not a rank-two substitute. Thus

R_L := ||S_L||_F^2/[binom(N,2)||F_L||_F^2]
= L^4/[binom(N,2)(N+r-1)(N+r-2)]
  times [integral |F|^(2L-2)|S|_wedge^2 dmu / integral |F|^(2L) dmu].

For a fixed finite base, the prefactor tends to 2/n^4. The numerator integrand uses the pointwise Euclidean norm of the wedge-coordinate vector; it does not take a Fischer norm at a point.

## 3. The moving-maximizer step survives the singular logarithm

A weakly equidistributed deterministic sequence of points on S^3 exists, for example by fixing a realization of independent Haar samples whose empirical measures converge weakly. No subsequent randomness is needed. Denote its empirical measure by nu_m.

Each finite product F_m is a nonzero polynomial. A finite union of proper complex hyperplanes cannot fill C^4, so max |F_m|>0. In particular every factor is nonzero at every maximizing point u_m.

### 3.1 Real canonical form and an intrinsic balance parameter

For a unit complex vector u=x+iy, multiplication by a scalar phase diagonalizes the real 2-by-2 Gram matrix of x,y. A further phase can exchange their lengths. A real orthogonal transformation then gives

u = sqrt(t)e1 + i sqrt(1-t)e2, with 1/2 <= t <= 1.

The invariant parameter is t=(1+|u^T u|)/2. Thus it is continuous on projective space, and balanced points are exactly those with u^T u=0. This also avoids any dependence on a globally continuous choice of phase or coordinates.

A phase changes the representative of a maximizing point; it need not multiply any row by a complex number. The coordinate transformation applied to the coefficient rows is real orthogonal. All original rows consequently remain real.

### 3.2 Population potential and its strict maximum

For uniform sigma on S^3 set U(u)=integral log|v dot u| dsigma(v). With G a standard real Gaussian in R^4, canonical form gives

U(t) = (1/2) E log[tG1^2+(1-t)G2^2] - E log||G||.

The logarithms are integrable, including at t=1. For t>=1/2 the first logarithm is bounded below by log(t)+log(G1^2), and bounded above by log(G1^2+G2^2), both integrable. The remaining Gaussian-radius logarithm is integrable as well. Symmetry t <-> 1-t and strict concavity, since G1^2 differs from G2^2 almost surely, give a unique maximum at t=1/2.

An independent explicit check is

U(t) = -1/2 + log[(sqrt(t)+sqrt(1-t))/2].

To see this, v1^2+v2^2 is uniform on [0,1], its polar angle is uniform and independent, and the elementary circular logarithm integral supplies the displayed expression. In particular U_bal = -(1+log 2)/2, whereas U(1)=-1/2-log 2 is strictly smaller. This check also includes the possibly dangerous real endpoint.

### 3.3 The lower bound does not assume empirical logarithm convergence

Fix u_bal=(e1+i e2)/sqrt(2). For every individual unit real row v, Haar averaging log|v dot R u_bal| over O(4) gives U_bal. These individual logarithms are integrable. A finite sum therefore gives

max_z (1/m)log|F_m(z)| >= U_bal

for every m, irrespective of how poorly the discrete cloud samples the singular logarithm. This is the needed exact lower bound, not a weak-convergence claim for an unbounded function.

### 3.4 A fully justified moving upper bound

Take a subsequence of projective maximizers converging to [u], and choose convergent unit representatives. On the compact product of S^3 and the unit complex sphere, set

phi_K(v,z)=log max(|v dot z|, exp(-K)).

For each fixed K this is bounded and continuous. The joint measures nu_m tensor delta_{u_m} converge weakly to sigma tensor delta_u. Equivalently, uniform continuity makes phi_K(v,u_m)-phi_K(v,u) tend uniformly to zero in v. Consequently

limsup_m (1/m)log|F_m(u_m)| <= integral phi_K(v,u) dsigma(v).

Let K tend to infinity. Monotone convergence applied to the negatives, or integrability of the limiting logarithm, gives the upper bound U(u). Combined with the lower bound, this implies U(u)>=U_bal. Uniqueness of the population maximum forces u to be balanced. Compactness and continuity of t then prove t_m -> 1/2.

This closes the most plausible failure mode: applying Portmanteau only in the row variable while overlooking the moving maximizer would be insufficiently explained, but the joint-measure/truncation proof is valid.

## 4. Moving real rotations do not destroy equidistribution

Let R_m be any choices of the real orthogonal coordinate changes above. Take any subsequence. Compactness of O(4) supplies a further subsequence with R_m -> R. For a continuous test function f, f(R_m v) -> f(Rv) uniformly on S^3. Thus the transformed empirical measures converge along that subsequence to R_*sigma=sigma. All subsequences have the same possible limit, proving convergence of the full transformed sequence.

There is no measurability, uniqueness, or equivariance requirement on the choices of maximizing point or rotation. Weak convergence is enough. Scaling the representative u_m by a phase also has no effect on reality of rows.

## 5. The four-real-factor selector is global on CP^3

For sufficiently large m, 1/2 <= t_m < 3/4. Write t=t_m and

c=(2t-1)/[t(3-4t)], a=sqrt(1+c),
H_t(z)=z1 z2 (a z1+z2)(a z1-z2).

The four coefficient rows are real, nonzero, and nonvanishing on u and conjugate(u).

If rho^2=|z1|^2+|z2|^2<1 and H_t(z) is nonzero, normalizing these two coordinates increases its modulus by rho^(-4). A global maximum is positive, so every maximizer has rho=1. Thus there are no overlooked maxima elsewhere in CP^3.

With s=|z1|^2 and |z2|^2=1-s,

|H_t(z)| <= sqrt(s(1-s)) [a^2 s+(1-s)]
= f_c(s):=sqrt(s(1-s))(1+cs).

For 0<s<1, f'_c has the sign of

p_c(s)=1-2s+c(3s-4s^2).

When c=0 the unique root is 1/2. For c>0 the two quadratic roots have negative product -1/(4c); p_c(0)>0 and p_c(1)<0. There is exactly one root in (0,1), and it is the unique maximum because the derivative changes from positive to negative. The prescribed c makes that root t.

At this interior maximum, triangle-inequality equality requires z1^2 and z2^2 to have opposite arguments. Their relative phase is therefore +pi/2 or -pi/2, modulo a common phase. The only projective maxima are exactly [u] and [conjugate(u)]. This remains true at t=1/2; these two projective points are distinct.

Both also maximize |F_m| because its coefficients are real. The product |F_m H_t| attains the product of the two individual maxima there. Equality anywhere else would require simultaneous equality for both factors, so its maximum set is exactly this pair. This argument does not require isolated original maxima or a nondegenerate Hessian.

Normalizing the four new real rows only multiplies the product by a positive constant. In fact scaling any rows by nonzero real factors multiplies both F and S by their total product, and leaves g unchanged.

## 6. The independent complex-Gaussian ratio and correct scaling

In the canonical coordinates take w=(e3+i e4)/sqrt(2), a Hermitian unit vector orthogonal to u_m. For every original row set

z_i=(v_i dot w)/(v_i dot u_m), and x_i=Re z_i.

The denominators are nonzero at the selected maximum. The map of (v,t) to this ratio is continuous outside v1=v2=0 at t=1/2, a set of sigma-measure zero. The joint empirical measures of (v_i,t_m) converge to sigma tensor delta_{1/2}, so the almost-everywhere continuous mapping theorem applies, even though ratios can be arbitrarily large on the discrete clouds.

Writing v=G/||G||, the common real normalization cancels. At balance the factors 1/sqrt(2) in the numerator and denominator also cancel, leaving

Z=(G3+iG4)/(G1+iG2).

The two Gaussian pairs are independent; the denominator is not the conjugate of the numerator or another correlated projection. Any convention about variance of a standard complex Gaussian cancels in this ratio. Direct change of variables (z,d) -> (zd,d), with real Jacobian |d|^2, gives

f_Z(z)=1/[pi(1+|z|^2)^2].

Integrating the imaginary coordinate gives the real marginal

f_X(x)=1/[2(1+x^2)^(3/2)],
J(x)=(1+x/sqrt(1+x^2))/2.

For independent copies X,Y, the indicator formula for absolute difference and Tonelli give

E|X-Y|=2 integral J(x)(1-J(x)) dx
=(1/2) integral dx/(1+x^2)=pi/2.

The four appended rows have numerator zero and nonzero denominator, hence four exact additional zeros. Their empirical mass vanishes as n=m+4 tends to infinity.

Let eta_n be the empirical law of all n real ratios. Weak convergence of eta_n implies weak convergence of eta_n tensor eta_n. For h_T(x,y)=min(|x-y|,T), bounded-continuous convergence therefore gives

liminf_n (2/n^2) sum_{i<j}|x_i-x_j| >= E h_T(X,Y).

Increasing T proves

liminf_n n^(-2) sum_{i<j}|x_i-x_j| >= pi/4.

This is a lower-semicontinuity argument. It needs neither convergence of unbounded first moments nor a bound on the largest finite-cloud ratio. Large outliers can only help the lower bound. The diagonal terms vanish exactly, and the ordered double sum gives exactly the factor two.

## 7. Sorting and the exterior-unitary transformation

Sort all n augmented real rows in nondecreasing x_i. The product F and its maxima do not change. The ordered Gram matrix and its q-permanent may change; that is a permitted part of constructing the example, not an invariance assumption.

Choose a complex unitary matrix U whose first two columns are u and w. Under z=Uy the coefficient rows become v_i U. These transformed rows are used only to compute the polynomial norm/coordinate: the constructed matrix is still the real Gram matrix, and (VU)(VU)^*=VV^T.

For exterior coordinates, direct expansion gives

S'_ab(y)=sum_{c<d} det U[{c,d},{a,b}] S_cd(Uy).

In row-vector notation this is S'(y)=S(Uy)(Lambda^2 U). Since Lambda^2 U is unitary, |S'(e1)|_wedge=|S(u)|_wedge. This proves the norm invariance rather than assuming that ordinary vector-coordinate transformations also apply to wedge coordinates. The column-vector transpose version gives the same norm.

The first wedge coordinate now satisfies

S'_12(e1)/F(u)=sum_{i<j}(z_j-z_i).

Its real part is sum_{i<j}|x_j-x_i|, since the rows were sorted. Hence

g(u)=|S(u)|_wedge^2/|F(u)|^2
>= [sum_{i<j}|x_i-x_j|]^2,

and

liminf_m g(u_m)/(m+4)^4 >= pi^2/16 > 1/2.

The same fixed ordered real rows give S(conjugate(u))=conjugate(S(u)) and F(conjugate(u))=conjugate(F(u)). Thus the g-values at the two peaks agree. There is no need, and it would be wrong, to resort the rows separately for the conjugate peak.

## 8. Concentration, unequal peak weights, and zeros of F

Now choose and fix one finite augmented ordered base with g(u)>n^4/2. All subsequent limits use this fixed F, S, n, and pair of maxima.

Let M=max|F|>0 and let their common g-value be g0. The quotient g is continuous on {F != 0}, in particular in neighborhoods of both maxima. Given eta>0 choose small neighborhoods of the two maxima on which |g-g0|<eta. On the compact complement, |F|<=a<M; enlarge a slightly within (0,M) if necessary. Choose a<b<M. A positive-measure neighborhood of a maximum has |F|>=b, giving

D_L:=integral |F|^(2L) dmu >= c b^(2L), with c>0.

The polynomial S is bounded on the compact unit sphere. Consequently the contribution to the numerator from the complement is at most C a^(2L-2), whose ratio to D_L tends to zero. The corresponding denominator mass also tends to zero. On the two neighborhoods the numerator equals |F|^(2L)g and differs from g0 times that denominator mass by at most eta times the mass.

Therefore

[integral |F|^(2L-2)|S|_wedge^2 dmu]/D_L -> g0.

Unknown relative weights of the two peaks cause no problem because g0 is the same at both. No nondegenerate Hessian or exact Laplace expansion is invoked. Singularities of g at other zeros of F were never bounded or integrated on their own; the original numerator was bounded directly. This explicitly resolves the other most plausible analytic objection.

It follows that R_L -> 2g0/n^4>1. A sufficiently large finite integer L therefore gives P'_1(A_L)<0 through the exact endpoint identity.

## 9. Quantifier audit and rational positive-definite conclusion

The finite choices, in their required order, are:

1. Fix a deterministic equidistributed real sphere sequence. For every m choose any maximizing point, its real canonical coordinates, and (eventually) its four selector rows.
2. Fix a margin eta satisfying 0<eta<pi^2/16-1/2. The liminf estimate supplies M0 such that every sufficiently large m has g(u_m)/(m+4)^4>1/2. Also require t_m<3/4. Choose one such finite m, append the rows, sort, and freeze this base completely.
3. With this one fixed base, take L -> infinity. Choose and freeze one finite L with the Fischer ratio R_L>1. There is no simultaneous limit in m and L.
4. Approximate the finitely many resulting real row entries sufficiently closely by rational entries. The derivative at 1 is polynomial in those entries, so its strict negative sign persists in an open neighborhood. Choose the approximation in that neighborhood and keep every row nonzero. Unit length, the two-peak structure, and sorted-ratio inequalities need not survive this approximation: all were used before obtaining the strict derivative inequality.
5. The rational Gram matrix A has rank at most four and positive diagonal. Since N>4, it cannot be diagonal; a positive diagonal N-by-N matrix has rank N. Choose a sufficiently small positive rational epsilon such that B=A+epsilon I still has P'_1(B)<0. Then B is rational, real symmetric, positive definite, and non-diagonal.
6. The polynomial q -> P'_q(B) is continuous. There is h>0 with derivative negative throughout (1-h,1]. Shrink h below 1, choose rational q0<q1 in (1-h,1), and integrate the negative derivative. This yields P_q0(B)>P_q1(B). One could take q0=1-2/k and q1=1-1/k for sufficiently large integer k.

Each existential choice is finite and uses a strict open inequality. Later perturbations do not require any limiting construction to remain valid. The final failure lies strictly inside (0,1), and thus inside the original interval [-1,1].

## 10. Independent exact algebra checks

I wrote a separate standard-library verifier rather than rerunning or editing the first referee's script:

- `check_independent_algebra.py`
- `check_independent_algebra.log`

Actual results:

- 90 exact endpoint and Fischer tests, with r=1,...,5 and n=2,...,7;
- 12 exact polynomial contiguous-repetition and CP factorial-ratio tests;
- 6 exact rational peak-selector stationary-point tests, including t=1/2 and t close to 3/4.

The endpoint tests enumerate the defining permutations and ordinary inversion counts directly, and independently expand multivariate coefficient polynomials for the Fischer side. No floating-point tolerance is used in assertions. These finite tests corroborate the identities but do not replace their proofs, establish any of the limiting lemmas, produce a finite numerical real counterexample, or supply a dimension bound.

## 11. Independent literature check and possible name collisions

An independent source check was performed specifically for the real restriction of this q-permanent conjecture. The bounded public search, as of 2026-10-08, found no prior general real-symmetric proof or counterexample. This is not an exhaustive priority certificate.

Relevant primary sources:

- R. B. Bapat and A. K. Lal, *Inequalities for the q-permanent*, Linear Algebra and its Applications 197–198 (1994), 397–409. The publisher abstract specifies the inversion-weighted definition and conjectures strict increase on [-1,1] for non-diagonal positive-definite matrices. https://doi.org/10.1016/0024-3795(94)90497-9
- Lon Mitchell, *A note on Bapat's q-permanent conjecture*, Operators and Matrices 14(4) (2020), 915–919. The paper explicitly states the Hermitian positive-definite conjecture and the related nontrivial PSD formulation, proves rank-one and 3-by-3 cases and reductions, and does not solve the entire real restriction. https://files.ele-math.com/articles/oam-14-56.pdf ; https://doi.org/10.7153/oam-2020-14-56
- Eduardo Marques de Sa, *Noncrossing partitions, noncrossing graphs, and q-permanental equations*, Linear Algebra and its Applications 541 (2018), 36–53. The author's preprint (with title ending *formulas*) treats particular noncrossing graph classes, including a real, positive-definite, entrywise-nonnegative even-cycle class. Those additional hypotheses are not a general real-symmetric resolution. https://www.mat.uc.pt/preprints/ps/p1722.pdf ; https://doi.org/10.1016/j.laa.2017.11.024
- Carlos M. da Fonseca, *The mu-permanent revisited*, submitted to arXiv 2018-04-06; Linear and Multilinear Algebra 67(8) (2019), 1713–1714. This retains the monotonicity conjecture and corrects the earlier tree-graph claims to account for vertex labeling. https://arxiv.org/abs/1804.02231 ; https://doi.org/10.1080/03081087.2018.1466860

Two apparent counterexample collisions were excluded:

- de Sa's *Letter to the editor* supplies real counterexamples to formulas used in an earlier tree-graph paper, not to Bapat's monotonicity conjecture itself. https://www.mat.uc.pt/preprints/ps/p1519.pdf ; https://doi.org/10.1080/03081087.2018.1466861
- The 2026 title *The Bapat–Sunder eigenvalue conjecture fails over the reals* concerns a permanental-adjoint/eigenvalue conjecture. It is not the inversion-weighted q-permanent monotonicity problem, and its title cannot establish or preempt the theorem here.

The theorem here concerns quadratic-form positive definiteness; it does not assert entrywise positivity or entrywise nonnegativity. Recommended priority wording remains cautious: the sources checked do not supply a general resolution of the real restriction. Avoid an unqualified “first-ever” claim without a broader priority review.

## 12. Minimal wording changes recommended

1. At the target, explicitly define P_q using the ordinary inversion count and the fixed index order.
2. In Section 1 replace “For real unit rows” with “For arbitrary real rows”; note that the later equidistributed cloud is unit-normalized. This makes the final rational perturbation visibly compatible with the finite algebra.
3. In Section 2 replace “the continuous quotient g” with “the quotient g, continuous on the set where F is nonzero, evaluated on unit representatives.” Keep the existing zero-set estimate.
4. In Section 3 explicitly state nu_m tensor delta_{u_m} -> sigma tensor delta_u along a convergent subsequence, and define the bounded continuous truncation as log max(|v dot z|,exp(-K)). The existing Portmanteau statement is valid under this interpretation; these two sentences make the moving point unambiguous.
5. In the conclusion explicitly retain that only the intermediate PSD matrix has rank at most four, and that no explicit N, rational matrix entries, epsilon, or q witnesses have been computed.

None of these changes inserts a missing substantive hypothesis. The delicate steps all admit the complete arguments above. The proof passes within its stated finite-existence scope.
