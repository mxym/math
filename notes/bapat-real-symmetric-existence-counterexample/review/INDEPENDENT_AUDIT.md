# Independent audit of the proposed real-symmetric Bapat extension

Audit date: 2026-10-08 (UTC).

Audited input: `PROOF_DRAFT.md` in the parent directory, SHA-256
`53ff4b0a29fc1e93553384bd30cb2ec184b4f12ca4a2b1a022cc13c92183a1ab`.

## Verdict

**PASS as a finite-existence proof.** I found no mathematical gap in the six-step argument. In particular, the newly introduced real four-dimensional construction does establish the following statement, independently of any numerical complex example:

> There are a finite integer N, a non-diagonal real symmetric positive-definite matrix B with rational entries, and rational numbers 0 < q0 < q1 < 1 such that P_q0(B) > P_q1(B), where the exponent in P_q is the ordinary inversion number of the permutation.

The intermediate endpoint counterexample is a real Gram matrix of rank at most four. Adding a positive diagonal perturbation gives full rank, so **do not describe the positive-definite final B itself as rank four**. No dimension bound, explicit rational witness, or formal proof-assistant certificate is supplied by this argument. The exact small-case checks below corroborate finite algebraic identities; they are not substitutes for the analytic proof.

The argument is not a realification of the complex example. Its load-bearing new ingredients are balancing maxima of products of real linear forms, a real four-factor selector, and a ratio of two independent complex Gaussian coordinate pairs.

### Minimal revisions before incorporating this into a manuscript

1. Distinguish the polynomial Fischer norm `||.||_F` from the pointwise Euclidean norm of the vector of wedge coordinates, `|S(z)|_wedge`. The draft uses `||S||` for the former and `||S(u)||` for the latter; its intended formulas are correct, but the distinction should be stated.
2. State the polynomial identities for arbitrary real coefficient rows, not only unit rows. Unit normalization is needed for the equidistribution argument, but rational approximation need not retain unit length. The same identities hold without normalization.
3. Include the moving-argument truncation and the exterior-power unitary transformation explicitly. Full versions appear below.
4. State that g is continuous **where F is nonzero**, rather than globally continuous on CP^3. The subsequent zero-set argument in the draft already handles this correctly.
5. Make the finite choice order explicit: choose and fix m and the selected/ordered base; then choose and fix L; then approximate the resulting finitely many real rows by rational rows; then choose rational epsilon; finally choose rational q0,q1. This is already the logical order of the draft.

These are precision/editorial improvements, not repairs of a failed lemma. There is no extra unproved hypothesis on an equidistributed cloud, the Hessian at a maximum, moment convergence, or a generic position condition.

## 1. General-rank endpoint identity: PASS

Let v_i be real rows in R^r, with A_ij = v_i dot v_j. Define ell_i(z)=v_i dot z, F=product_i ell_i, and

S_ab = sum_{i<j} (v_ia v_jb-v_ib v_ja) product_{k outside {i,j}} ell_k,

for a<b. Use the Fischer inner product linear in its first argument. The product identity is

< product_{i in I} ell_i, product_{j in J} ell_j >_F = per A[I,J].

This follows by matching monomial coefficients, or by the Gaussian moment expansion. It applies with ordered increasing complementary lists and introduces no determinant sign on those complements.

Independently mark an inversion in the defining permutation sum. For row indices i<j and image indices k<l, the marked inverted assignments are sigma(i)=l and sigma(j)=k. Therefore

P'_1(A) = sum_{i<j,k<l} A_il A_jk per A[{i,j}^c,{k,l}^c].

For each fixed i<j, expanding the permanent by those two rows gives

per A = sum_{k<l} (A_ik A_jl+A_il A_jk) per A[{i,j}^c,{k,l}^c].

Subtracting the marked-inversion sum twice from the sum of these expansions gives

binom(n,2) per A - 2P'_1(A)
= sum_{i<j,k<l} (A_ik A_jl-A_il A_jk) per A[{i,j}^c,{k,l}^c].

Cauchy–Binet gives exactly

A_ik A_jl-A_il A_jk
= sum_{a<b} (v_ia v_jb-v_ib v_ja)(v_ka v_lb-v_kb v_la).

Combining this with the product inner-product identity yields

2P'_1(A) = binom(n,2)||F||_F^2 - sum_{a<b}||S_ab||_F^2.

There is no factor of two missing in the wedge norm: only a<b is summed. Real row scaling causes no difficulty; both F and every S_ab are multiplied by the product of all row scaling factors.

## 2. Contiguous repetition and CP normalization: PASS

For L consecutive copies of each row, every same-block wedge vanishes. Every pair of different blocks contributes L^2 identical wedge terms. Consequently

F_L = F^L,
S_L = L^2 F^(L-1) S.

Contiguity is important. The statement is not a claim that an arbitrary rearrangement of all repeated rows gives the same S_L.

For normalized invariant measure on CP^(r-1), represented by unit complex vectors, the monomial formula is

integral |z^alpha|^2 dmu = alpha! (r-1)! / (d+r-1)!,  |alpha|=d.

Mixed monomials of different multi-index integrate to zero under coordinate phases. Hence

||T||_F^2 = (d+r-1)!/(r-1)! integral |T|^2 dmu.

The numerator vector has degree N-2 and the denominator polynomial has degree N, where N=nL. The factorial ratio is therefore

(N+r-3)!/(N+r-1)! = 1/[(N+r-1)(N+r-2)].

The draft's exact expression follows:

R_L = ||S_L||_F^2 / [binom(N,2)||F_L||_F^2]
= L^4/[binom(N,2)(N+r-1)(N+r-2)]
  * integral |F|^(2L-2)|S|_wedge^2 dmu / integral |F|^(2L) dmu.

For a fixed base of size n and a fixed r, the prefactor tends to 2/n^4. The fact that r=4 rather than r=2 changes finite factorials, but does not change that limit.

## 3. Maxima of real clouds become balanced: PASS

Let nu_m be the empirical probability measure of the unit real rows, with nu_m weakly converging to uniform sigma on S^3. Finite products F_m are nonzero polynomials, so their maximum modulus on the unit complex sphere is positive. No factor vanishes at a maximum.

### Canonical form

For a unit complex vector u=x+iy, a scalar phase can make its real and imaginary parts orthogonal. Multiplication by i can interchange their lengths. A real orthogonal change of coordinates then gives

u = sqrt(t)e1 + i sqrt(1-t)e2,  1/2 <= t <= 1.

The parameter is intrinsic and continuous:

t = (1+|u^T u|)/2.

Thus balanced means t=1/2, equivalently u^T u=0. These operations preserve realness of all coefficient rows.

### Population potential

Writing a uniform sphere vector as G/||G|| with G a standard real Gaussian vector gives

U(t) = (1/2) E log(tG1^2+(1-t)G2^2) - E log||G||.

Every term is integrable, including t=0 and t=1. The first expectation is strictly concave in t: for distinct t-values, pointwise strictness fails only where G1^2=G2^2, a probability-zero set. Symmetry under t <-> 1-t therefore forces a unique maximum at 1/2.

As an optional independent check, one can explicitly compute

U(t) = -1/2 + log[(sqrt(t)+sqrt(1-t))/2].

Indeed v1^2+v2^2 is uniform on [0,1] for a uniform point of S^3, and the angle in the first coordinate plane is uniform. This expression also gives U_bal = -(1+log 2)/2 and its unique maximizing parameter 1/2.

### Finite-cloud lower bound

For a fixed balanced unit vector u_bal, averaging log|v_i dot R u_bal| over normalized Haar measure of O(4) gives U_bal for every unit real row v_i. Each logarithm is integrable. Summing the finitely many integrals implies

max_z (1/m)log|F_m(z)| >= U_bal.

No convergence or uniform integrability of finite-cloud logarithmic potentials is used here.

### Moving-point upper bound

Suppose along a subsequence u_m converges on the unit sphere to u. For every K>0, put

phi_K(v,z) = max(log|v dot z|,-K).

This is a bounded continuous function on S^3 times the complex unit sphere, with the natural value -K at a zero. Compactness makes phi_K(v,u_m) converge uniformly in v to phi_K(v,u). Thus weak convergence of nu_m gives

limsup_m integral log|v dot u_m| dnu_m(v)
<= integral phi_K(v,u) dsigma(v).

Let K increase to infinity. Integrability of the population logarithm gives the upper bound U(u). Together with the finite-cloud lower bound, U(u)>=U_bal. Consequently every cluster point is balanced. By compactness and continuity of t, t_m tends to 1/2.

This is a valid upper Portmanteau argument. It does not silently exchange an unbounded integral with weak convergence.

## 4. Orthogonal changes depending on m: PASS

Let R_m be any sequence of real orthogonal transformations used in the canonical form. Every subsequence has a further subsequence with R_m converging to an orthogonal R. For any continuous test function f on S^3, f(R_m v) converges uniformly in v to f(Rv). Hence

integral f(R_m v) dnu_m(v) -> integral f(Rv) dsigma(v) = integral f(v) dsigma(v).

Every subsequence has the same limiting measure sigma, so the full transformed empirical sequence converges to sigma. There is no need for R_m itself to converge or for a measurable/equivariant choice of maximizer.

## 5. Four real factors select exactly two projective peaks: PASS

For 1/2 <= t < 3/4, let

c=(2t-1)/[t(3-4t)], a^2=1+c, b^2=1,
H(z)=z1 z2 (a z1+b z2)(a z1-b z2).

The four rows are real and nonzero. They have nonzero evaluations at u=sqrt(t)e1+i sqrt(1-t)e2.

If rho^2=|z1|^2+|z2|^2<1 and H(z) is nonzero, normalizing the first two coordinates increases |H| by the factor rho^(-4)>1. Thus every global maximizer is supported on the first two coordinates.

With |z1|^2=s and |z2|^2=1-s,

|H(z)| = sqrt(s(1-s)) |a^2 z1^2-b^2 z2^2|
<= sqrt(s(1-s)) [a^2s+b^2(1-s)]
= f_c(s).

The maximum is positive and occurs in 0<s<1. At such a point, equality in the triangle inequality requires z1^2 and z2^2 to have opposite arguments. This means relative phase +pi/2 or -pi/2, modulo a common scalar phase.

The derivative of f_c has the sign of

p_c(s)=1-2s+c(3s-4s^2).

For c=0 it changes sign once at s=1/2. For c>0, p_c has one negative and one positive root (their product is -1/(4c)); p_c(0)=1 and p_c(1)=-1-c. Its unique positive root is therefore in (0,1), with the required positive-then-negative derivative signs. Substitution of the stated c gives p_c(t)=0. Hence the only projective maxima are

[sqrt(t)e1+i sqrt(1-t)e2],
[sqrt(t)e1-i sqrt(1-t)e2].

These are distinct because 0<t<1. Normalizing each real row multiplies H by one fixed positive factor and does not affect its maximizer set.

Since F_m has real coefficients, u and conjugate(u) are both original maxima. Since both also maximize |H|, the product achieves the product of the two separate maximum moduli. Equality in that bound requires simultaneous equality for the two factors. Thus F_m H has **exactly** the stated pair of projective maxima, even if F_m previously had a continuum of maxima.

## 6. Ratio law and the Gini constant: PASS

Choose w=(e3+i e4)/sqrt(2). It is a Hermitian unit vector perpendicular to u. For each original row,

z_i=(v_i dot w)/(v_i dot u), x_i=Re z_i.

All denominators are nonzero. The transformed empirical row measure tends to sigma and t_m tends to 1/2. The mapping is continuous except where its limiting denominator v1+i v2 vanishes. That subset has sigma-measure zero. Apply the almost-everywhere-continuous mapping theorem to the joint empirical measure of (v,t_m). It yields the weak ratio law

Z=(G3+iG4)/(G1+iG2).

The factors 1/sqrt(2) in numerator and limiting denominator cancel. The two complex Gaussians are independent because their underlying four real Gaussian coordinates are independent. Dividing G by its real length to obtain the uniform sphere does not change the ratio.

The quotient density is 1/[pi(1+|z|^2)^2]. For example, the change of variables (z,d)->(zd,d) has real Jacobian |d|^2; integrating the product of the two circular Gaussian densities gives exactly this constant. Its real marginal is

p(x)=1/[2(1+x^2)^(3/2)],
J(x)=[1+x/sqrt(1+x^2)]/2.

For independent copies X,Y, Tonelli applied to the indicator representation of |X-Y| gives

E|X-Y| = 2 integral J(x)(1-J(x)) dx
= (1/2) integral 1/(1+x^2) dx = pi/2.

The four new rows have numerator zero and nonzero denominator, so their ratios are zero. Their total relative mass tends to zero. They do not change the limiting empirical distribution.

### The unbounded moment step is justified

Let eta_n be the empirical distribution of all n=m+4 real ratios. For each T>0, h_T(x,y)=min(|x-y|,T) is bounded and continuous. Weak convergence of eta_n implies weak convergence of eta_n tensor eta_n, giving convergence of the integrals of h_T. Since

(2/n^2) sum_{i<j}|x_i-x_j| = integral |x-y| d(eta_n tensor eta_n),

first taking liminf and then increasing T gives

liminf n^(-2) sum_{i<j}|x_i-x_j| >= pi/4.

Only a lower bound is required. Full convergence of these unbounded moments, a uniform bound on the largest ratio, and uniform integrability are unnecessary.

## 7. The ordering-to-wedge calculation: PASS

Order the entire augmented real row list by nondecreasing x_i. F and its maxima are unchanged. The ordered q-permanent is allowed to change: this order is part of constructing the counterexample.

Let U be a unitary matrix with first two columns u,w. Under the change of polynomial variables z=Uy, coefficient rows become v_i U. The original real Gram matrix is unchanged:

(VU)(VU)*=VV^T.

Write S' for the wedge-polynomial vector computed from these transformed rows. Direct minor expansion gives

S'_ab(y) = sum_{c<d} det U[{c,d},{a,b}] S_cd(Uy).

Thus S' is obtained from S composed with U by the transpose of the exterior-square matrix of U. That matrix, and its transpose, are unitary. Therefore

|S'(e1)|_wedge = |S(u)|_wedge.

In the (1,2) coordinate, after dividing by nonzero F(u),

S'_12(e1)/F(u)
= sum_{i<j} [(v_i dot u)(v_j dot w)-(v_i dot w)(v_j dot u)]
             /[(v_i dot u)(v_j dot u)]
= sum_{i<j}(z_j-z_i).

Its real part is sum_{i<j}|x_j-x_i|. A coordinate's absolute value is bounded by the full Euclidean norm, so

g(u):=|S(u)|_wedge^2/|F(u)|^2
>= [sum_{i<j}|x_j-x_i|]^2.

Consequently

liminf g(u_m)/n^4 >= pi^2/16 > 1/2.

The last inequality is strict, with pi^2/16 approximately 0.616850275. Thus some finite base satisfies the required strict score threshold. Its row order is now fixed.

All coefficient rows in that fixed order are real. Hence S(conjugate(u))=conjugate(S(u)) and F(conjugate(u))=conjugate(F(u)); g has the same value at both maxima. It is unnecessary to resort the rows for the conjugate point or to find a new projection there.

## 8. Two-peak concentration with zeros: PASS

Let M=max|F|>0 and let the two maximum points have common value g0. The function g is continuous in neighborhoods of those points, since F is nonzero there. Given a desired accuracy, choose neighborhoods on which |g-g0| is small.

On the complement, compactness and the exact two-peak property give |F|<=a<M; take a>0 if necessary. Choose b with a<b<M and a positive-measure neighborhood of a maximum where |F|>=b. Then

integral |F|^(2L) dmu >= c b^(2L), c>0.

Since the polynomial vector S is bounded on the unit sphere, the exterior numerator is bounded by C a^(2L-2). Its ratio to the denominator tends to zero exponentially. The exterior denominator contribution similarly tends to zero. Inside the chosen neighborhoods, g differs from g0 by an arbitrarily small amount. Therefore

integral |F|^(2L-2)|S|_wedge^2 dmu / integral |F|^(2L) dmu -> g0.

No assertion of nondegenerate Hessians, equal Laplace weights, or a finite-order stationary phase expansion is needed. In particular, unknown relative concentration weights of the two peaks do not matter because their g-values agree.

For the previously fixed base, R_L tends to 2g0/n^4>1. A finite integer L therefore has R_L>1, and the endpoint identity gives P'_1(A_L)<0.

## 9. Rational positive-definite lifting and interior parameters: PASS

There are finitely many rows after L is fixed. Their derivative expression is a polynomial in their real entries. Approximate all those entries sufficiently closely by rational numbers so that P'_1 stays negative and every row remains nonzero. The resulting rational Gram matrix A has rank at most four and strictly positive diagonal.

The number of rows N is greater than four. Such a matrix cannot be diagonal: a diagonal matrix with N positive diagonal entries has rank N, which would contradict rank A<=4.

For sufficiently small positive rational epsilon,

B=A+epsilon I

still has P'_1(B)<0, by polynomial continuity. It is real symmetric with rational entries, and for any nonzero real x,

x^T Bx = x^T Ax+epsilon||x||^2 >0.

It remains non-diagonal because the perturbation changes no off-diagonal entry.

The real polynomial q->P'_q(B) is strictly negative on some interval immediately to the left of 1. Take that interval within (0,1). Rational density supplies q0<q1 there, or one may take q0=1-2/k and q1=1-1/k for a sufficiently large integer k. Integration of the negative derivative gives P_q0(B)>P_q1(B).

The final q-values are genuinely inside the classical interval. This is not merely a failure at q>1, not just an endpoint derivative whose sign is compatible with monotonicity inside the interval, and not only a singular PSD example.

## 10. Independent exact algebra checks

Files accompanying this report:

- `check_exact_algebra.py`: standard-library-only Python verifier.
- `check_exact_algebra.log`: its actual output.

The verifier computes the defining permutation sum and inversion derivative directly and compares them with independently expanded multivariate polynomial Fischer norms. It checks 80 deterministic random integer examples across n=2,...,6 and r=2,...,5. It also verifies nine contiguous-repetition polynomial identities and the degree-two CP factorial quotient. All checks pass.

Run:

`python check_exact_algebra.py`

These checks contain no floating-point tolerances and require no package installation. They do not claim to produce a large finite real counterexample or verify the limiting selection of m and L computationally.

## 11. Scope and literature check

The target is correctly the ordinary inversion-number q-permanent. It is not the alpha-permanent, a cycle-counting deformation, or a different quantum permanent.

- Bapat and Lal, *Inequalities for the q-permanent* (1994), explicitly state strict monotonicity for non-diagonal positive-definite matrices on [-1,1]. [Publisher source](https://www.sciencedirect.com/science/article/pii/0024379594904979).
- Mitchell, *A note on Bapat's q-permanent conjecture* (2020), p.915, states the Hermitian positive-definite version and discusses the equivalent positive-semidefinite extension; the article establishes rank-one and order-three cases. [Primary PDF](https://files.ele-math.com/articles/oam-14-56.pdf).
- Da Fonseca's manuscript distinguishes the original interval conjecture from its proposed extension beyond that interval. [Primary manuscript](https://arxiv.org/abs/1804.02231).

The real-symmetric matrices here are a subclass of Hermitian matrices. “Positive definite” is a quadratic-form condition; the theorem does not assert an entrywise nonnegative counterexample.

Targeted searches on 2026-10-08 for the exact q-permanent monotonicity conjecture, real symmetric restrictions, counterexamples, and 2024–2026 updates found no separate current resolution of this exact real-restricted question. This is a bounded search result, not proof of priority or exhaustive novelty.

A potentially confusing recent item is Logan R. Chalmers, *The Bapat–Sunder eigenvalue conjecture fails over the reals* (September 2026), an author-uploaded preprint. Its stated real counterexample concerns the largest eigenvalue of the matrix [a_ij per A(i,j)], not q-permanent monotonicity. It does not by its stated theorem preempt or establish the target proved here. Its full argument was not audited as part of this task. [Author-uploaded preprint](https://www.researchgate.net/publication/414009185_The_Bapat-Sunder_eigenvalue_conjecture_fails_over_the_reals).

## Bottom line

The six-step draft survives an independent adversarial check. With the notation and explicit lemmas above, it gives a complete nonconstructive real-rational positive-definite counterexample existence theorem in the original q interval. The already audited explicit complex example remains a separate result and should not be delayed, relabeled as real, or used as a substitute for the newly audited four-dimensional reasoning.
