# Technical audit of the complete Crouzeix deficit argument

Date: 7 October 2026. This public technical report is adapted from the independent AI-assisted audit of the frozen original Crouzeix argument. The audited original research.tex has SHA-256 b3f0de0bc1009dd6d6905bcc18c94bbe6e1a1a61db2502ae4b5d9ff5162355a2. The report below preserves the mathematical verification needed to assess the argument.

## Verdict and scope

Full mathematical PASS under the stated injective exterior-collar and strict numerical-range-enclosure hypotheses. No core mathematical correction was required. The intrinsic strict bound, exact deficit, necessary near-equality conditions, Hilbert-space geometric form and perturbation/disk specializations follow from the written proof. The complete-two outer-limit implication is explicit and attributed to the pinned OpenAI direct manuscript, which already states complete two. The audit is neither proof-assistant formalization nor human peer review.

The standalone note preserves the audited core proof, corrects the reduced-density wording, includes the attributed outer construction, and reproduces the auditor's classical-input disk deduction. A separate frozen-copy review covers the public presentation and these additions.

## Exact finite checks

The original rational checker and the separately written complex rational checker import only the Python standard library. Both ordinary and optimized executions agree. The original checker tests 100 generic rational Laurent block cases, 255 actual nilpotent singular pairs, 1,020 perturbation cases and two boundary/zero cases. Generic X,Y cases do not establish arbitrary singular-vector dual slacks. The independent checker tests 20 complex nilpotent density cases, 60 actual entangled complex singular pairs, 120 separately ordered products, and 36 ellipse coefficient cases. Finite tests support the algebra and examples; the proof of analytic and universal claims is the written argument below.

## 2. Analytic Faber coefficient estimate: PASS

The critical statement is the unweighted coefficient estimate in the original manuscript's exterior-coefficient lemma.

Write h(lambda)=c lambda+g(1/lambda), u=1/lambda, v=1/zeta. The reciprocal divided difference is

U(u,v)=c-uv (g(u)-g(v))/(u-v).

It extends holomorphically to the whole bidisk |u|,|v|<1/r0. Off the axes and diagonal, U cannot vanish because h is injective. On the diagonal it is h'(lambda), which is nonzero for an injective holomorphic map. On either axis it is c, which is nonzero. Therefore

s=-u (partial_u U)/U

is holomorphic and vanishes on each reciprocal axis. Its Taylor series contains only u^k v^j, k,j>=1. Cauchy estimates on a smaller reciprocal bidisk yield geometric coefficient decay, so all boundary Fourier expansions and integrations are legitimate. Comparing the expansion in lambda at infinity gives

b_k(h(zeta))=zeta^k+sum_{j>=1} s_{kj} zeta^{-j}.

No constant or other positive-frequency terms are omitted.

The exterior coordinate has positively oriented tangent i q(lambda), so q(lambda) is an outward normal. For distinct boundary points,

Re(q(lambda)/(h(lambda)-h(zeta)))
= Re(conj(q(lambda)) (h(lambda)-h(zeta))) / |h(lambda)-h(zeta)|^2 >=0

by convexity. Together with 2 Re(lambda/(lambda-zeta))=1, this gives the nonnegative continuous kernel K0=1+s+conj(s). The removable diagonal is legitimate; its s-value is lambda h''(lambda)/(2h'(lambda)), and continuity preserves the sign.

Each nonconstant Fourier term has nonzero frequency in both variables. Consequently both angular marginals of K0 are 1. Jensen with the first marginal, followed by integration with the second, proves contraction on every Hilbert-valued L2 space. Symmetry of K0, positive-semidefiniteness as an integral operator, and a scalar commutation lemma are unnecessary.

For u(lambda)=sum_{k>=1} C_k lambda^k, only s contributes to the integral. Thus Tu is exactly the negative Fourier part of G composed with h. Orthogonality of constant, positive, and negative Fourier modes yields

integral ||G(h)||_HS^2
= ||C0||_HS^2+sum_{k>=1}||Ck||_HS^2
  +sum_{j>=1}||sum_k s_kj Ck||_HS^2.

The final sum is at most sum_{k>=1}||Ck||_HS^2, proving both bounds with their exact constants.

## 3. Resolvent positivity and collar: PASS

Every eigenvalue lies in W(A). The exterior mapping property and compact spectral separation give a smaller collar on which R_A is holomorphic, including infinity with value I. Coefficient substitution at sufficiently large lambda is ordinary resolvent expansion; analytic continuation and Cauchy estimates give the stated absolute uniform convergence. Therefore the mean of R_A is I and the mean of H_A is 2I.

For B=h(lambda)I-A, direct multiplication gives

B* H_A B=conj(q) B+q B*.

The quadratic form on a unit vector is twice the supporting-line margin for its numerical-range value. Compact strict enclosure makes the uniform margin b positive. Congruence gives

H_A >= 2b (B^{-1})* B^{-1} >= (2b/||B||^2) I >= (2b/D^2) I.

This proves mu>0. Integrating H_A>=mu I gives mu<=2. No Crouzeix bound is used to establish positivity or convergence.

The theorem treats the injective exterior collar as an explicit assumption. Its claimed availability for regular real-analytic Jordan boundaries is consistent with classical boundary reflection: local holomorphic continuation has nonzero derivative, and compactness plus boundary injectivity yields a uniform injective collar.

## 4. Ordered products and coefficient duality: PASS

The tensor-basis identity is the entrywise bilinear pairing

y*G[A]x=sum_{k,i,j} (Y* b_k(A) X)_{ij} (C_k)_{ij}.

There is no conjugation in this bilinear expression. Cauchy–Schwarz supplies its bound. Taking G=F proves a>0.

Polynomial evaluation is an algebra homomorphism in the actual matrix-coefficient order. The two singular equations therefore give two different identities:

y*(FG)[A]x=gamma x*G[A]x;
y*(GF)[A]x=gamma y*G[A]y.

Both are used separately. F and G are never assumed to commute. Applying the cross-functional bound to the full Faber expansion of each product, the lower coefficient estimate, the appropriate left/right Hilbert–Schmidt multiplier inequality, and the upper coefficient estimate for G gives the two diagonal-functional bounds.

The weighted dual tests are C0=conj(P0), Ck=conj(Pk)/2 for k>=1, with entrywise conjugation. Their paired value and squared test norm are both

d_N=||P0||_HS^2+(1/2)sum_{1<=k<=N}||Pk||_HS^2.

Thus d_N <= (a/gamma) sqrt(d_N). The resulting reciprocal weights are correct. Finite tests and monotone convergence avoid a density or attainment assumption in the coefficient duality. The Q argument has its own ordered test.

## 5. Exact deficit and reduced-density cancellation: PASS

Parseval gives

U_P=4||P0||_HS^2+2 sum_{k>=1}||Pk||_HS^2 <=4a^2/gamma^2,

and the analogous Q inequality. Hence D_P,D_Q are nonnegative.

Because L0*=M0, the off-diagonal constant Fourier coefficient is 2M0. Its remaining positive and negative Fourier coefficients have disjoint supports. Therefore

V=a^2+3t+sum_{k>=1}||Lk||_HS^2.

For Delta=[X Y]* H_A [X Y] and J=diag(I,-I), Delta and J Delta J are positive, so Tr(Delta J Delta J)>=0. The diagonal/off-diagonal Hilbert–Schmidt expansion is exact. In particular E>=0. Substitution gives the displayed identity

2a^2(4/gamma^2-1)
=D_P+D_Q+E+6t+2 sum_{k>=1}||Lk||_HS^2.

The rank-free quantitative step is valid for mixed reduced densities. Set rho_X=XX*, rho_Y=YY*, D0=rho_X-rho_Y. Cyclic trace gives

Tr(Delta J Delta J)=Tr(H_A D0 H_A D0)
=||H_A^{1/2} D0 H_A^{1/2}||_HS^2.

Diagonalizing H_A multiplies each squared D0 entry by a product of two eigenvalues, each at least mu. Consequently E>=mu^2||D0||_HS^2. Moreover

||D0||_HS^2=p+q1-2t,   t=Tr(rho_X rho_Y)>=0.

With c=min(mu^2,3), one has 6-2c>=0, so

E+6t >= c(p+q1-2t)+6t >= c(p+q1) >=2c sqrt(p q1).

The energy identity and Schatten ideal inequality give

a^2=integral Tr(rho_Y R_A rho_X R_A*)
<=M^2 ||rho_X||_HS ||rho_Y||_HS
=M^2 sqrt(p q1).

Both reduced densities have trace 1 and positive purity. There is no division by a potentially zero rank factor, and the same purity product cancels exactly. Combining these statements proves the claimed intrinsic factor 2/sqrt(1+c/M^2).

The near-equality corollary follows by retaining individual nonnegative terms. It establishes necessary conditions only; no stability-to-model or extremizer classification is claimed.

The original phrase “pure densities” has been corrected to “reduced densities” in this standalone note. They are generally mixed, while their trace-one and positive-purity properties used in the proof are correct.

## 6. Geometric, Hilbert-space, and perturbation forms: PASS

The numerical-range resolvent estimate gives M<=Q/d, and the congruence gives mu>=2b/D^2. The map x -> min(x^2,3) is increasing for x>=0, so the substitutions have the correct inequality directions.

For arbitrary Hilbert spaces, the finite-dimensional compression E contains A^j x_i for all j up to the polynomial degree. Induction shows B^j x_i=A^j x_i through that degree, even though E need not be A-invariant. Thus F[B]x=F[A]x. W(B) is contained in K, and ||hI_E-B|| is at most ||hI-A||. The same geometric constants work for every compression, so taking the supremum over x proves the bound. This also covers nonseparable spaces and avoids infinite-dimensional singular-vector attainment.

For ||E1||<=e, numerical-range values move by at most e. The separation, margin, and resolvent denominator estimates become d-e, b-Qe, and D+e. The strict hypotheses ensure positivity and enclosure, and yield the stated eta_e. The disk specialization uses q=1, d,b>=1-r, and ||A||<=2r; all substitutions are conservative but correct.

## 7. What outer approximation actually implies

Let K be the compact convex numerical range of a finite matrix, or the closure of the numerical range of a bounded Hilbert-space operator. There exist regular real-analytic convex domains Omega_j strictly containing K and converging to K in Hausdorff distance, including when K is a segment or singleton. One independent construction is to smooth the support function by the circle heat kernel and add a positive constant exceeding its uniform approximation error. Heat smoothing preserves the nonnegative curvature distribution; the added constant makes it strictly positive. The resulting support functions define regular analytic strictly convex boundaries.

For a fixed finite matrix-valued polynomial F, continuity gives

max_{closure Omega_j}||F|| -> max_K||F||.

Each audited strict-domain theorem has constant at most 2. Consequently

||F[A]||<=2 max_K||F||,

uniformly in the coefficient dimension, with no need for a positive limiting eta. This is the full complete polynomial constant-two statement. Standard polynomial approximation on convex compact sets extends it to matrix-valued rational functions with poles off K and functions holomorphic near K.

Thus the candidate does carry the full complete-two implication. It does not improve the optimal universal constant below 2. The nilpotent matrix [[0,2],[0,0]] with F(z)=z establishes universal sharpness. In that example the strict-domain gap vanishes as enclosing disks shrink.

## Literature and limits

The full complete-two architecture and outer approximation are attributed to the pinned public OpenAI direct manuscript. Exact pins and two independently matched Crouzeix source hashes are in PROVENANCE.json. Neither a public manuscript nor an AI-assisted audit establishes publication acceptance.

The bounded comparison checked older complete disk/ellipse estimates and the specified weighted-shift strictness result. The stronger disk formula in the standalone note is an elementary deduction from classical similarity input; no claim is made that the formula was located in a publication. It is not a revision of the general intrinsic theorem. A serious priority determination for the exact deficit or mu/M certificate would require a broader comparison and has not been completed.

The near-equality corollary gives necessary conditions only. It does not classify extremizers or imply closeness to a nilpotent model. No positive gap below two is required to survive the outer limit, and the nilpotent example establishes sharpness of the universal constant.
