# The complete Gaussian approximation threshold for fixed-length Gaussian matrix products

**Scope.** This is a statistical theorem about independent real Gaussian matrices, motivated by Gaussian noise generation in a tensor-coordinate space. It does not model a concrete cryptosystem or its samples. [Li–Woodruff, Theorem 1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2021.35) study products of several Gaussian matrices, with inner widths at least max(p,q) and an equal-first/last-width hypothesis. They give the sufficient scale pq per factor and, at fixed length, an obstruction at scale sqrt(max(p,q)) min(p,q)^(3/2). Their lower bound uses the Schatten four-norm. Here the chain length is fixed, but its inner widths may be heterogeneous and need not have equal endpoints. The result gives the sharp pq threshold and the full limiting TV profile. The two-factor method extends by comparing a Wishart martingale to its additive approximation in the likelihood overlap, not by asserting that their full matrix laws are close.

## 1. Model and statement

Fix k>=1. Let G_1,...,G_(k+1) be independent real matrices with iid N(0,1) entries, of respective sizes

    p by d_1, d_1 by d_2, ..., d_(k-1) by d_k, d_k by q.

Set Y=G_1 ... G_(k+1)/sqrt(prod_i d_i). Let P denote its law and Q the iid standard real Gaussian law on p by q matrices. Reverse the chain and transpose if necessary so p<=q. Put

    a=sum_(i=1 to k) 1/d_i,   rho=pq a.

As p,q both tend to infinity, for every rho tending to gamma in [0,infinity],

    TV(P,Q) -> 2 Phi(gamma/4)-1,                           (1)

with value one for gamma=infinity. Here Phi is the normal CDF. There is no additional requirement on q/p or on ratios between the inner widths. In particular TV tends to zero if and only if all d_i/(pq) tend to infinity, and tends to one if any d_i/(pq) tends to zero. No theorem is asserted for a growing chain length.

If p is fixed and q tends to infinity, the effective ratio is lambda=q a. At finite positive limiting lambda, set D=p(p+1)/2, F_D the chi-square(D) CDF, and b=D(1+lambda) log(1+lambda)/lambda. Then the exact limit is

    F_D(b)-F_D(b/(1+lambda)),                               (2)

with limits zero and one when lambda tends to zero and infinity, respectively.

## 2. Covariance process and its additive approximation

Let W_i be independent Wishart sample covariance matrices G_i^0(G_i^0)^T/d_i, where G_i^0 has shape p by d_i and iid standard Gaussian entries. Put E_i=W_i-I. Conditional on the prefix of the matrix product, each new Gaussian column has covariance equal to the preceding prefix scatter. Thus one may represent the covariance of the q final columns by the independent-increment construction

    S_0=I,   S_i=S_(i-1)^(1/2) W_i S_(i-1)^(1/2),
    X=S_k-I,   U=sum_i E_i,   V=X-U.                       (3)

Conditionally on S_k, the q columns are independent N(0,S_k). This does not claim that S_k is the product of commuting matrices. If any d_i<p then P is supported on rank-deficient matrices and TV(P,Q)=1. For the bounded-rho part with p,q growing, all d_i are at least c pq for some fixed c>0, so assume d_i>=p.

We record bounds for this bounded-rho regime. Constants may depend on k and on the bound for rho, and are uniform in the separate d_i. The elementary Gaussian net bound gives

    Pr(||E_i||_op>K sqrt(p/d_i)) <= exp(-c_0 p),
    E ||E_i||_op^b <= C_b (p/d_i)^(b/2)                    (4)

for any fixed b>0 and large fixed K. Indeed, quadratic forms along a fixed unit vector are centered chi-square(d_i) ratios; their exponential tails followed by a 1/4-net of size at most 9^p give (4), with moments from tail integration. Let A be the simultaneous good event in (4). On A,

    ||X||_op+||U||_op <= C sqrt(p a),
    ||V||_op <= C p a.                                    (5)

These follow inductively from S_i-S_(i-1)=S_(i-1)^(1/2) E_i S_(i-1)^(1/2) and ||S^(1/2)-I||_op<=||S-I||_op. The first bound, as an L^b moment bound, holds without A: use ||S_i||_op<=prod_(j<=i)(1+||E_j||_op), insert it in the difference estimate, and apply (4) and Holder. These arguments also apply to each partial sum with a replaced by the corresponding partial sum of 1/d_i.

For a fixed symmetric test matrix B, E tr(B V)=0, and

    E [tr(B V)^2] <= C p a^2 ||B||_F^2.                   (6)

For this, write V as the sum of differences
D_i=S_(i-1)^(1/2) E_i S_(i-1)^(1/2)-E_i. These are martingale differences with respect to the independent W_i. Given the past, the variance of tr(B D_i) is

    (2/d_i) ||S_(i-1)^(1/2) B S_(i-1)^(1/2)-B||_F^2,

using the covariance of a centered real Wishart quadratic form. Its expectation is bounded by C p a_(i-1) ||B||_F^2/d_i by (4), where a_(i-1)=sum_(j<i)1/d_j. Sum the variances. The operator-norm moment estimates also give E||X||_F^2+E||U||_F^2=O(p^2 a) and fourth Frobenius moments O(p^4 a^2).

The covariance of U on the space of symmetric matrices is exactly 2a times the identity for the Frobenius inner product. Consequently

    E tr(U^2)=p(p+1)a,   E (tr U)^2=2pa,
    E sum_(i<j) U_ij^2=binom(p,2) a.                       (7)

Both tr(U^2) and sum_(i<j) U_ij^2 have variance O(p^2 a^2). For example Gaussian Poincare applied to tr(U^2), as a function of all G_i^0, uses gradient 4 U G_i^0/d_i in the i-th matrix. After summing its squared norm expectations, bound each by (16/d_i) E[||W_i||_op ||U||_F^2], and use the moments above. The offdiagonal version uses the orthogonal projector onto symmetric matrices with zero diagonal in place of U in the gradient, and obeys the same bound.

## 3. The likelihood overlap reaches the Gaussian benchmark

Assume p,q grow and rho tends to finite gamma. Condition on A in (3) to form P', so TV(P',P)<=Pr(A^c)=o(1). For one conditional covariance S=I+X, let L_S be the q-column likelihood relative to Q. For independent copies X,X' in the good events A,A', direct integration of the Gaussian likelihood gives

    E_Q L_S L_S' = det(I-X X')^(-q/2).                    (8)

Indeed S^(-1)+S'^(-1)-I is positive definite on the good events for large p,q, and its determinant times det(S)det(S') is det(I-XX'), by multiplication on the left by S and on the right by S'. On the good events ||XX'||_op=O(p a)=O(1/q), so the logarithm of (8) is

    Z + R,  Z=(q/2) tr(X X'),
    R=(q/4) tr((XX')^2) + O(p/q^2),                       (9)

uniformly, with R=O(1). We show that R tends to zero in probability and obtain the leading exponential expectation.

First, the second trace can use U,U' in place of X,X'. Each replaced factor contributes at most C p (p a)^(5/2) to the absolute trace difference on the good events, from one V and three factors with norm O(sqrt(p a)); after multiplying by q this tends to zero. For fixed U, the covariance of U' gives

    E_(U') tr(U U' U U') = a[tr(U^2)+(tr U)^2].

Its expectation times q is O(q p^2 a^2)=O(1/q). Gaussian Poincare conditionally on U gives

    Var_(U') tr(U U' U U') <= C p^2 a^2 ||U||_op^4.

Indeed the gradient in G_i^{0 prime} is 4 U U' U G_i^{0 prime}/d_i; use the same norm-moment bound as for (7). On A the variance after multiplying the trace by q is O(q^2 p^4 a^4)=o(1). Thus R tends to zero in probability on A,A'.

For the first trace define Z_U=(q/2) tr(U U'). Independence between the primed and unprimed chains and (6) give

    E[(Z-Z_U)^2] <= C q^2 p^3 a^3 = o(1).                 (10)

In detail use tr(XX'-UU')=tr(V X')+tr(U V'), apply (6) conditionally on X' or U, and use their O(p^2 a) second Frobenius moments. This is the step where using only two Frobenius norm bounds would be insufficient in square aspect ratios.

Conditional on U on A, independence of the summands of U' and the exact Wishart exponential formula imply, for every fixed real t,

    log E_(U') exp(t Z_U)
        = (t^2 q^2 a/4) tr(U^2)+o(1),                    (11)

uniformly on A. For the i-th summand the exact factor is
exp(-tq tr U/2) det(I-tq U/d_i)^(-d_i/2). Its logarithm cancels at degree one; the sum of remainders after degree two is at most
C_t q^3 (sum_i d_i^(-2)) ||U||_op tr(U^2)=o(1)
by (5). The main exponent is bounded on A, and (7) shows it converges in probability to t^2 gamma^2/4. Averaging (11) on A therefore tends to exp(t^2 gamma^2/4).

We make the exchange of exponential expectations explicit. For every fixed real t, E[exp(t Z) 1_A 1_A'] is bounded uniformly. To prove this, hold X fixed on A. In the primed process, use its martingale increments S_(i-1)'^(1/2) E_i' S_(i-1)'^(1/2) until the first bad step of (4), and set all *subsequent* increments to zero. The stopped sum agrees with X' on A'. Conditional on a still-good past, its i-th contribution to tZ uses the fixed symmetric matrix B_i=S_(i-1)'^(1/2) X S_(i-1)'^(1/2). Its operator norm is O(sqrt(p a)) and its squared Frobenius norm is O(p^2 a). The exact conditional Wishart mgf, with first-order cancellation, is bounded by exp(C_t q^2 p^2 a/d_i); it is one after stopping. Iterating conditional expectation yields exp(C_t (pq a)^2), a uniform bound. This argument uses the *unclipped* increment at the first bad step, for which the same mgf formula is valid from a still-good past; it never conditions an increment on future goodness.

By (11) with t=2, excluding A'^c changes the average of exp(Z_U) on A by o(1), by Cauchy–Schwarz. By (10) and the just-proved bounded second exponential moments, replacing exp(Z_U) by exp(Z) on A,A' changes the average by o(1): the difference tends to zero in probability and is uniformly integrable there. Finally R is bounded on those events and tends to zero in probability, so inserting exp(R) changes the average by o(1), again using the second exponential moment bound. Both clipping probabilities tend to one. Thus (8) and Fubini show for L'=dP'/dQ

    E_Q (L')^2 -> exp(gamma^2/4).                         (12)

In particular gamma=0 gives TV(P,Q) tending to zero. No assertion about the untrimmed mixture's second likelihood moment is needed.

## 4. Orthogonal rectangle statistic saturates (12)

Assume 0<gamma<infinity. Put N_p=binom(p,2), N_q=binom(q,2), N=N_p N_q. Define

    T(Y)=sum_(i<i',j<j') Y_ij Y_i'j Y_ij' Y_i'j'.

Under Q different rectangles are orthogonal products of four distinct Gaussian cells. Thus T/sqrt(N) has mean zero and variance one and belongs to the fourth Gaussian chaos. Its fourth moment tends to three: every contributing quadruple of rectangles has even cell multiplicities. The repeated-pair terms give 3N(N-1) up to relative O(1/(pq)) corrections for shared cells, and all-identical terms are O(N). Exactly three distinct rectangles cannot contribute. With four distinct rectangles, at most four rows and four columns occur, because every used row and column occurs at least twice. If both counts were four, a rectangle's two rows would force either an identical other rectangle or two other rectangles with the same column pair, contradicting the column counts. Hence the four-distinct contribution is O(p^3 q^4+p^4 q^3), negligible relative to N^2. The [Nualart–Peccati fourth moment theorem](https://arxiv.org/abs/math/0503598) gives T/sqrt(N) converging under Q to N(0,1).

For the conditional version, index a vector of upper offdiagonal entries by i<i'. Given S, let Z_j have entries Y_ij Y_i'j, with mean v consisting of S_ii', and put W_j=Z_j-v. Then

    T=N_q ||v||^2+(q-1) sum_j v^T W_j + sum_(j<j') W_j^T W_j'.  (13)

Now ||v||^2/(N_p a) tends to one in probability, by (7) and replacing X by U: on A the error in their squared offdiagonal norms is O(p(p a)^(3/2))=o(p^2 a) by (5). The first term in (13), divided by sqrt(N), therefore tends to gamma/2. The conditional covariance K of W_j has operator norm at most ||S||_op^2, by the Gaussian quadratic-form variance formula applied to the matrix with coefficients b_ii'/2 in both offdiagonal positions. Consequently the linear term has unconditional variance O(q^3 p^2 a), by the Frobenius moments from §2. On the scale sqrt(N) it tends to zero since q a=O(1/p).

For the remaining degenerate term, couple Y_j=S^(1/2)g_j to standard independent g_j as under Q. On symmetric matrices put F_j=g_jg_j^T-I, which has covariance 2I in Frobenius coordinates. Let B_S take upper offdiagonal entries after the map F -> S^(1/2) F S^(1/2), so W_j=B_S F_j. The conditional variance of the difference from the corresponding term at S=I is exactly

    4 N_q ||B_S^* B_S - B_I^* B_I||_HS^2.

Indeed different unordered column pairs are orthogonal and F_j are centered with covariance 2I. The squared Hilbert–Schmidt norm is at most
C p^2 (1+||S||_op)^4 ||S-I||_op^2 by the operator norm bound and the dimension of the symmetric matrix space. Its expectation is o(p^2) by (4)–(5) and the stated moment bounds. The coupled difference thus vanishes after dividing by sqrt(N). This proves T/sqrt(N) tends to N(gamma/2,1) under P and P'.

Let h(z)=exp((gamma/2) z-gamma^2/8), the likelihood between these limiting one-dimensional normals. Its second norm under N(0,1) is exp(gamma^2/4), matching (12). For bounded continuous h_M=min(h,M), put W=T/sqrt(N). Then

    E_Q (L'-h_M(W))^2
       -> E_(Z~N(0,1)) (h(Z)-h_M(Z))^2,

because the mixed term is E_P' h_M(W) and the other terms are (12) and E_Q h_M(W)^2. Letting M increase and using Cauchy–Schwarz controls the error when replacing L' by h_M(W) in TV. This proves the exact finite positive profile (1); the limiting TV is the Gaussian mean-shift distance 2 Phi(gamma/4)-1. The order is first dimensions tending to infinity at fixed clipping constant and fixed M, then M tending to infinity.

If rho tends to infinity and every d_i>=p, then a<=k/p tends to zero. For any fixed gamma_0>0 one can select a p' by q' submatrix with p',q' both tending to infinity, p'<=p, q'<=q, and p'q' a tending to gamma_0: take p' as the smaller of p and floor(sqrt(gamma_0/a)), then choose q' approximately gamma_0/(a p'). The original ratio tending to infinity leaves enough columns. The submatrix has exactly the same chain structure with only the outer dimensions changed. By data processing, the just-proved finite profile gives a lower bound, and gamma_0 can tend to infinity after the dimension limit. If d_i<p on any subsequence, the rank-deficiency argument already applies there. This proves the infinite endpoint.

## 5. Fixed small outer factor

For fixed p, the scatter YY^T/q captures the entire likelihood relative to Q whenever all d_i>=p, since each conditional density is a function of the scatter. Its law is the covariance process in (3) followed by one more Wishart step with q degrees of freedom. Normalize its fluctuation by multiplying S-I by sqrt(q).

For fixed p, the centered scaled Wishart V_d=sqrt(d)(W_d-I) tends in TV to real GOE normalized with diagonal variance two and upper offdiagonal variance one, i.e. N(0,2I_D) in Frobenius-orthonormal symmetric coordinates. This is a specialization of [Bubeck–Ding–Eldan–Racz, Theorem 7](https://arxiv.org/abs/1411.5713); at fixed p it also follows by expanding the Wishart density in those coordinates. If lambda is finite then all d_i tend to infinity. For each step and fixed good past S near I, the exact increment in the normalized process is sqrt(q/d_i) S^(1/2) V_(d_i) S^(1/2). Its conditional law is within o(1) TV of sqrt(q/d_i) times an independent GOE, by the Wishart limit and continuity in S of Gaussian covariance. Scalar multiplication has no cost in TV for each positive scale. The past is near I in probability since the number of steps is fixed and W_i converge in probability to I. Replacing the transitions one at a time costs o(1) total TV: integrate the conditional errors under the true past, or use sequential couplings, accumulating only the probability of a previous mismatch. The extra final step with q degrees of freedom adds another independent GOE on this scale. Thus the normalized scatter under P becomes asymptotically N(0,2(1+lambda)I_D) in TV, and that under Q becomes N(0,2I_D). Comparing their densities' crossing radius gives (2), including zero by continuity.

For fixed p and lambda tending to infinity, take subsequences. If all d_i tend to infinity, then a tends to zero and one can reduce q to q' approximately lambda_0/a for arbitrary fixed lambda_0, obtaining the limit one from the finite profile. If some d_i stay bounded, take a subsequence on which each d_i is fixed or tends to infinity. Reject any rank-deficient case as before; otherwise the scatter converges in distribution to a finite composition of nonsingular Wisharts and identity steps, with at least one genuinely random Wishart. This limit gives no atom at I, by conditioning on the last fixed-width step, whose law has a density under invertible congruence. Under Q the scatter converges to I. Comparing a ball shrinking sufficiently slowly about I gives TV tending to one.

These profiles apply to an abstract orthogonal tensor coordinate representation of the noise. The upper statements persist through any shared subsequent Markov processing; the lower statements do not assert a bound after wrapping or in a concrete scheme.

## Reproduction

    node verify-fixed-length-gaussian-matrix-products.js

The verifier checks finite Wishart covariance and auxiliary matrix identities and exact rectangle moment combinatorics on generated examples. The clipped likelihood proof provides the limiting statements, not a numerical fit.
