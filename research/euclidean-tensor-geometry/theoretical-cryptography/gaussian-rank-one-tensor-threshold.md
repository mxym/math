# A sharp rectangular-width threshold for two-factor Gaussian tensor noise

**Model and scope.** In a fixed real Hilbert tensor product of dimensions p and q, consider a proposed replacement of standard spherical Gaussian noise by a variance-matched sum of r independent rank-one Gaussian tensors. After orthonormal coordinates the sum has the law of a product of two Gaussian matrices. The result below determines its total-variation approximation threshold, including highly unequal factors. For the cyclotomic tensor-product identification see [Lyubashevsky–Peikert–Regev, Toolkit Proposition 2.13 and §2.5.2](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf); for coprime cyclotomic conductor factors the canonical embeddings pair across the CRT indices. Hence the canonical inner product of two pure tensors factors into the two inner products, and dimension equality extends this to a real Hilbert isometry. The result is invariant under that identification. The standard error definitions of Ring-LWE do not assert generation by rank-one terms. This is solely a statistical comparison of two synthetic error laws, not a new hardness assumption, a concrete implementation, or a claim about a scheme.

Let G be p by r and H be r by q, independently with iid N(0,1) entries, and let

    Y=GH/sqrt(r),           Q= iid N(0,1) p-by-q matrix law.

Write P for the law of Y. Transposition allows p<=q. [Li–Woodruff, Theorem 1(a)](https://arxiv.org/abs/2108.09887) establishes the sufficient r≫pq condition in the regime r>=max(p,q), which is automatic there. Their Theorem 1(b) provides the lower scale sqrt(q) p^(3/2) for the two-factor specialization of their general product theorem, using Schatten moments; these scales may separate for unequal p,q. Here for two factors specifically we remove the rectangular gap and compute limiting profiles for two regimes. We make no claim about longer products.

## 1. Threshold and profiles

As q tends to infinity with arbitrary p<=q:

- TV(P,Q) tends to zero **if and only if** r/(pq) tends to infinity.
- TV(P,Q) tends to one when r/(pq) tends to zero.
- If p,q both tend to infinity and r/(pq) tends to c in (0,infinity),

      liminf TV(P,Q) >= 2 Phi(1/(4c))-1.                     (1)

  If also q/p^3 tends to infinity, equality holds in (1) with a limit.
- If p is fixed and q/r tends to lambda in (0,infinity), there is an exact limit. Set D=p(p+1)/2, F_D the chi-squared(D) CDF, and

      t_*=D(1+lambda) log(1+lambda)/lambda.
      lim TV(P,Q)=F_D(t_*)-F_D(t_* /(1+lambda)).             (2)

The general critical limit for growing factors with q=O(p^3) is not determined here. No finite-dimensional Gaussian projection approximation is assumed uniformly for that range.

## 2. Rectangular Wick component

Write S=GG^T/r. Conditional on S, the columns Y_j are independent N(0,S) vectors. Put N_p=binom(p,2), N_q=binom(q,2), N=N_p N_q, and for p,q>=2 define

    T(Y)=sum_(i<i',j<j') Y_ij Y_i'j Y_ij' Y_i'j'.

Under Q different rectangles have orthogonal monomials and each has variance one, so E_Q T=0 and Var_Q T=N. Given S, define Z_j indexed by unordered pairs i<i' with coordinates Y_ij Y_i'j; their mean vector v has entries S_ii'. Their covariance K satisfies

    K_(ii'),(kk') = S_ik S_i'k' + S_ik' S_i'k.

Then T=sum_(j<j') Z_j^T Z_j'. Writing W_j=Z_j-v gives its exact scalar/linear/degenerate decomposition

    T = N_q ||v||^2 + (q-1) sum_j v^T W_j
                         + sum_(j<j') W_j^T W_j'.          (3)

The latter terms are conditionally centered and orthogonal because the W_j are independent and centered. Distinct column pairs in the last term are also orthogonal, even if they share one column. Thus

    Var(T|S)=q(q-1)^2 v^T K v + N_q ||K||_F^2.              (4)

The first two Wishart moments needed for v are explicit:

    E ||v||^2 = N_p/r,
    Var ||v||^2 = N_p (2/r^2+6/r^3) + 12 binom(p,3)/r^3.   (5)

Indeed, S_ii' is the inner product of independent Gaussian rows divided by r. Its fourth moment is 3 r(r+2)/r^4, giving the first variance term. Two different squared inner products are independent if the row pairs are disjoint. With a shared row u their conditional means are both ||u||^2/r^2 and the squares are conditionally independent, yielding covariance 2/r^3. There are 3 binom(p,3) unordered overlapping pairs.

For r>=p, S has uniformly bounded operator-norm moments of any fixed order. If p/r tends to zero then ||S-I||_op tends to zero in each fixed L^a. For completeness, for a fixed unit vector x the quadratic form x^T S x is chi-squared(r)/r. The usual chi-squared tail bound exp(-c r min(t^2,t)) follows by its moment generating function. Applying it on a 1/4-net of size at most 9^p, and using that the operator norm of a real symmetric matrix is at most twice the largest absolute net quadratic form, proves uniform moment bounds when r>=p and convergence in probability when p/r tends to zero. The same moment bounds give uniform integrability.

For an offdiagonal coefficient vector b, b^T K b is the variance of a Gaussian quadratic form with symmetric coefficient matrix A having A_ii'=b_(ii')/2 for i!=i' and zero diagonal. Wick's formula yields

    b^T K b = 2 ||S^(1/2) A S^(1/2)||_F^2 <= ||S||_op^2 ||b||^2.

It follows by (5), Cauchy–Schwarz and the norm moments that
E||K||_F^2<=Cp^2 and E[v^T K v]<=Cp^2/r. Hence for r>=p, from (4)–(5),

    E_P T = N/r,
    Var_P T <= C [q^2 p^2 + q^3 p^2/r
                        + q^4(p^2/r^2+p^3/r^3)].           (6)

If both p,q grow and r/(pq) tends to zero, (6) gives Var_P T/(E_P T)^2 tending to zero, and Var_Q T/(E_P T)^2 also tends to zero. Comparing the two laws at the midpoint of their means yields TV tending to one. If r<p then the product is rank deficient while Q is full rank almost surely, so TV is exactly one. These arguments together prove the small-r statement for p tending to infinity.

## 3. Critical lower profile when both factors grow

Under Q the normalized rectangle sum T/sqrt(N) tends to standard normal. Here is an elementary moment check for the [Nualart–Peccati fourth moment theorem](https://arxiv.org/abs/math/0503598). Each rectangle monomial is in fourth Gaussian chaos. The second moment after normalization is exactly one. In the fourth moment expansion a term vanishes unless all cells occur an even number of times. Two pairs of equal rectangles account for 3N(N-1) ordered quadruples, except that their weights can exceed one when the distinct rectangles share a cell. That fraction is O(1/(pq)), because their row pairs and column pairs must both intersect. The all-identical contribution is O(N). Exactly three distinct rectangles cannot contribute, since the two unrepeated ones would need equal cell sets.

For four distinct rectangles the even-cell rule forces each used row and each used column to occur in at least two rectangles. Thus at most four rows and four columns occur. If exactly four of each occur, every used row and column occurs twice. Both rectangles incident to a row must have the same two columns. Take one rectangle with row pair A and column pair B. Either its two rows are both in a single other rectangle, which must then be identical, or they force two other rectangles each using B, contradicting the fact that the columns of B occur twice. Thus at least one side uses at most three distinct indices. The four-distinct contribution is O(p^3q^4+p^4q^3), as there are only a bounded number of edge patterns on fixed sets and Gaussian moments of fixed degree are bounded. Dividing by N^2 gives fourth moment tending to three. This proves the claimed CLT without a relation between the rates p,q.

Now let r/(pq) tend to c in (0,infinity), p,q tending to infinity. By (4)–(6) the linear term in (3), scaled by sqrt(N), tends to zero in L2; its variance after scaling is O(q/r)=o(1). The conditional-mean term minus N/r also tends to zero in this scale, by (5). Couple the third term in (3) with its Q version using independent g_j~N(0,I_p), Y_j=S^(1/2)g_j, and set F_j=g_j g_j^T-I. On real symmetric matrices with Frobenius inner product the covariance of F_j is 2I. Let B_S be the linear map taking the upper offdiagonal entries of S^(1/2) F S^(1/2). Then W_j=B_S F_j and the difference of the coupled degenerate terms is

    sum_(j<j') <F_j, (B_S^* B_S - B_I^* B_I) F_j'>.

Conditionally its variance is 4 N_q ||B_S^* B_S-B_I^* B_I||_HS^2, by independence, orthogonality of different column pairs, and the covariance identity for F_j. The squared Hilbert–Schmidt norm is at most
C p^2 (1+||S||_op)^4 ||S-I||_op^2: bound first the operator norm using ||S^(1/2)-I||_op<=||S-I||_op, then use the dimension p(p+1)/2. Since p/r tends to zero, the averaged variance is o(N). Therefore under P, T/sqrt(N) tends to N(1/(2c),1), as sqrt(N)/r tends to 1/(2c). Under Q it tends to N(0,1). A threshold midway between these means gives (1).

## 4. Sufficiency of the scatter and the exact profiles

When q>=p and r>=p, the two densities on the full matrices depend on the matrix only through its scatter U=YY^T/q. Indeed, the conditional normal density given S depends on Y through tr(S^(-1) YY^T). The likelihood relative to Q therefore depends only on U. As a result, total variation is equal to the total variation of the scatter laws, not just bounded below by it.

Let V_r=sqrt(r)(S-I), and independently let V_q be the analogous standardized Wishart fluctuation for the empirical covariance of q standard p-dimensional normals. Under P the standardized scatter has the representation

    sqrt(q)(U-I)=sqrt(q/r) V_r + S^(1/2) V_q S^(1/2),       (7)

while under Q it is V_q. Let Z_p denote real GOE normalized with variances two on the diagonal and one on the upper offdiagonal. In Frobenius-orthonormal coordinates of real symmetric matrices this is exactly N(0,2I_D).

For fixed p (also p=1), V_k approaches Z_p in TV as k tends to infinity. For p tending to infinity and k/p^3 tending to infinity the same is true by [Bubeck–Ding–Eldan–Rácz, Theorem 7](https://arxiv.org/abs/1411.5713). For fixed p one can also see this directly from the Wishart density: on compact sets of standardized symmetric matrices the factor det(I+X/sqrt(k))^((k-p-1)/2) exp(-sqrt(k) tr(X)/2) approaches exp(-tr(X^2)/4) uniformly. Tightness follows from the fixed-dimension second moments, so its normalizing constants converge, and then Scheffé's theorem gives TV convergence.

For fixed p and q/r tending to finite positive lambda, replace V_q by Z_p in (7), with TV error tending to zero by independent postprocessing. Then replace S^(1/2) Z_p S^(1/2) by Z_p independently of S. For this step and also growing p, condition on S: if its eigenvalues l_i are in [1/2,2], the covariance ratios of these two centered Gaussians, in Frobenius coordinates, are l_i l_j over i<=j. Their KL divergence is

    (1/2) sum_(i<=j) (l_i l_j - 1 - log(l_i l_j))
            <= C p ||S-I||_F^2.

The expected bound is O(p^3/r) since E ||S-I||_F^2=(p^2+p)/r; the bad spectral event has vanishing probability when p/r tends to zero. Thus if p^3/r tends to zero, Pinsker's inequality and conditioning justify replacing by an independent Z_p in TV. Finally replace V_r by an independent Z_p, again by data processing. These replacements apply both for fixed p and the growing regime q/p^3 tending to infinity with r/(pq) tending to c. They reduce the TV comparison of scatters to the comparison of N(0,2I_D) and N(0,2(1+q/r)I_D).

For fixed D the densities of these Gaussians cross exactly at squared radius t_* in coordinates divided by sqrt(2); the difference of the two interior ball probabilities gives (2). In the growing rectangular regime put u=q/r, then u tends to zero and D u^2 tends to 1/(2c^2). Under the reference N(0,I_D), the log-likelihood of N(0,(1+u)I_D) is

    -D log(1+u)/2 + u chi-squared(D)/(2(1+u)).

By the scalar chi-squared CLT and Taylor expansion this approaches N(-1/(8c^2),1/(4c^2)). Taking E(1-exp(log likelihood))_+ gives exactly 2 Phi(1/(4c))-1, matching (1).

For fixed p and r/q tending to zero there are two possibilities, handled on subsequences. If r stays bounded, either r<p and the rank argument applies, or the scatter converges in probability to the random S under the product representation, whereas it converges to I under Q. S has no atom at I. If r tends to infinity, use scale sqrt(r): in (7) the V_q term multiplied by sqrt(r/q) tends to zero in probability while V_r tends to GOE, whereas under Q the rescaled scatter tends to zero. In either case a vanishing-radius ball about the null limit makes TV tend to one.

Finally, Li–Woodruff gives the vanishing upper bound whenever r/(pq) tends to infinity. Conversely, if this ratio fails to diverge, pass to a subsequence on which it tends to some finite c>=0 and on which either p is fixed or p grows. The small-r case or the critical lower profiles are positive there. This completes the threshold statement for arbitrary aspect ratios with q growing.

For the original abstract error substitution the *upper* bounds remain valid under any common subsequent linear embedding, addition of the same independent signal, discretization or wrapping by data processing. The lower bounds compare the unwrapped noise alone and need not survive those operations.

## Reproduction

    node verify-gaussian-rank-one-tensor-threshold.js

This runs finite exact Wick identities, even-cell enumeration, and numerical radial likelihood checks in synthetic examples. The limits above follow from the proofs, not from fitted asymptotics.
