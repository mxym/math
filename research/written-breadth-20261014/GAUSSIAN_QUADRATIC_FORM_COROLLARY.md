# Positive quadratic-form and Gaussian block-norm product inequality

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. ORCID 0009-0000-3864-3536;
mxymmxym1@gmail.com. 14 October 2026, Asia/Shanghai.
No external funding. OpenAI AI assistants assisted research and writing.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.
Status: complete ordinary proof of an explicitly attributed corollary; not a solution credited here to the scalar Gaussian product conjecture, and not a new major-conjecture count.

## External input and exact scope

We use Theorem 1 of Frédéric Ouimet and Dylan Greaves,
[A proof of the strong Gaussian product inequality conjecture, arXiv:2609.20234v1](https://arxiv.org/html/2609.20234v1).
Its actual assertion is
\[
 \mathbb E\prod_{i=1}^s |Y_i|^{p_i}
 \geq \prod_{i=1}^s\mathbb E|Y_i|^{p_i},
 \qquad p_i>0,
 \tag{G}
\]
for every centered jointly real Gaussian vector, including singular covariance.
If all marginal variances are positive, equality is equivalent to independence.
This preprint input was read at its statement and complete main proof. We do not reprove it here or certify its historical priority or external peer review.

In (G), the right side is the product of **all individual marginal moments**.
It is not the generally false assertion that one can replace it by products of arbitrarily grouped joint moments. The different use of "strong" in older literature must not change the statement being used.

## N1. Arbitrary finite real Gaussian blocks

Let \(X_i\in\mathbb R^{d_i}\), \(d_i\geq1\), \(1\leq i\leq s\), be jointly centered real Gaussian blocks. Their total covariance may be singular; there is no restriction on the block sizes or correlations. For every \(p_i>0\),
\[
 \mathbb E\prod_{i=1}^s\|X_i\|^{p_i}
 \geq \prod_{i=1}^s\mathbb E\|X_i\|^{p_i}.                 \tag{N}
\]
If some \(X_i=0\) almost surely, equality is automatic. If no block is almost surely zero, equality holds exactly when the blocks are jointly independent.

### Proof

Let \(\sigma_d\) denote the uniform probability measure on \(S^{d-1}\), including the two-point sphere for \(d=1\). Rotational invariance and the beta integral give, for all \(x\in\mathbb R^d\),
\[
 \int_{S^{d-1}}|\langle u,x\rangle|^p\,d\sigma_d(u)
 =c_{d,p}\|x\|^p,\qquad
 c_{d,p}=\frac{\Gamma(d/2)\Gamma((p+1)/2)}
                 {\sqrt\pi\,\Gamma((d+p)/2)}>0.           \tag{1}
\]
For each fixed tuple \(u_i\in S^{d_i-1}\), apply (G) to
\(Y_i=\langle u_i,X_i\rangle\). Integrate the result with respect to
\(\bigotimes_i\sigma_{d_i}\). Tonelli's theorem and (1) turn its two sides into the corresponding sides of (N), multiplied by the same positive number \(\prod_i c_{d_i,p_i}\). All moments are finite: Hölder reduces each joint moment to Gaussian norm moments of finite orders. This proves (N).

Write \(C_{ij}=\mathbb E[X_iX_j^{\mathsf T}]\). If no block is almost surely zero, \(C_{ii}\neq0\), so
\(u_i^{\mathsf T}C_{ii}u_i>0\) for almost every spherical direction: its zero set is the intersection with the proper kernel of the nonzero positive semidefinite matrix \(C_{ii}\).

If some \(C_{ij}\neq0\), the continuous bilinear function
\(u_i^{\mathsf T}C_{ij}u_j\) is nonzero on a nonempty open subset of the two spheres. This set has positive spherical product measure. Intersecting it with the full-measure sets of positive variances for all projections still gives positive measure. On this set (G) is strict by its equality assertion. Its integrated nonnegative gap is therefore strictly positive. Hence equality in (N) forces every \(C_{ij}=0\) for \(i\neq j\). For jointly Gaussian blocks this condition is equivalent to joint independence. Independence also gives equality directly. The zero-block case has both sides zero. \(\square\)

Powers equal to zero may be included by adopting the constant factor \(x^0=1\) and deleting their blocks before applying the statement and equality test.

## Q1. Every collection of Gaussian positive semidefinite quadratic forms

Let \(G\sim N(0,\Sigma)\), where \(\Sigma\) is any finite real positive semidefinite matrix, and let \(B_i\succeq0\) be arbitrary real symmetric matrices of the same size. They need not commute and need not have disjoint supports. Put
\(Q_i=G^{\mathsf T}B_iG\). For all \(a_i>0\),
\[
 \mathbb E\prod_{i=1}^s Q_i^{a_i}
 \geq\prod_{i=1}^s\mathbb E Q_i^{a_i}.                    \tag{Q}
\]
If some \(\operatorname{tr}(\Sigma B_i)=0\), equality is automatic.
Otherwise the following conditions are equivalent:

1. equality in (Q);
2. \(B_i^{1/2}\Sigma B_j^{1/2}=0\) for every \(i\neq j\);
3. \(\operatorname{tr}(B_i\Sigma B_j\Sigma)=0\) for every \(i\neq j\);
4. the quadratic forms \(Q_i\) are jointly independent.

### Proof

Apply N1 to \(X_i=B_i^{1/2}G\) and \(p_i=2a_i\), since
\(\|X_i\|^2=Q_i\). The mean of \(Q_i\) is \(\operatorname{tr}(\Sigma B_i)\); its vanishing is equivalent to this nonnegative random variable being almost surely zero. Also \(C_{ij}=B_i^{1/2}\Sigma B_j^{1/2}\), and
\[
 \|C_{ij}\|_{\mathrm F}^2=\operatorname{tr}(B_i\Sigma B_j\Sigma).
 \tag{2}
\]
This proves the equality characterization and equivalence of the first three conditions. They imply independence of the blocks and thus of their squared norms. Conversely, independence of the forms implies their pairwise covariances vanish. The Gaussian fourth-moment identity gives
\[
 \operatorname{Cov}(Q_i,Q_j)
 =2\operatorname{tr}(B_i\Sigma B_j\Sigma).
 \tag{3}
\]
Equation (2) then gives condition 2, and hence joint independence of the Gaussian blocks. \(\square\)

## C1. Complex Gaussian blocks, including improper laws

Let \(Z_i\in\mathbb C^{d_i}\) be jointly centered complex Gaussian, meaning that their real and imaginary parts are jointly real Gaussian. No properness assumption is needed. Realification identifies their Euclidean norms with those in N1, so (N) holds with \(Z_i\) in place of \(X_i\). With no almost surely zero block, equality holds exactly when, for all distinct blocks,
\[
 K_{ij}:=\mathbb E[Z_iZ_j^*]=0,\qquad
 P_{ij}:=\mathbb E[Z_iZ_j^{\mathsf T}]=0.                  \tag{4}
\]
Indeed the real cross covariance vanishes exactly when both complex matrices in (4) vanish. Writing \(Z_i=U_i+\mathrm i V_i\), its four real cross blocks are
\[
 \mathbb E[U_iU_j^{\mathsf T}]=\tfrac12\Re(K_{ij}+P_{ij}),
 \quad
 \mathbb E[V_iV_j^{\mathsf T}]=\tfrac12\Re(K_{ij}-P_{ij}),
\]
\[
 \mathbb E[V_iU_j^{\mathsf T}]=\tfrac12\Im(K_{ij}+P_{ij}),
 \quad
 \mathbb E[U_iV_j^{\mathsf T}]=\tfrac12\Im(P_{ij}-K_{ij}).
\]
For jointly proper complex Gaussian blocks all \(P_{ij}\) vanish already, and (4) reduces to vanishing Hermitian cross covariance.

The pseudo-covariance condition is essential. If \(U,V\) are independent
\(N(0,1/2)\), set \(Z_1=U+\mathrm iV\) and \(Z_2=U-\mathrm iV\).
Then \(K_{12}=0\), \(P_{12}=1\), and \(|Z_1|=|Z_2|\) is nonconstant. The product inequality is strict for every pair of positive exponents.

## Wishart connection and the unresolved boundary

For every **positive integer** degree of freedom \(\nu\), the Gaussian representation of \(W\sim W_p(\nu,\Sigma)\) expresses each trace of a diagonal block as the squared norm of a Gaussian block formed by stacking its \(\nu\) independent samples. N1 therefore gives the comparison with the product of all marginal trace moments, with exact equality conditions, for every positive real power and arbitrary diagonal block sizes.

This argument provides neither a representation at noninteger \(\nu\) nor a product inequality for determinants of diagonal blocks. In particular it does not close [Conjecture 1.1 of Genest–Ouimet–Richards, arXiv:2311.00202v3](https://arxiv.org/html/2311.00202v3), whose actual range is all \(\nu>p-1\), positive definite scale matrices, arbitrary finite disjoint block sizes, and all nonnegative real determinant powers. That full conjecture is the subsequent research target.

The different grouped trace assertion in Conjecture 1 of
[Genest–Ouimet, arXiv:2206.01976v2](https://arxiv.org/html/2206.01976v2)
must be treated separately. Its literal range includes the already problematic one-degree Gaussian case. No first-refutation claim is made here.

## Theorem map and verification boundary

| Claim | Inputs | Actual range | Status |
|---|---|---|---|
| N1 | External scalar theorem (G), spherical beta integral, Tonelli | All finite real centered Gaussian blocks, all positive real powers | Complete corollary proof |
| Q1 | N1, Gaussian fourth moments | All PSD covariances and all PSD forms, all positive real powers | Complete corollary proof, complete equality cases |
| C1 | N1, invertible realification identities | All centered complex Gaussian blocks, proper or improper | Complete corollary proof, complete equality cases |
| Wishart trace consequence | N1, Gaussian sample representation | All positive integer degrees; arbitrary trace blocks and positive powers | Explicitly limited consequence |
| Full determinant Wishart conjecture | No proof supplied | All real \(\nu>p-1\), all disjoint blocks and nonnegative powers | Unresolved here |

This note has a self-check by its authoring assistant only. It is not an independent second-agent review, external human peer review, Lean proof, or historical-priority certification. No numerical experiment is an input to any proof above.
