# The exact zero-dispersion window for flat product sources under linear hashing

Let \(\mathbb F_q\) be fixed, \(d\geq1\) fixed, and \(S\subseteq\mathbb F_q^d\) fixed with \(|S|>1\). Let \(X\) be uniform on \(S^n\subseteq\mathbb F_q^{dn}\). Independently take \(A\) uniform on all \(k\times dn\) matrices over \(\mathbb F_q\); in particular there is no conditioning on rank. Put
\[
 \lambda_n=|S|^n/q^k\longrightarrow\lambda\in(0,\infty),\quad
 Z_A(y)=|\{x\in S^n:Ax=y\}|,\quad
 \nu_A(j)=q^{-k}|\{y:Z_A(y)=j\}|.
\]
The empirical measure \(\nu_A\) conditions on the **publicly chosen matrix**; randomness in it is over matrices, not over a resampled matrix for each bin.

**Dichotomy.**
1. If \(S\) is **not** a translate of an additive subgroup, then \(\nu_A\) converges in probability in total variation to \(\operatorname{Pois}(\lambda)\). In particular the total variation of \(AX\), given \(A\), from uniform output converges in probability to
   \[
     e^{-\lambda}\frac{\lambda^{\lfloor\lambda\rfloor}}{\lfloor\lambda\rfloor!}.
     \tag{1}
   \]
2. If \(S=s+U\) for an additive subgroup \(U\), put \(E=\{a\in\mathbb F_q:aU\subseteq U\}\), \(b=|E|\), \(u=\dim_E U\), and \(v=[\mathbb F_q:E]\). This \(E\) is a subfield. Necessarily \(un-vk\) is eventually a fixed integer \(\kappa\), with \(\lambda=b^\kappa\). The output corank \(J_A\) of the restricted \(E\)-linear map \(A:U^n\to\mathbb F_q^k\) has the limiting law
   \[
    \Pr[J=j]=\frac{b^{-j(j+\kappa)}C_\infty(b)}
      {C_j(b)C_{j+\kappa}(b)},\quad j\geq\max(0,-\kappa),
    \qquad C_m(b)=\prod_{\ell=1}^m(1-b^{-\ell}).
    \tag{2}
   \]
   The empirical load measure for each \(A\) is supported on \(0\) and \(b^{J_A+\kappa}\), with masses \(1-b^{-J_A}\) and \(b^{-J_A}\), respectively. The conditional output TV is thus \(1-b^{-J_A}\), converging **in distribution** to \(1-b^{-J}\), a nonconstant limit at every fixed \(\kappa\).

There is also a finite-perturbation version of the additive branch. Append an independent arbitrary random variable \(T\in\mathbb F_q^a\) for fixed \(a\), apply an independent uniform \(k\times a\) matrix \(B\), and consider \(AX+BT\), at the **same base** \(|U|^n/q^k\to b^\kappa\). The limiting law of the conditional output TV, over the choices \(A,B\), is exactly this experiment: draw \(J\) as in (2), independently conditional on \(J\) draw a uniform \(E\)-linear map \(G:\mathbb F_q^a\to E^J\), and compute \(\|\mathcal L(GT\mid G)-U_{E^J}\|_{\mathrm{TV}}\). This is a genuine smaller-quotient reduction, not an assertion that the original structured matrix entries become independent.

For example, over \(\mathbb F_2\) take \(d=3\), \(k=2n\). The uniform source with single-block support \(\{0,e_1,e_2,e_3\}\) has limiting TV \(e^{-1}\); a plane of size four with the same entropy and zero dispersion gives the random rank law instead.

### Context

The [module information-spectrum note](https://github.com/mxym/math/blob/e67ae1997061f00436f6a73a50aec04ea4679b7b/research/euclidean-tensor-geometry/theoretical-cryptography/module-information-spectrum.md) leaves open a finer central window when an active quotient has zero dispersion. Here the fully flat field source has \(\log|S|^n\) fixed and the window is constant excess information \(\log\lambda_n\), not a nondegenerate CLT. The claim is for independent scalar entries over a fixed field (including fixed multiscalar input blocks as above), not general modules or side information. [Kopyttsev–Mikhailov](https://doi.org/10.4213/dm1091) give related Poisson moment criteria for counts in random linear inclusions via asymptotic freedom from linear combinations. The proof below identifies a product-support geometry dichotomy and gives the joint random-bin limit needed for an empirical, matrix-conditioned statement. [Kumar, *Linear Hashing Is Poissonesque*, §1.1 and Eq. (1)](https://arxiv.org/abs/2610.34750) bounds a logarithmic potential of the bin loads for arbitrary sets over the binary field, rather than asserting exact Poisson histograms for all sets. [Fulman–Goldstein, §1](https://arxiv.org/abs/1211.0504) give the classical iid finite-field rank law underlying (2); the transfer here is to a block-correlated restriction governed by the stabilizer subfield, with an additional genericity statement on the dual quotient. No cryptosystem, implementation, hidden secret, or offensive use is analyzed.

## 1. A one-block closure test

Let \(s\geq2\), let \(\alpha_1,\ldots,\alpha_s\in\mathbb F_q\) sum to one, and suppose at least two are nonzero. If \(\sum_i\alpha_i S\subseteq S\), then \(S\) is a translate of an additive subgroup. To prove it translate a point of \(S\) to zero, permissible since the coefficients sum to one. With \(0\in S\), setting all but one summand to zero shows \(\alpha_i S=S\) for the nonzero coefficients by cardinality. Using two such coefficients now gives \(S+S\subseteq S\), which makes a finite set containing zero an additive subgroup. Thus in the non-additive branch there is a strict loss of at least one out of \(|S|^s\) one-block choices for every such combination. The loss need not be uniform in \(s\), and only fixed \(s\) is used.

For an additive subgroup \(U\ne\{0\}\), the scalars mapping \(U\) into itself form a ring containing the prime field, and every nonzero one maps \(U\) onto itself by cardinality. Hence it is the subfield \(E\) above. More generally for a linear combination \(\sum_i\alpha_i U\subseteq U\), every coefficient must belong to \(E\) by setting the other operands to zero, regardless of their sum. For an \(h\)-tuple of independent draws from \(U\) and any fixed linear coefficient vector not all in \(E\), belonging of its result to \(U\) has probability at most \(1-|U|^{-h}\).

## 2. Poisson counts for common matrices, not just for one bin

Take independent uniform bin labels \(Y_1,\ldots,Y_\ell\in\mathbb F_q^k\), independent of \(A\), for fixed \(\ell\). For fixed nonnegative orders \(m_i\), expand the mixed factorial moment of \((Z_A(Y_i))_{i=1}^\ell\). It is a sum over ordered tuples of \(M=\sum_i m_i\) source points, distinct within each group, with one group per label. A point \(x\) assigned to group \(i\) gives the augmented row vector \((x,e_i)\in\mathbb F_q^{dn+\ell}\), where \(e_i\) is the tag in the extra coordinates. Since the \(k\times(dn+\ell)\) matrix \((A,-Y_1,\ldots,-Y_\ell)\) is uniform iid by construction, a tuple of augmented rank \(h\) contributes probability \(q^{-kh}\).

For \(h<M\), choose \(h\) positions giving a basis and give the coefficients of every other augmented row in that basis. There are boundedly many choices depending only on \(q\) and the fixed orders. Each dependent row has basis coefficients summing to one because taking the sum of the tag coordinates of every row gives one. The coefficient list cannot have just one nonzero entry: that entry would be one and the dependent row would be identical to some basis row, including its tag, which violates distinctness within that group. For any such fixed pattern, already one of its dependent rows requires the nontrivial affine combination of the basis points to lie in \(S\) separately in every block. By §1 the number of basis choices is at most
\[
 |S|^{nh}(1-|S|^{-h})^n .
\]
The same is an upper bound without enforcing any other rows or basis-rank constraints. Therefore the total factorial moment contribution from deficient patterns is \(o(1)\), since \(q^{-kh}|S|^{nh}=\lambda_n^h\) stays bounded. The full-rank tuples have count \((1+o(1))|S|^{nM}\): this is the total count up to the \(o(|S|^{nM})\) deficient tuples, and the within-group exclusions do not change the leading count. Thus each fixed mixed factorial moment tends to \(\lambda^M\).

These mixed factorial moments imply joint convergence to \(\ell\) independent Poisson variables of mean \(\lambda\). For instance ordinary mixed moments follow by expanding each power in falling factorials, tightness follows from bounded first moments, and bounded higher moments give uniform integrability on subsequences. The product Poisson limit is moment-determinate (each real linear projection has a finite moment generating function near zero). This argument counts coincident bin labels too; their independence and possible coincidence are already included in the augmented uniform matrix.

For \(\ell=1,2\) it follows that for fixed \(j\),
\(\mathbb E\nu_A(j)\to p_j\) and \(\mathbb E\nu_A(j)^2\to p_j^2\), with \(p_j\) Poisson. For the second identity condition on \(A\); the two independent uniform outputs sample the *same* histogram independently. Thus each \(\nu_A(j)\) concentrates. The deterministic mean \(\sum_j j\nu_A(j)=\lambda_n\) bounds the tails uniformly, giving total-variation convergence of the empirical measure in probability.

Given \(A\), the output density relative to uniform is \(Z_A(y)/\lambda_n\). The conditional TV is \(\mathbb E_{\nu_A}(1-Z/\lambda_n)_+\) since this density has mean one. The bounded integrand and convergence prove (1): for \(Z\sim\operatorname{Pois}(\lambda)\) and \(j=\lfloor\lambda\rfloor\), the expression is \(\Pr(Z\leq j)-\lambda^{-1}\mathbb E[Z\,1_{\{Z\leq j\}}]=\Pr(Z=j)\), including an integer \(\lambda\).

## 3. Rank law for the block-correlated additive restriction

Translations do not change TV or the load histogram, so take \(S=U\). For a fixed \(r\geq1\) count the ordered tuples of \(r\) \(E\)-independent vectors in \(\ker(A|_{U^n})\). Put \(D_A=\dim_E\ker(A|_{U^n})\). Dividing the count by \(G_r=\prod_{i=0}^{r-1}(b^r-b^i)\) gives the random Gaussian binomial coefficient \({D_A\brack r}_b\), the number of \(r\)-dimensional \(E\)-subspaces there.

A tuple of \(\mathbb F_q\)-rank \(h\) is killed with probability \(q^{-kh}\). If it is \(E\)-independent but has \(h<r\), then after choosing an \(\mathbb F_q\)-basis from the tuple, at least one dependent row has coefficient vector not all in \(E\), since otherwise the whole tuple lies in the \(E\)-span of the basis. With boundedly many choices of basis positions and coefficients, §1 gives a bound \(O_{q,r}(|U|^{nh}(1-|U|^{-h})^n)\) on such choices. Their probability-weighted contribution vanishes as \(|U|^{nh}q^{-kh}=\lambda_n^h=O_{q,r}(1)\). The full \(\mathbb F_q\)-rank tuples have count \((1+o(1))|U|^{nr}\); indeed the total ordered \(E\)-independent count is \(\prod_{i=0}^{r-1}(|U|^n-b^i)\), and the deficient count is negligible. Thus
\[
 \mathbb E{D_A\brack r}_b\longrightarrow \lambda^r/G_r .
 \tag{3}
\]
These are the subspace moments of the usual iid uniform \(E\)-matrix comparison in the limit of domain \(un\), codomain \(vk\), and excess \(\kappa\), since an \(r\)-subspace is killed there with probability \(b^{-vkr}\).

Here the moments characterize a unique law; one need not assume that the ordinary moments of \(b^{D_A}\) determine its distribution. For clarity, \(r=1\) gives tightness. For each \(r\), the ratio of consecutive Gaussian binomials at \(D\geq r+1\) is
\({D\brack r+1}_b/{D\brack r}_b=(b^{D-r}-1)/(b^{r+1}-1)\), which tends to infinity with \(D\). This and the bounded next moment give uniform integrability when taking subsequential limits. For any law \(D\) having the limiting moments (3), the finite \(b\)-binomial identity gives
\[
 \mathbb E\prod_{i=0}^{D-1}(1+b^i z)
 =\sum_{r\geq0} b^{r(r-1)/2}\frac{\lambda^r}{G_r}z^r .
\]
Use \(G_0=1\). The series is absolutely summable for every complex \(z\), since \(G_r=b^{r^2}C_r(b)\) with \(C_r(b)\) bounded away from zero, justifying expectation and expansion. The identity itself follows by successively multiplying the factors and the Gaussian binomial recurrence. At \(z=-b^{-j}\), the product is zero for \(D>j\), whereas for \(D=j\) it is nonzero. Starting at \(j=0\), these evaluations recover each probability \(\Pr(D=j)\) by a triangular system. Thus (3) forces the same limit as for the iid \(E\)-matrix comparison.

For that usual comparison with domain dimension \(N\) and output dimension \(L\), the probability of rank \(v_0\) is
\[
 b^{-NL}\frac{\prod_{i=0}^{v_0-1}(b^N-b^i)(b^L-b^i)}
                  {\prod_{i=0}^{v_0-1}(b^{v_0}-b^i)} .
\]
This counts factorizations of a rank \(v_0\) linear map as a surjection followed by an injection, modulo a change of intermediate basis. Substitute \(N-L=\kappa\), \(v_0=L-j\), take \(j\) fixed, and let \(N,L\to\infty\) to obtain (2). The limiting \(D\) equals \(J+\kappa\). For each restricted map the output law is uniform on an affine image of size \(b^{vk-J_A}\); all nonempty fibers have size \(b^{D_A}\). This proves the histogram and TV assertions, including that the limit is truly random since at least two of the probabilities in (2) are strictly positive.

## 4. The conditional quotient is generic for finite perturbations

Use the trace pairing \(\operatorname{Tr}_{\mathbb F_q/E}\langle y,x\rangle\) on input and output vector spaces, where \(\langle\ ,\ \rangle\) is the usual bilinear dot product over \(\mathbb F_q\). This pairing is nondegenerate over \(E\). Let \(W=\operatorname{im}(A|_{U^n})\) and \(W^\perp\) its \(E\)-annihilator in the output. We show that with probability tending to one an \(E\)-basis of \(W^\perp\) is \(\mathbb F_q\)-linearly independent. This is automatic if \(E=\mathbb F_q\); otherwise \(U^\perp\) in the *input-block* pairing is nonzero and has the same scalar stabilizer \(E\) as \(U\): scalar multiplication is self-adjoint under the trace pairing, and one can take orthogonal complements twice to see the equivalence.

For each fixed \(r\), count \(E\)-independent \(r\)-tuples \(y\) in \(W^\perp\) of \(\mathbb F_q\)-rank \(h<r\). Choose an \(\mathbb F_q\)-basis among the tuple and write the other vectors in it; there is a fixed number of position and coefficient patterns. The basis choices have count \(O(q^{kh})\), and at least one dependent \(y\) uses a coefficient outside \(E\). For each of the \(n\) independent blocks of \(d\) columns of \(A\), the products with the basis \(y\)'s are \(h\) independent uniform elements of \(\mathbb F_q^d\), since the \(y\)'s are independent over \(\mathbb F_q\). They must all land in \(U^\perp\), an event of probability \(|U|^{-h}\). Conditional on that event, the products are independent uniform in \(U^\perp\). The specified non-\(E\) combination lands there with a strict loss bounded by \(1-|U^\perp|^{-h}\) by §1. The expected count of the tuples under consideration is therefore
\[
 O_{q,r}\big(q^{kh}|U|^{-nh}(1-|U^\perp|^{-h})^n\big)=o(1).
\]
Since \(J_A\) is tight by (2), this proves the genericity claim by first restricting to \(J_A\leq J_0\) for fixed \(J_0\), then letting \(J_0\to\infty\).

On this event choose an \(E\)-basis \(y_1,\ldots,y_{J_A}\) of \(W^\perp\). The quotient by \(W\) is identified with \(E^{J_A}\) by taking the trace pairings with these vectors. Each column of the independent \(B\) then gives \((\langle y_i,B_{\cdot c}\rangle)_i\) uniform on \(\mathbb F_q^{J_A}\), independently across columns, because the basis vectors are \(\mathbb F_q\)-independent. After pairing with the coordinates of \(T\) and taking the trace, this is precisely a uniform \(E\)-linear map into \(E^{J_A}\) by the nondegeneracy of the scalar trace pairing. Conditional on the base \(A\), its law depends only on \(J_A\). Adding \(AX\) makes the output uniform within each coset of \(W\) without changing the \(BT\) mass assigned to that coset, up to a fixed translation from \(s\). TV to uniform is exactly TV on the quotient. Since the nongeneric probability tends to zero and \(J_A\) converges in law to \(J\), the stated finite-perturbation experiment follows.

## Reproduction

Run `python3 verify-flat-product-field-critical.py`. The standard-library checker verifies finite tagged rank-count formulas for binary non-affine blocks, exact finite rank moments and Gaussian-binomial inversion, and examples using a genuinely block-correlated subfield restriction. These are checks of finite identities, not a substitute for the limits.
