# A logarithmic smoothing cutoff for boundedly anisotropic lattice Gaussians

**Status:** proved for the matrix class stated below. Main example is the canonical dual of the codifferent in the power-of-two cyclotomic family. This is an asymptotic statement about Gaussian mass, not a cryptanalysis result, implementation recommendation, or change to a whole Ring-LWE reduction.

## 1. Statement

Let \(Q_n\) be a real symmetric matrix with diagonal entries 1. Assume, uniformly in \(n\),
\[
  Q_n\succeq aI,\qquad \max_i\sum_j |(Q_n)_{ij}|^2\le B^2,
  \qquad 1/2<a<1,\quad B<\infty.
\]
For \(t>0\) set
\[
  Z_Q(t,z)=\sum_{v\in\mathbb Z^n} z^{|\operatorname{supp}v|}
           e^{-t v^TQv},\qquad Z_Q(t)=Z_Q(t,1).
\]
Write \(x=n e^{-t}\), \(\gamma=a-1/2\), and \(\delta=\gamma/2\). For every fixed \(A\ge0\), uniformly over the stated matrix class and \(t\ge\log n-A\),
\[
  \boxed{\log Z_Q(t)=2n e^{-t}\bigl(1+O_{a,B,A}(n^{-\delta})\bigr).} \tag{1}
\]
The logarithm of \(Z_Q(t,z)\), normalized to vanish at zero, is \(2xz+O_{a,B,A}(n^{-\delta}x)\) throughout \(|z|\le2\), for sufficiently large \(n\). In fact the difference from the product weights satisfies the stronger qualitative bound
\[
 \sum_{v\in\mathbb Z^n}\bigl|e^{-t v^TQv}-e^{-t\|v\|_2^2}\bigr|=o(x) . \tag{2}
\]
Consequently the normalized distributions have total variation \(o(x)\), and at \(t=\log n+u\) for fixed real \(u\), the number of nonzero coordinates converges to \(\operatorname{Poisson}(2e^{-u})\). The estimate (1) includes \(t-\log n\to+\infty\), not just the bounded transition window. In particular, for every fixed \(E>0\) and all \(0<\epsilon_n\le E\), the unique solution of \(Z_Q(t)-1=\epsilon_n\) is
\[
  \boxed{t_\epsilon=\log\!\left(\frac{2n}{\log(1+\epsilon_n)}\right)
         +O_{a,B,E}(n^{-\delta}).} \tag{3}
\]
No lower bound on \(\epsilon_n\) is needed.

## 2. A fixed number of occupied sites

Put \(h(s)=2\sum_{m\ge1}e^{-s m^2}\). For \(s\ge1\), \(h(s)=2e^{-s}(1+O(e^{-3s}))\), and \(\sum_{m\ne0}m^2 e^{-s m^2}=O(e^{-s})\), by comparison with convergent sums at \(s=1\).

Fix \(k\). Join sites \(i,j\) when \(|Q_{ij}|>n^{-\delta}/t\); the maximum degree is at most \(B^2t^2 n^{2\delta}\). On a support of size \(k\), let its induced graph have connected components of sizes \(r_1,\dots,r_c\). After multiplication by \(t\), the absolute contribution of all cross-component quadratic terms is at most \((k-1)n^{-\delta}\sum_i v_i^2\), using \(2|v_i v_j|\le v_i^2+v_j^2\). A singleton has precision 1, and each nonsingleton principal block has precision at least \(aI\).

Let \(d=1+B^2t^2n^{2\delta}\). The number of supports with prescribed component sizes is at most \(C_k n^c d^{\,k-c}\): for each component choose a labeled spanning tree, its root site and successive adjacent sites. Ignoring extra constraints only increases the bound. Summing the Gaussian weights of the nonzero coordinates, the total is at most \(C_k\) times the product of one factor \(x\) per singleton and one factor
\[
  x\, d^{\,r-1}e^{-(ar-1)t}
\]
per component of size \(r\ge2\). The same bound applies to the product weights, since those have within-component precision 1. For each fixed \(r\ge2\) the factor after \(x\) is \(O_{a,B,A,r}(n^{-\delta})\). Indeed, the maximum of \((1+t)^{2(r-1)}e^{-(ar-1)t}\) on the indicated \(t\)-range occurs at its left endpoint for large \(n\), and
\[
  ar-1-2\delta(r-1)=\gamma+(r-2)/2>\delta .
\]
Since \(x\le e^A\), supports with any strong edge contribute \(O_{k,a,B,A}(n^{-\delta}x)\).

On a support without strong edges, \(|t(v^TQv-\|v\|^2)|\le (k-1)n^{-\delta}\|v\|^2\). Using \(|e^y-1|\le |y|e^{|y|}\) and the one-dimensional second-moment estimate above, the sum of absolute differences on this support is \(O_k(n^{-\delta}e^{-kt})\). Summation over at most \(n^k\) supports gives the same required bound (the zero-support difference is zero). Therefore
\[
 \sum_{|\operatorname{supp}v|=k}|e^{-t v^TQv}-e^{-t\|v\|^2}|
       =O_{k,a,B,A}(n^{-\delta}x) . \tag{4}
\]
This fixed-\(k\) estimate alone does not justify summing over \(k\). A uniform large-cluster bound is needed.

## 3. Large connected clusters from a tree-graph estimate

Use site-charge particles \(p=(i,m)\), \(m\in\mathbb Z\setminus\{0\}\), with activity \(e^{-t m^2}\). Set
\[
 V((i,m),(j,l))=\begin{cases}+\infty,&i=j,\\2tQ_{ij}ml,&i\ne j.\end{cases}
\]
Hard core permits at most one particle at a site. The exponential generating sum over labeled particles, with Boltzmann factor \(\prod_{i<j}e^{-V_{ij}}\), is exactly \(Z_Q(t,z)\). The coefficient \(b_k=[z^k]\log Z_Q(t,z)\) is given by
\[
 b_k=\frac1{k!}\sum_{p_1,\ldots,p_k}e^{-t\sum m_i^2}
             \sum_{G\ {\rm connected}}\prod_{ij\in G}(e^{-V_{ij}}-1). \tag{5}
\]
For finite marks this follows by expanding every pair factor as \(1+(e^{-V}-1)\) and separating the connected components of each graph. The infinite-mark limit is justified after the bound below.

Every subset of labels satisfies \(\sum_{i<j} V_{ij}\ge-(1-a)t\sum m_i^2\), by the spectral inequality on distinct sites and by hard core otherwise. The improved tree-graph inequality of [Procacci–Yuhjtman](https://arxiv.org/abs/1508.07379) in [Ueltschi's variable-stability form, Theorem 1](https://arxiv.org/abs/1705.05353) bounds the absolute connected sum in (5) by
\[
 e^{(1-a)t\sum m_i^2}\sum_{T\ {\rm tree}}\prod_{ij\in T}
                                    (1-e^{-|V_{ij}|}).
\]
The form with hard core follows by replacing infinite energies by a sufficiently large positive number for each fixed tuple, and passing to the limit. The site part of each tree edge is bounded by the entry of the nonnegative matrix \(D_{ij}=\mathbf1_{i=j}+2t|Q_{ij}|\mathbf1_{i\ne j}\), times \(|m_i m_j|\). Its row sums are at most \(D=1+2tB\sqrt n\). Removing leaves one by one bounds the site sum for a tree by \(nD^{k-1}\).

For \(s\ge1\), \(\sum_{m\ne0}|m|^d e^{-s m^2}\le C d! e^{-s}\), since \(|m|^d\le d!e^{|m|}\) and \(\sum_{m\ne0}e^{|m|-(m^2-1)}<\infty\). The charge contribution of a tree is therefore bounded by \((Ce^{-at})^k\prod_i d_i(T)!\). By the Prüfer code,
\[
 \sum_T\prod_i d_i(T)!=(k-2)![y^{k-2}](1-y)^{-2k}
                    =(k-2)!\binom{3k-3}{k-2}\qquad(k\ge2).
\]
After division by \(k!\) the combinatorial factor is at most \(8^k\). In particular every sum in (5) converges absolutely after grouping the finite connected graph sum, and the finite-mark identity passes to the limit. Enlarging \(C\) gives, for \(k\ge2\),
\[
  |b_k|\le nD^{k-1}(Ce^{-at})^k. \tag{6}
\]

Uniformly on the stated \(t\)-range, \(D e^{-at}=O_{a,B,A}(n^{-\gamma}\log n)\). Thus the logarithm series converges absolutely on \(|z|\le2\) for sufficiently large \(n\); exponentiation gives the original fugacity polynomial there, by equality of the formal series at zero. Choose a fixed integer \(K\ge2\) with \(K\gamma>1/2+\delta\). The tail of the logarithm on this disk is bounded by a constant times \(n e^{-at}(C' D e^{-at})^{K-1}\), and, after division by \(x\), by
\[
 O_{a,B,A,K}\bigl((\log n)^{K-1} n^{1/2-K\gamma}\bigr)=O(n^{-\delta}).
\]
Here the uniform bound uses \(aK>1\) and the monotone decrease, for large \(n\), of \((1+t)^{K-1}e^{-(aK-1)t}\) to the right of \(\log n-A\).

For every fixed \(k<K\), (4) shows that the coefficient of the original fugacity polynomial differs by \(O_k(n^{-\delta}x)\) from that of \((1+z h(t))^n\). All such low coefficients are bounded; the \(k\)-th logarithm coefficient is a polynomial in the first \(k\) coefficients of a series with constant term 1. Hence the low logarithm coefficients differ by \(O_k(n^{-\delta}x)\) as well. For the product polynomial, the first logarithm coefficient is \(nh(t)=2x+O(x e^{-3t})\), and each fixed \(k\ge2\) coefficient is \(O_k(xe^{-(k-1)t})\). Together with (6), this is the claimed logarithm approximation, hence (1).

For (2), positivity and the bounded value at \(z=2\) give
\[
 \sum_{k>L}[z^k]Z_Q(t,z)\le 2^{-L}(Z_Q(t,2)-1)
                          =O(2^{-L}x),
\]
and the same is true for the product weights. Use (4) for \(k\le L\), then let \(n\to\infty\) followed by \(L\to\infty\), to get the uniform little-oh. Dividing by the respective normalizing constants changes the sum of absolute differences by at most another copy of its original bound, since both constants are at least 1. Under the product law the support is binomial with occupation probability \(h(t)/(1+h(t))\), which gives the claimed Poisson limit. Finally, the strictly decreasing continuous \(Z_Q(t)\) tends to 1 at infinity and diverges as \(t\downarrow0\). At the leading expression on the right of (3), plug (1) into \(\log Z_Q\). Shifting that expression by \(\pm C n^{-\delta}\) brackets the target \(\log(1+\epsilon_n)\) for a fixed large \(C\), uniformly for \(0<\epsilon_n\le E\).

## 4. Consequence for canonical codifferent smoothing

Let \(n\) be a power of 2, \(R=\mathbb Z[\zeta_{2n}]\), and \(I=R^\vee\), the trace codifferent. Use the all-embeddings Euclidean convention, with each pair of complex embeddings counted twice. The Euclidean dual of \(\sigma(I)\) is \(\sigma(R)\), since the codifferent is conjugation-invariant. The canonical power vectors \(\sigma(\zeta_{2n}^j)\), \(0\le j<n\), are orthogonal and have norm \(\sqrt n\). This follows from the sum over the odd residue classes modulo \(2n\). Each entry of their unnormalized complex embedding matrix has modulus one.

For positive widths \(w_i\) equal within conjugate pairs, define \(m=(1/n)\sum_i w_i^2\) and assume
\[
 \min_i w_i^2\ge a m,\qquad \frac1n\sum_i w_i^4\le B^2m^2
\]
with the previous fixed \(a>1/2\) and \(B\). The dual Gaussian mass at widths \(s w_i\) is \(Z_Q(\pi n m s^2)\) for \(Q=U^*\operatorname{diag}(w_i^2/m)U\), where \(U\) is the unitary normalized embedding matrix. This is a real matrix by conjugate pairing, has diagonal 1, spectrum \(w_i^2/m\), and \((Q^2)_{jj}=(1/n)\sum_i w_i^4/m^2\). Define \(\eta_\epsilon(I;\mathbf w)\) as the least \(s\) for which the nonzero dual mass is at most \(\epsilon\). Then
\[
  \pi n m\,\eta_\epsilon(I;\mathbf w)^2
       =\log\!\left(\frac{2n}{\log(1+\epsilon)}\right)+O(n^{-\delta}).
\]
This is also a formula for a principal dual ideal after absorbing the absolute values of its generator's embeddings into \(w_i\), whenever the same conditions hold on the resulting widths.

At fixed positive \(\epsilon\) this gives the exact root-mean-square scale \(\sqrt{\log n/(\pi n)}\); at \(\epsilon=n^{-d}\) with fixed \(d>0\) it becomes \(\sqrt{((1+d)\log n+\log2+o(1))/(\pi n)}\). For \(\epsilon=e^{-c n}\) with fixed \(c>0\) the scale is instead constant and no order improvement is claimed.

## 5. Sharpness and a cyclotomic obstruction to extending the formula

**The half-gap is sharp for the general matrix class.** For even \(n\), repeat a two-site block with diagonal 1 and off-diagonal \(-(1-a)\). At \(a=1/2\) each block has six vectors of squared energy 1: four signed singletons and the two equal-sign pairs; all others have energy greater than 1. Thus \(\log Z_Q(\log n+u)\to3e^{-u}\), not \(2e^{-u}\). At fixed \(0<a<1/2\) even the two pair vectors of energy \(2a\) alone make \(Z_Q(\log n+u)\) diverge.

**Failure without the premise also occurs in the actual dyadic geometry.** Let \(S\) be signed cyclic shift on the \(n\) power coordinates, representing multiplication by \(\zeta_{2n}\), so \(S^n=-I\). For \(n\ge4\), put \(J=S^{n/4}\), \(X=(J+J^{-1})/\sqrt2\), and \(Q_\beta=I-\beta X\), \(0<\beta<1\). Then \(X^2=I\), the canonical eigenvalues of \(X\) are \(+1,-1\) with equal multiplicities, and the corresponding width squares \(1\pm\beta\) respect conjugate pairs. The coordinates split into \(n/4\) identical signed four-cycles. In one block at \(\beta_* = 1/\sqrt2\), the energy is
\[
 q_*(v)=\sum_{i=0}^3 v_i^2-(v_0v_1+v_1v_2+v_2v_3-v_3v_0).
\]
It is positive integral; energy 1 requires ordinary squared length at most \(1/(1-1/\sqrt2)<4\). There are eight signed singletons, eight pairs on one cycle edge with the preferred sign, and eight three-site paths satisfying both edge signs. These are all 24 energy-one vectors. Therefore \(\log Z_{Q_*}(\log n+u)\to6e^{-u}\).

More precisely, for \(\beta_n=\beta_*+c/\log n\) with fixed real \(c\), the three kinds have energies \(1,1-\sqrt2 c/\log n,1-2\sqrt2 c/\log n\). All other nonzero vectors have \(q_*\ge2\); because \(\|X\|=1\) and \(Q_*\succeq (1-\beta_*)I\), their mass in a block is \(O(e^{-7t/4})\) for large \(n\) and \(t\ge1\), by comparing with the convergent \(q_*\)-Gaussian sum. This gives the different limiting phase
\[
 \log Z_{Q_{\beta_n}}(\log n+u)\ \longrightarrow\
  2e^{-u}\bigl(1+e^{\sqrt2 c}+e^{2\sqrt2 c}\bigr).
\]
The example shows why equal diagonal and bounded spectral condition number alone do not force the singleton formula. It does not determine the optimal sufficient spectral bound for the dyadic subclass.

## 6. Relationship to prior work and limits

[Peikert–Regev–Stephens-Davidowitz, Lemma 6.9](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) proves a geometric-mean-width sufficient bound for any ideal and any number field, using the ideal norm and AM–GM. The present result is narrower, and improves the dimension dependence in the indicated family at bounded or inverse-polynomial target error; it does not replace the general volume lemma or change the worst-case-to-average-case reduction. [Regev–Stephens-Davidowitz, Theorems 1.2 and 1.6](https://arxiv.org/abs/1611.05979) bound the Gaussian mass of stable lattices at a general \(\log n\) reciprocal-width scale, and compare exactly with \(\mathbb Z^n\) at very extreme scales. An irreducible rational orthogonal automorphism makes the determinant-normalized dyadic ideal stable (the canonical filtration is isometry-invariant). The result here resolves a different, intermediate-window asymptotic in a restricted shape class, not the general exact reverse Minkowski conjecture. The tree-graph estimate itself is prior work, not claimed here.

The repository's earlier _Elliptical smoothing optimizers_ concerns shape extrema for a fixed lattice in the large-width limit; _Ramified ideal smoothing_ treats a different ramified ideal family and its exact enumerators. A recent [theta-dimension factorization paper](https://eprint.iacr.org/2026/2028) concerns exactly block-diagonal relative coordinates and fixed-coset theta identities. The theorem above allows dense coupled coefficient matrices; exact block factorization is used only for the explicit boundary examples. The literature check is not a priority claim.

The adjacent script checks finite algebra and small generated block/dense examples only. It reports 60,238 exact checks and 519 numerical checks. The uniform control in growing dimension is supplied by the proofs, not inferred from the checks.
