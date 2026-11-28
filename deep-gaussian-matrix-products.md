# Exact Gaussian approximation for products of arbitrarily many Gaussian matrices

For each member of a sequence, take a finite chain of independent real
Gaussian matrices with iid \(N(0,1)\) entries and shapes
\[
 p\times d_1,\ d_1\times d_2,\ \ldots,\ d_k\times q.
\]
The number \(k\) of inner widths, like every width, can vary arbitrarily
along the sequence. Let \(P\) be the law of the product divided by
\(\sqrt{\prod_{i=1}^k d_i}\), and \(Q\) the law of an iid standard Gaussian
\(p\times q\) matrix. Reverse and transpose the chain if necessary so
\(p\le q\). Write \(a=\sum_{i=1}^k d_i^{-1}\).

**Theorem.** If \(p,q\to\infty\), put \(\rho=pq a\). For
\(\rho\to\gamma\in[0,\infty]\),
\[
               \operatorname{TV}(P,Q)\longrightarrow
                    2\Phi(\gamma/4)-1,                                \tag{1}
\]
with value one at infinity. If \(p\ge1\) is fixed and \(q\to\infty\), put
\(\lambda=q a\). For \(\lambda\to l\in(0,\infty)\), the limit is
\[
 F_b\!\left(\frac{b(1+l)\log(1+l)}{l}\right)
 -F_b\!\left(\frac{b\log(1+l)}{l}\right),\qquad b=p(p+1)/2,             \tag{2}
\]
where \(F_b\) is the \(\chi_b^2\) CDF. The limits at \(l=0,\infty\)
are zero and one respectively. No assumption on the chain length or
ratios between inner widths is made. In the first regime a necessary
and sufficient condition for Gaussian approximation in TV is
\(pq\sum_i d_i^{-1}\to0\); checking each layer separately against
\(pq\) does not suffice for a growing chain. For example, when
\(p=q=n\), \(k=n\), and every \(d_i=n^3\), each layer exceeds
\(pq\) by a growing factor, yet the TV limit is \(2\Phi(1/4)-1>0\).

[Li–Woodruff, Theorem 1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX/RANDOM.2021.35)
bound TV above by an absolute constant times
\(\sum_i\sqrt{pq/d_i}\) under \(d_i\ge\max(p,q)\) and equal first
and last inner widths. Their lower condition scales as
\(C_2^r/[\sqrt{\max(p,q)}\min(p,q)^{3/2}]\) for \(a\), with
\(r=k+1\), under the same shape hypotheses. Their proof of the lower
bound treats constant length. The [fixed-length TV result](fixed-length-gaussian-matrix-products.md) gives
(1)–(2) when \(k\) is fixed. Here the new estimates replace every use of
fixed length by the accumulated inverse width; in particular they do
not take a union over layers. The scalar product law used below already
appears in [Hanin–Nica, Eq. (9)](https://arxiv.org/html/1812.05994v1);
that paper studies the norm of a given vector, not the TV law of
all matrix entries. [Hanin–Paouris](https://arxiv.org/abs/2005.08899)
treat singular values and Lyapunov exponents of deep Gaussian products.
The present result concerns an abstract statistical comparison only.

## 1. Covariance process, simultaneous moment bounds

Let \(W_i=G_iG_i^T/d_i\) with independent standard Gaussian matrices
\(G_i\) of shape \(p\times d_i\). Write \(E_i=W_i-I_p\),
\[
 S_0=I_p,\quad S_i=S_{i-1}^{1/2}W_iS_{i-1}^{1/2},\quad
 X_i=S_i-I_p,\quad U_i=\sum_{j\le i}E_j,\quad V_i=X_i-U_i .
 \tag{3}
\]
Conditionally on \(S_k\), the output has \(q\) independent
\(N(0,S_k)\) columns. Indeed, conditional on any prefix of the chain,
the implemented Gaussian columns have its scatter as covariance;
the next normalized scatter thus has exactly the congruence transition
(3). This does not equate noncommuting products of the \(W_i\)'s.
If any \(d_i<p\) the original product has rank \(<p\) and TV is one.
An empty chain of inner widths has \(P=Q\) and is trivial; below assume
there is at least one inner width.

Let \(a_i=\sum_{j\le i} d_j^{-1}\). For \(p a\) sufficiently small
and each fixed \(r\ge1\),
\[
 \mathbb E \max_{j\le i}\|X_j\|_{\rm op}^r+
 \mathbb E \max_{j\le i}\|U_j\|_{\rm op}^r
                       \le C_r(p a_i)^{r/2}.                           \tag{4}
\]
Moreover when \(p\to\infty\) there exist fixed \(C,c>0\) such that,
simultaneously over the entire chain with probability \(1-e^{-cp}\)
(after adjusting \(c\) for large \(p\)),
\[
 \max_i(\|X_i\|_{\rm op}+\|U_i\|_{\rm op})\le C\sqrt{p a},
                         \qquad
 \max_i\|V_i\|_{\rm op}\le C p a.                                       \tag{5}
\]
For each symmetric \(B\) we also have
\[
       \mathbb E\operatorname{tr}(B V_k)^2
                            \le C p a^2\|B\|_{\rm F}^2.                 \tag{6}
\]
Constants in (4)–(6) do not depend on \(k\) or the individual widths.

For a unit \(v\), \(v^T S_j v/v^T S_{j-1}v\) has law
\(\chi^2_{d_j}/d_j\) independent of the past, by the Gaussian projection
of \(S_{j-1}^{1/2}v\). The forms along this particular direction
are positive almost surely, recursively. Thus the successive log ratios
are independent. For \(L_d=\log(\chi_d^2/d)\),
\(\log\mathbb E e^{t L_d}=\log\Gamma(d/2+t)-\log\Gamma(d/2)-t\log(d/2)\).
In particular \(-C/d\le \mathbb E L_d\le-c/d\),
\(\operatorname{Var}(L_d)\le C/d\), and
\[
       \log\mathbb E e^{t(L_d-\mathbb E L_d)}\le C t^2/d
                                      \quad(|t|\le d/4).
 \tag{7}
\]
These bounds follow from \(\psi(x)=\log x-1/(2x)+O(x^{-2})\),
strict Jensen for the finitely many small widths, and
\(\psi_1(x)=\sum_{m\ge0}(x+m)^{-2}=x^{-1}+O(x^{-2})\).
The independent summands \(v^TE_jv\) have the same centered mgf
bound by the chi-square formula.

For either centered scalar sum, the exponential supermartingale
with deterministic compensator \(C t^2 a_j\) gives
a maximum tail up to prefix \(i\) of
\(2\exp[-c\min(x^2,x)/a_i]\). Indeed optimize \(t\) of order
\(\min(x,1)/a_i\), which is allowed as
\(\min_{j\le i}d_j\ge1/a_i\). For the uncentered log process the
total drift is at most \(C a_i\). On a \(1/4\)-net of the unit
sphere of size at most \(9^p\), the operator norm of a symmetric
matrix is bounded by twice the maximum absolute quadratic form.
If all net log forms are bounded by \(x\) at all times, the net
forms of \(X_j\) are bounded by \(e^x-1\). For
\(x\ge K\sqrt{p a_i}\) with large fixed \(K\), the net size and the
drift are absorbed in the exponential tail. Integrating for
\(x\le1\) gives (4); for \(x>1\), the \(e^{r x}\) factor incurred
by transforming log forms back is dominated by \(e^{-c x/a_i}\)
when \(p a\) is sufficiently small (for the given \(r\)).
The same net argument gives the first part of (5), without
any factor \(k\).

The increment of \(V_j\) is the martingale difference
\(S_{j-1}^{1/2}E_j S_{j-1}^{1/2}-E_j\).
For fixed \(v\), its quadratic form uses the Wishart linear test
\(B_j=(S_{j-1}^{1/2}v)(S_{j-1}^{1/2}v)^T-vv^T\).
From a past with \(\|X_{j-1}\|_{\rm op}\le C\sqrt{p a}\) we have
\(\|B_j\|_{\rm F}+\|B_j\|_{\rm op}=O(\sqrt{p a})\).
Stop after the first failure of this path bound, including the
unclipped step from a still-good past. For a fixed symmetric
test \(B\) one step satisfies
\[
 \log\mathbb E e^{t\operatorname{tr}(BE_j)}
      \le C t^2\|B\|_{\rm F}^2/d_j\qquad
                                  (|t|\|B\|_{\rm op}\le d_j/4),
 \tag{8}
\]
by diagonalization and the same centered chi-square formula.
The stopped scalar process has total compensator at most
\(C t^2 p a^2\); the maximum bound at level \(L p a\)
uses \(t\) of order \(L/a\), permitted for each fixed \(L\)
when \(p a\to0\). Take \(L\) large and apply the net again.
The stopped and original processes agree on the first event
in (5), proving its second part. For (6) no stopping is needed:
the conditional variance at step \(j\) is
\(2\|S_{j-1}^{1/2}B S_{j-1}^{1/2}-B\|_{\rm F}^2/d_j\).
Using \(\|S^{1/2}-I\|_{\rm op}\le\|S-I\|_{\rm op}\) and (4), its
mean is at most \(C p a_{j-1}\|B\|_{\rm F}^2/d_j\). Orthogonality
of martingale increments and summation give (6).

## 2. Likelihood overlap for \(p,q\to\infty\) at bounded \(\rho\)

Write \(X=X_k,U=U_k,V=V_k\), and let \(\mathcal A\) be the event
in (5). Its probability tends to one. In this regime \(p a=O(1/q)\),
and \(d_j\ge1/a\) so no rank loss occurs. From (4), the second
and fourth Frobenius moments of \(X,U\) are respectively
\(O(p^2a),O(p^4 a^2)\). On the symmetric matrix space the additive
independent covariance of \(U\) is exactly \(2a I\) in the Frobenius
inner product; in particular
\[
 \mathbb E\operatorname{tr}(U^2)=p(p+1)a,\quad
 \mathbb E(\operatorname{tr} U)^2=2pa,\quad
 \mathbb E\sum_{i<j} U_{ij}^2=\binom p2 a.
 \tag{9}
\]
The first and last quantities inside expectations have variance
\(O(p^2 a^2)\). For the first, Gaussian Poincaré and
\(\nabla_{G_j}\operatorname{tr}(U^2)=4 U G_j/d_j\)
give a sum bounded by
\(C\sum_j d_j^{-1}\mathbb E[\|W_j\|_{\rm op}\|U\|_{\rm F}^2]\).
Each expectation is \(O(p^2a)\) by the preceding fourth moment
and the uniform bounded second moment of \(\|W_j\|_{\rm op}\);
the latter follows by the usual scalar chi-square net bound since
\(d_j\ge p\). Projecting to the offdiagonal subspace gives the other
variance bound. These are summed estimates, independent of depth.

Let \(P'\) be the mixture conditional on \(\mathcal A\); its TV
distance to \(P\) is \(o(1)\). Write \(L'\) for its likelihood
relative to \(Q\). For independent covariance copies on the good
events, integrating the two conditional Gaussian likelihoods gives
\(\det(I-XX')^{-q/2}\), by multiplying their combined precision
matrix on both sides by the two respective covariance matrices.
Since \(\|XX'\|_{\rm op}=O(pa)\), its logarithm is
\[
 Z+R,\qquad Z=\tfrac q2\operatorname{tr}(XX'),\qquad
 R=\tfrac q4\operatorname{tr}((XX')^2)+O(p/q^2).
 \tag{10}
\]
Uniformly \(R=O(1)\), since \(p\le q\). Replacing all four factors
by \(U,U'\) changes the second term by \(O(qp(pa)^{5/2})=o(1)\)
on the good events. For fixed \(U\), the additive covariance gives
\(\mathbb E_{U'}\operatorname{tr}(U U' U U')=
a(\operatorname{tr}(U^2)+(\operatorname{tr}U)^2)\).
The conditional Gaussian Poincaré bound is
\(C p^2 a^2\|U\|_{\rm op}^4\), obtained with gradient
\(4 U U' U G_j'/d_j\). By (5), (9) these imply that \(R\) tends
to zero in probability on the good events. For
\(Z_U=\frac q2\operatorname{tr}(UU')\), apply (6) to
\(\operatorname{tr}(V X')+\operatorname{tr}(U V')\), using independence
between the copies, to get
\(\mathbb E|Z-Z_U|^2=O(q^2 p^3 a^3)=o(1)\).

For \(U\) satisfying its good norm bound, the exact Wishart mgfs give,
uniformly for each fixed \(t\),
\[
 \log\mathbb E_{U'}e^{t Z_U}
       =\tfrac{t^2 q^2 a}{4}\operatorname{tr}(U^2)+o(1).
 \tag{11}
\]
Here the first order cancels, and the higher order error is bounded by
\(C_t q^3 (\sum_j d_j^{-2})\|U\|_{\rm op}\operatorname{tr}(U^2)=o(1)\),
since \(\sum_j d_j^{-2}\le a^2\). The leading exponent is bounded
on the good event and tends to \(t^2\gamma^2/4\) by (9).
For \(Z\) also, \(\mathbb E[e^{tZ}{\bf1}_{\mathcal A}{\bf1}_{\mathcal A'}]\)
is bounded for every fixed \(t\). In the primed process stop its
\(X'\) increments after the first failure of the \(X'\) bound from
(5), retaining the first failure increment. Given \(X\) on
\(\mathcal A\), use (8) on
\(B_j=S_{j-1}'^{1/2}X S_{j-1}'^{1/2}\) from each still-good past.
Its norm and squared Frobenius norm are \(O(\sqrt{pa}),O(p^2a)\),
respectively. The exponent compensator from these steps totals
\(O_t(q^2p^2 a^2)\), bounded. On \(\mathcal A'\) the stopped
sum agrees with \(X'\), which proves the desired bound. In
particular no expectation conditions an increment on its own success.

Cauchy–Schwarz, (11) with \(t=2\), and \(\Pr(\mathcal A'^c)=o(1)\)
justify excluding the bad primed events from the \(Z_U\) expectation.
The bounded second exponential moments and the \(L^2\) trace
replacement permit replacing \(Z_U\) by \(Z\); bounded \(R\to0\)
in probability then permits inserting \(e^R\). Thus
\[
                \mathbb E_Q (L')^2\longrightarrow e^{\gamma^2/4}.
 \tag{12}
\]
At \(\gamma=0\) this already proves (1). This argument uses
only the clipped second moment; the untrimmed one need not be finite.

## 3. An asymptotically sufficient rectangle statistic

For \(0<\gamma<\infty\) use the same rectangle statistic as in the
[fixed-length result, §4](fixed-length-gaussian-matrix-products.md):
\[
 T(Y)=\sum_{i<i',\,j<j'}Y_{ij}Y_{i'j}Y_{ij'}Y_{i'j'},\qquad
 N=\binom p2\binom q2 .
\]
Its law under \(Q\), independent of the chain, tends after division
by \(\sqrt N\) to \(N(0,1)\). For completeness this follows from
orthogonal monomials and the fourth moment theorem
[Nualart–Peccati](https://arxiv.org/abs/math/0503598): to contribute
to the fourth moment, each cell must occur evenly. Repeated pairs
give \(3N(N-1)+O(Npq)\): the disjoint-cell contribution has unit
expectation, a fixed rectangle shares a cell with only \(O(pq)\)
others, and the expectation on these exceptional pairs is bounded.
All identical give \(O(N)\), and three distinct rectangles cannot
contribute. For four distinct rectangles at most
four rows and four columns occur. If there are four rows, each is
in precisely two rectangles, whose column pairs must equal for that
row. The row-pair graph is then 2-regular; a doubled edge gives
identical rectangles, and a four-cycle forces the same column pair
around the cycle. Thus four rows and four columns cannot both occur
in this case. The four-distinct count is \(O(p^3q^4+p^4q^3)=o(N^2)\).

Given \(S=S_k\), let \(v=(S_{ii'})_{i<i'}\) and for each column
\(j\) write its products of different row entries as \(v+Z_j\).
The centered \(Z_j\)'s are independent conditionally. Expanding,
\(T=\binom q2\|v\|^2+(q-1)\sum_j v^T Z_j+\sum_{j<j'} Z_j^T Z_{j'}\).
By (5), (9), the first term divided by \(\sqrt N\) tends to
\(\gamma/2\): the error in the squared offdiagonal norm when replacing
\(X\) by \(U\) is \(O(p(pa)^{3/2})=o(p^2 a)\) on the good event.
The second term is negligible in probability in this normalization:
\(\|\operatorname{Cov}(Z_j\mid S)\|_{\rm op}\le\|S\|_{\rm op}^2\)
by the Gaussian quadratic form variance formula, and on the
good event \(\|v\|^2=O(p^2a)\), giving normalized variance \(O(qa)\).
For the last term use \(Y_j=S^{1/2}g_j\) with iid standard \(g_j\)'s
and couple to its counterpart under \(Q\). On symmetric matrices
let \(B_S\) map \(M\) to the offdiagonal upper entries of
\(S^{1/2} M S^{1/2}\). The \(g_jg_j^T-I_p\)'s have covariance \(2I\);
orthogonality over distinct column pairs gives conditional difference
variance \(4\binom q2\|B_S^*B_S-B_I^*B_I\|_{\rm HS}^2\).
The squared norm divided by \(p^2\) tends uniformly to zero on
\(\mathcal A\), by its operator-norm bound \(O(\|S-I\|_{\rm op})\)
and the dimension \(p(p+1)/2\). Thus the normalized statistic
under \(P'\) tends to \(N(\gamma/2,1)\).

The likelihood \(h(z)=\exp(\gamma z/2-\gamma^2/8)\) between
these scalar normals has squared norm \(e^{\gamma^2/4}\),
matching (12). With \(H_M=\min(h,M)\), expand
\(\mathbb E_Q(L'-H_M(T/\sqrt N))^2\). The mixed term is an
expectation under \(P'\), so the limit is the squared
\(L^2(N(0,1))\) norm of \(h-H_M\). First let the dimensions
tend to infinity and then \(M\to\infty\). This yields the TV
distance of the limiting two normal laws, proving (1) at
finite positive \(\gamma\).

## 4. Fixed \(p\) and the infinite endpoints

For fixed \(p\) and bounded \(q a\), the scatter \(YY^T/q\)
is sufficient for the likelihood, as each conditional likelihood
is a function of it. Let \(V_q^*=\sqrt q(W_q^*-I)\) for the
independent last scatter step of width \(q\). Its law tends in
TV to \(N(0,2I_b)\) in Frobenius coordinates
([Bubeck–Ding–Eldan–Rácz, Theorem 7](https://arxiv.org/abs/1411.5713)).
The normalized scatter is
\[
             \sqrt q X+S_k^{1/2}V_q^*S_k^{1/2}.
\]
By (6) on an orthonormal symmetric basis,
\(\sqrt q(X-U)\to0\) in \(L^2\). By the centered Wishart mgf
in each fixed symmetric test direction, \(\sqrt q\,U\) tends
weakly to \(N(0,2l I_b)\) if \(qa\to l\): the degree-two term is
\(qa\|B\|_{\rm F}^2\) and the higher-degree error is
\(O(q^{3/2}a^2)=o(1)\) for fixed \(B\). The last scatter noise
can be replaced in TV by independent \(N(0,2I_b)\), also dropping
its congruence by \(S_k^{1/2}\): (4) gives \(S_k\to I\) in probability,
and finite-dimensional Gaussian densities are TV-continuous at
the identity covariance. Convolution with this fixed nonsingular
Gaussian maps weak convergence of the input laws into TV convergence:
the mixed densities converge pointwise by bounded continuous
testing, and then in \(L^1\) by Scheffé. Thus the scatter limit
under \(P\) is \(N(0,2(1+l)I_b)\) in TV, and under \(Q\) it is
\(N(0,2I_b)\). Comparing the crossing radii gives (2) including
the zero endpoint by continuity. This avoids accumulating any
error over the intermediate scatter steps.

It remains to prove TV tends to one when the relevant \(\rho\)
or \(\lambda\) diverges. Along subsequences with \(a\to0\), retain
a submatrix with unchanged inner widths at an arbitrary fixed positive
critical value, using data processing. For \(p,q\to\infty\), choose
\(p'=\min\{p,\lfloor\sqrt{\gamma_0/a}\rfloor\}\) and
\(q'=\min\{q,\lfloor\gamma_0/(a p')\rfloor\}\); then both
tend to infinity and \(p'q'a\to\gamma_0\). If
\(p'=\lfloor\sqrt{\gamma_0/a}\rfloor\), then \(q\ge p\ge p'\),
so the smaller of the two candidate column counts agrees with
\(\sqrt{\gamma_0/a}\) up to relative \(o(1)\). If \(p'<\lfloor\sqrt{\gamma_0/a}\rfloor\),
then \(p'=p\) and \(pqa\to\infty\) eventually leaves enough columns. For fixed \(p\), keep \(p\)
and retain \(q'=\lfloor l_0/a\rfloor\) columns. The submatrix law
really is a product with the indicated outer sizes, by restricting
the first and last factors. Apply the finite profiles and then
send \(\gamma_0\) or \(l_0\) to infinity.

For subsequences with \(a\) bounded away from zero, the log of the
squared norm of a single output row divided by \(q\) is independent-log
sum with widths \(d_1,\ldots,d_k,q\), by the scalar identity above.
Under \(Q\) this log belongs to \([-q^{-1/4},q^{-1/4}]\) with
probability tending to one. If some inner width stays bounded,
extract a subsequence with one fixed width; its log law has a
bounded density, inherited by convolution with all other terms,
so the shrinking interval has vanishing probability under \(P\).
If all inner widths tend to infinity and \(a\to a_0\in(0,\infty)\),
the sum tends in law to \(N(-a_0,2a_0)\): the log of the gamma
mgf expands at fixed \(t\) as \((t^2-t)/d+O_t(d^{-2})\), and
the errors sum to \(o(1)\). The limiting law has no atom at zero.
If \(a\to\infty\), independent summation of (7) gives mean at
most \(-c(a+1/q)\) and variance \(O(a+1/q)\); the log
therefore tends to minus infinity in probability. These cases
cover all subsequences and prove the last endpoints.

Only the distribution of the real Gaussian chain is compared here;
no finite-field, reduction, sampler, or security conclusion follows.
