# Exact low-rate trace distance of a random affine ensemble

## 1. Model and statement

Let \(G=\mathbb F_2^k\), \(k\ge1\), \(q=2^k\), and
\(\rho_{XE}=\sum_{x\in G}|x\rangle\langle x|\otimes R_x\), where
\(R_x\succeq0\) on one finite-dimensional space and
\(\sum_x\operatorname{tr}(R_x)=1\). There is no condition on the
probabilities or commutation of the \(R_x\). Any smaller finite alphabet
can be embedded into \(G\) by assigning zero blocks to unused points.
For \(a\in G\) set
\[
 \widehat R(a)=\sum_{x\in G}(-1)^{a\cdot x} R_x,\qquad
 s(a)=\|\widehat R(a)\|_1,\qquad
 W=\sum_{a\in G}s(a),\qquad
 \nu(a)=s(a)/W.
\]
We have \(s(0)=1\) and \(0\le s(a)\le1\). Thus \(1\le W\le q\).
Throughout, logarithms and Shannon and Rényi entropies are in bits.

For \(n\) i.i.d. copies, identify the input group with \(G^n\).
For an output length \(r=r_n\ge1\), draw a uniform matrix
\(A\in\mathbb F_2^{r\times kn}\) and uniform \(c\in\mathbb F_2^r\)
independently of each other and of the source, and use
\(f_{A,c}(x)=Ax+c\). Set \(M=2^r\).
Let
\[
 \Delta_{A,c}=\frac12\left\|\rho^f_{Z E^n}
       -\frac{I_M}{M}\otimes\rho_E^{\otimes n}\right\|_1,\qquad
 \overline\Delta_n=\mathbb E_{A,c}\Delta_{A,c}.
\]
The classical public-seed register could equivalently be included in
both states, since direct-sum trace norm gives the same expected metric.
The displacement \(c\) permutes the output labels so the fixed-seed
distance depends only on \(A\); we write \(\Delta_A\).

**Theorem 1.** If \(r_n/n\to R\) and \(0\le R<k-H(\nu)\), then
\[
 \overline\Delta_n
  =\frac{2^{r_n}-1}{2}\left(\frac{W}{q}\right)^n
     \bigl(1+O(2^{-\gamma n})\bigr)
\]
for some \(\gamma>0\) depending on the fixed source and the rate gap.
The relative correction here is nonpositive. If \(R=k-H(\nu)\),
or anywhere below it, the exponent exists and is
\[
 \lim_{n\to\infty}-\frac1n\log_2\overline\Delta_n
       =k-R-\log_2 W.
\]
The family is strongly three-wise independent regardless of the source.
In particular it satisfies the usual pair-collision hypothesis of
leftover hashing. We do not claim that it is optimal among all
three-wise-independent hash ensembles in the presence of arbitrary
quantum side information.

The threshold always makes the asserted exponent nonnegative.
Indeed \(H(\nu)=\log_2 W-\sum_{\nu(a)>0}\nu(a)\log_2 s(a)\ge
\log_2 W\). If \(r=1\), the one-shot expression
\(\overline\Delta_n=\tfrac12(W/q)^n\) holds exactly. Allowing \(r_n=0\)
on a subsequence would give zero error there and is not covered.

## 2. Two elementary Fourier estimates

For \(a=(a_1,\ldots,a_n)\in G^n\), write
\(s_n(a)=\prod_{i=1}^n s(a_i)\). The operator Fourier coefficient of
the product source at \(a\) is
\(\widehat R(a_1)\otimes\cdots\otimes\widehat R(a_n)\); its norm is
\(s_n(a)\), since singular values of a tensor product are the
products of the singular values of the factors.

For a fixed affine map, take the Fourier transform of its output
operator blocks, indexed by \(z\in\mathbb F_2^r\). At \(u\in\mathbb F_2^r\)
it is the input product-source coefficient at \(A^\top u\) multiplied
by the scalar \((-1)^{u\cdot c}\). The uniform-output ideal removes only
the zero frequency: the zero input coefficient is the true marginal.
Fourier inversion with factor \(1/M\), the direct-sum trace formula,
and the triangle inequality thus give
\[
 \Delta_A\le\frac12\sum_{u\ne0}s_n(A^\top u).                 \tag{1}
\]
No injectivity or surjectivity of \(A\) is used. In the other
direction, for any nonzero \(u\), map the output to the single bit
\(u\cdot z\). The ideal bit remains uniform; the distance for this
binary output is exactly \(\tfrac12 s_n(A^\top u)\), since its two
centered operator blocks are opposite copies of half its coefficient
at frequency one. Trace distance cannot increase under this
postprocessing. Therefore
\[
 \frac12\max_{u\ne0}s_n(A^\top u)\le\Delta_A.                 \tag{2}
\]
This is also valid for \(A^\top u=0\): in that case the bit is
constant, giving distance \(1/2\). When \(r=1\) (1) and (2) coincide.

For every nonzero \(u\), \(A^\top u\) is uniform on \(G^n\). For
distinct nonzero \(u,v\), the two images are independently uniform:
\(u,v\) are linearly independent over \(\mathbb F_2\), and the
\(kn\) columns of \(A\) are uniform independent columns. In contrast,
higher independence in the family of these images is neither
assumed nor needed. The *hash evaluations* at up to three distinct
inputs are strongly independent because their augmented vectors
\((x,1)\) are linearly independent over \(\mathbb F_2\): a nontrivial
affine dependence must involve an even number of distinct vectors,
and a two-term dependence would equate the points. This applies
separately to each independent row of \((A,c)\).

Let \(U_n=(M-1)W^n/(2q^n)\). Taking expectations in (1) gives
\(\overline\Delta_n\le U_n\). For any set \(T\subseteq G^n\),
\[
 \overline\Delta_n
 \ \ge\ U_n\,\frac{\nu^{\otimes n}(T)}{1+\mu_T},
        \qquad \mu_T=(M-1)|T|/q^n .                        \tag{3}
\]
To prove this, put \(Y_u=s_n(A^\top u)1_{\{A^\top u\in T\}}\).
For \(t>0\), the number of indices \(u\ne0\) with \(Y_u\ge t\)
has mean \(\mu_t\le\mu_T\) and second moment at most
\(\mu_t+\mu_t^2\) by pairwise independence. Cauchy–Schwarz
bounds the probability of at least one such index below by
\(\mu_t/(1+\mu_t)\) (trivial if \(\mu_t=0\)). Integrating the
tail of the maximum yields
\[
 \mathbb E \max_{u\ne0}Y_u
  \ge \frac{\int_0^\infty\mu_t\,dt}{1+\mu_T}
  =\frac{(M-1)\sum_{a\in T}s_n(a)}{q^n(1+\mu_T)} .
\]
Combine with (2) and \(\sum_{a\in T}s_n(a)=W^n\nu^{\otimes n}(T)\).
Neither higher independence nor nonzero weights on all of \(T\)
are required.

## 3. Prefactor and endpoint exponent

For the strict inequality \(R<k-H(\nu)\), choose \(\epsilon>0\)
with \(R+2\epsilon<k-H(\nu)\). Use
\[
 T_n=\{a\in(\operatorname{supp}\nu)^n:
              -n^{-1}\log_2\nu^{\otimes n}(a)\le H(\nu)+\epsilon\}.
\]
Its cardinality is at most \(2^{n(H(\nu)+\epsilon)}\).
Under \(\nu^{\otimes n}\) the bounded independent summands
\(-\log_2\nu(a_i)\) have mean \(H(\nu)\), so Hoeffding's
inequality gives \(\nu^{\otimes n}(T_n)=1-O(2^{-c_1 n})\)
with \(c_1>0\), or exactly one for constant surprisal.
For all sufficiently large \(n\), \(r_n/n\le R+\epsilon/2\),
and therefore \(\mu_{T_n}=O(2^{-c_2n})\) for \(c_2>0\).
Now (3) and the upper bound prove the prefactor assertion.

At the endpoint let \(\nu_n\) be an \(n\)-type supported
on \(\operatorname{supp}\nu\), differing from \(\nu\) by
\(O(1/n)\) entrywise, and use its full type class \(T_n\).
Apply (3) on this \(T_n\).
The type class mass is at least
\((n+1)^{-q}2^{-nD(\nu_n\|\nu)}=2^{-o(n)}\), as follows from
the multinomial type count and \(D(\nu_n\|\nu)\to0\) on its
fixed support. Also \(|T_n|\le2^{nH(\nu_n)}\), hence
\(\mu_{T_n}\le 2^{o(n)}\) when \(R=k-H(\nu)\).
The multiplicative loss is only subexponential.
As \(n^{-1}\log_2(M-1)\to R\) when \(r_n\ge1\), the exponent
equals \(k-R-\log_2 W\), as claimed.

## 4. Binary form, noncommuting separation, and the Rényi expression

For \(k=1\) let \(s=\|R_0-R_1\|_1\). Then \(W=1+s\) and
\(\nu(1)=s/(1+s)\), so the exponent is
\[
 1-R-\log_2(1+s)=H_{\min}(X|E)-R
\]
up to and including \(R=1-h_2(s/(1+s))\).
The equality follows from the binary guessing identity
\(P_{\rm guess}=(1+s)/2\) and the operational interpretation of
conditional min-entropy. The guessing identity itself follows
by maximizing \(\operatorname{tr}(R_1)+\operatorname{tr}(T(R_0-R_1))\)
over \(0\preceq T\preceq I\), using the positive spectral projector.
This binary specialization includes nonuniform priors and mixed,
noncommuting side-information states.

For a concrete separation choose two equally likely pure conditional
states with vectors
\(|0\rangle\) and \((\sqrt{24}\,|0\rangle+|1\rangle)/5\).
Their overlap is neither zero nor one, hence their projections
do not commute, and \(s=1/5\).
Take \(r_n/n\to1/4\). The strict low-rate inequality is
\(h_2(1/6)<3/4\), equivalent to \(6^{12}<2^9\,5^{10}\).
The resulting exponent \(3/4-\log_2(6/5)\) exceeds \(3/8\)
because \(6^8<2^3\,5^8\). On this same source and at the same rate,
the independence-class exponent in Regula–Cheng Theorem 11 and
Equation (7), for every four-wise-exact collision ensemble, is
\[
 E_{4^*}=\sup_{1\le\alpha\le2}
              \frac{\alpha-1}{\alpha}
                 \bigl(\widetilde H_\alpha^\uparrow(X|E)-R\bigr).
\]
For binary \(X\), data processing of the sandwiched divergence
when forgetting \(E\) implies \(\widetilde H_\alpha^\uparrow(X|E)
\le H_\alpha(X)\le1\). Thus \(E_{4^*}\le3/8\).
This comparison is between actual expected trace-distance
exponents for different ensemble classes, not between different
security criteria or different sources.

There is also an exact connection with Equation (144) of
Regula–Cheng for the uniform binary pure-state subclass.
Suppose \(X\) is uniform and the two pure vector states are
chosen with nonzero, nonunit overlap. After a phase and a basis
change they have the form
\[
 |\psi_\pm\rangle=\sqrt{1-\lambda}\,|0\rangle
                         \ \pm\ \sqrt\lambda\,|1\rangle,
       \qquad 0<\lambda<1/2 .
\]
To see this, take the normalized sum and difference of the two
vectors after making their overlap real and positive; these
are orthogonal. In this form \(s=2\sqrt{\lambda(1-\lambda)}\).
For \(p=(1-\lambda,\lambda)\) and \(\theta=(\alpha-1)/\alpha\),
\[
 \widetilde H_\alpha^\uparrow(X|E)
             =1-H_{1/(1+\theta)}(p),\qquad \alpha>1 .       \tag{4}
\]
Here the optimization minimizes the sandwiched divergence
against \(I_X\otimes\sigma_E\) over density operators
\(\sigma_E\). Restricting to the span of the states does not
hurt, by a quantum channel that fixes both states and maps
the orthogonal complement into this span. The phase-flip symmetry
swapping the two classical labels conjugates the side state by
\(Z=\operatorname{diag}(1,-1)\). Thus the two reference choices
\(\sigma\) and \(Z\sigma Z\) have the same objective.
The convexity of sandwiched trace power for \(\alpha>1\),
or operator convexity of \(T\mapsto T^{-\theta}\) followed
by convexity of the scalar power \(\alpha\) on the two rank-one
blocks, allows averaging these references. One may therefore use
a diagonal reference with entries \(q_i\). Each of the two
rank-one traces then depends on the same positive scalar
\(V=\sum_i p_iq_i^{-\theta}\); the sandwiched trace power
is \(2^{1-\alpha}V^\alpha\).
A Lagrange multiplier (or Hölder) minimizes \(V\) at
\(q_i=p_i^{1/(1+\theta)}/\sum_j p_j^{1/(1+\theta)}\),
with value \((\sum_i p_i^{1/(1+\theta)})^{1+\theta}\).
This gives (4). Here both \(p_i>0\), so no boundary density
operator yields a smaller value.

Let \(u_\theta=\lambda^{1/(1+\theta)}/
(\lambda^{1/(1+\theta)}+(1-\lambda)^{1/(1+\theta)})\).
Writing
\(\theta(\widetilde H_\alpha^\uparrow-R)
=\theta(1-R)-(1+\theta)\log_2\sum_i p_i^{1/(1+\theta)}\),
its derivative in \(\theta\in(0,1)\) is
\(1-R-h_2(u_\theta)\). The number \(u_\theta\) is nondecreasing
in \(\theta\) and at most \(1/2\), so the entropy is at most
\(h_2(u_1)\). Since \(s/(1+s)=2u_1(1-u_1)\ge u_1\), the
range \(R\le 1-h_2(s/(1+s))\) ensures that the objective is
nondecreasing. Its supremum is the limit \(\theta\uparrow1\):
\[
 \sup_{\alpha>1}\frac{\alpha-1}{\alpha}
       \bigl(\widetilde H_\alpha^\uparrow(X|E)-R\bigr)
        =1-R-\log_2(1+s).
\]
This proves that the natural sandwiched-conditional-entropy
counterpart of their Eq. (144) is attained in this subclass and
rate range by the specified strongly three-wise independent
ensemble. It neither settles that expression for general sources
nor implies that \(\alpha=\infty\) is optimal outside this range.

## 5. Full-rank binary quotients and a preprint counterexample

Let \(k=1\), take \(1\le r\le n\), and draw \(A\) uniformly among
rank-\(r\) binary matrices. The row space \(L\) is a uniform
\(r\)-dimensional subspace and \(\ker A=L^\perp\) is a uniform
\((n-r)\)-dimensional subspace. Indeed each \(r\)-space has
the same number of ordered bases, and composing \(A\) with
an invertible output identification changes none of the trace
distances. The output of \(A\) is therefore the same up to
relabeling as the quotient by the uniform kernel.

In this ensemble the \(A^\top u\) for \(u\ne0\) are the nonzero
vectors of \(L\), each occurring once. Each nonzero \(a\in\mathbb F_2^n\)
has inclusion probability \((2^r-1)/(2^n-1)\), by transitivity and
counting all included vectors. Consequently (1) implies for any
binary i.i.d. cq source
\[
 \mathbb E_{\rm full}\Delta_A
    \le \frac{2^r-1}{2(2^n-1)}
            \left[(1+s)^n-1\right],\qquad s=\|R_0-R_1\|_1. \tag{5}
\]
Equality holds for \(r=1\) by (2). This upper bound does not
require the full-rank ensemble to be strongly three-wise
independent.

If \(s>0\) and \(r_n/n\to R\le1-h_2(s/(1+s))\), the
full-rank ensemble has the same exponent as Theorem 1,
and in the strict interval the same prefactor with exponentially
small relative error. To prove this, under unrestricted uniform \(A\)
let \(p_{\rm def}=\Pr(\operatorname{rank}A<r)\).
By union-bounding \(A^\top u=0\) over nonzero \(u\),
\(p_{\rm def}\le (2^r-1)2^{-n}\). The part
\(\mathbb E[\Delta_A1_{\{\operatorname{rank}A<r\}}]\) is at most
\(p_{\rm def}\), since \(\Delta_A\le1\);
relative to the leading quantity \(U_n\) it is at most
\(2/(1+s)^n\). Also \(1-p_{\rm def}=1-O(2^{r-n})\).
For \(s>0\) in the stated interval, \(R<1\), so conditioning
out the deficient part preserves the prefactor in the strict
range and the exponent at the boundary. The latter follows
also when the lower bound is \(U_n2^{-o(n)}\), since the
discarded part is exponentially smaller than \(U_n\).
At \(s=0\) the full-rank error is zero, unlike the unrestricted
ensemble; it is not included in this comparison.

### Hayashi, arXiv:1202.0322v6, Lemma 39

In §VIII-B and Appendix E of the public v6 preprint, take its
phase-state source with \(P_X=(9/10,1/10)\) and a uniform binary
raw symbol \(a\):
\[
 |a:P_X\rangle=(3|0\rangle+(-1)^a|1\rangle)/\sqrt{10}.
\]
Then \(\|R_0-R_1\|_1=3/5\), because the difference has only
off-diagonal entries of magnitude \(3/10\). For \(R=1/100\),
use \(r_n=\lfloor nR\rfloor\) (for sufficiently large \(n\));
the kernel dimension is exactly \(\lceil n(1-R)\rceil\),
as in Lemma 39. Hayashi's \(d'_1\) is the full trace norm to
the uniform product with the actual side marginal, that is
\(2\Delta_A\) in our convention. Its definition and the
quotient interpretation are also explicit in his Lemma 40.
Thus (5) gives the finite inequality
\[
 \mathbb E_{C_{\bf Z}} d'_1
 \ \le\frac{2^{r_n}-1}{2^n-1}\big[(8/5)^n-1\big].            \tag{6}
\]
This alone implies that the \(\liminf\) of its base-two
exponent is at least \(e=99/100-\log_2(8/5)>0\),
and the low-rate full-rank theorem shows the exponent
is exactly \(e\). The strict threshold is
\(h_2(3/8)<99/100\), certified by \(3^{300}5^{500}>2^{1608}\);
positivity follows from \(8^{100}<2^{99}5^{100}\).

On the other hand, Lemma 39 (HTML Equation (151);
v6 PDF Equation (150)) gives, after converting to bits,
\[
 E_{\rm H}=\max_{0\le u\le1/2}
            \frac{u}{2(1-u)}
                   \left[1-R-H_{1-u}(9/10,1/10)\right] .
\]
With \(\theta=u/(1-u)\), the quantity maximized is one-half
of the objective in the pure-state calculation in §4.
The derivative calculation there applies: the order parameter
runs over \([0,1]\), \(u_1=1/4<3/8\) in that calculation,
and \(R<1-h_2(3/8)\). Hence the right-hand side reaches
its maximum at \(u=1/2\). Since
\(H_{1/2}(9/10,1/10)=\log_2(8/5)\), the asserted exponent is
\(e/2<e\). Even without knowing the actual exponent, (6)
already rules out the asserted equality. The change between
the trace-norm and half-trace-norm conventions changes the
error by a factor of two, not its exponent.

This finding is about the publicly accessible arXiv v6 statement.
The next display (HTML (152), PDF (151)) is an inequality for a
different quantity \(\Delta_{d,2}\); it is **not** the equality that
is contradicted here. Its use together with Lemma 39 to conclude
a matching limit has lost that premise. We do not determine the
correct exponent for \(\Delta_{d,2}\), audit the final IEEE typeset
text, or make a claim about an implementation.
