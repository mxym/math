# The collective-unitary logarithmic-negativity rate of every bipartite spectrum

**Written analytic proof; not Lean-formalized or externally peer reviewed.**
The matrix Bernstein inequality [T, Theorem 1.4] is the principal external probabilistic input. The ancillary exact checks do not replace this theorem or the unbounded argument below. All logarithms are natural.

## 1. Statement, operation class, and relation to prior work

All logarithms are natural; rates in bits are obtained by dividing by $\log2$.

Let $2\le m\le n$ be fixed integers and let $\rho$ be any density matrix on $\mathbb C^m\otimes\mathbb C^n$. Write $p=(p_1,\ldots,p_{mn})$ for its eigenvalues, allowing zeros. For $k\ge1$, put
\[
 F_k(\rho)=\max_{U\in\mathcal U((mn)^k)}
 \big\|(U\rho^{\otimes k}U^*)^{\Gamma_k}\big\|_1.
 \tag{1}
\]
Here the tensor factors are grouped as $A^k:B^k$, of dimensions $m^k:n^k$, and $\Gamma_k$ transposes the entire $B^k$ factor in a product basis. The optimization allows arbitrary global unitaries on the existing space, but no additional ancilla, conditioning, measurement, or discarded subsystem. The maximum exists by compactness and continuity. Define the maximal logarithmic negativity by $E_k=\log F_k$, using the trace-norm convention of [VW], rather than the unlogged negativity $(F_k-1)/2$.

**Theorem 1 (exact rate).** For every such state, including rank-deficient states, the limit exists and equals
\[
 \boxed{\displaystyle
 \lim_{k\to\infty}\frac{E_k}{k}
 =\min_{1\le\alpha\le2}
 \frac{\log m+(\alpha-1)\log n+
       \log\!\sum_i p_i^\alpha}{\alpha}.}
 \tag{2}
\]
The value at $\alpha=1$ is $\log m$. In terms of the Renyi entropy $S_\alpha(p)=(1-\alpha)^{-1}\log\sum_i p_i^\alpha$, the numerator for $\alpha>1$ is $\log m+(\alpha-1)(\log n-S_\alpha(p))$.

**Corollary 2 (balanced systems).** If $m=n=d$, then
\[
 \lim_{k\to\infty}\frac{E_k}{k}
 =\frac12\log\bigl(d^2\operatorname{Tr}\rho^2\bigr)
 =\log d-\frac12S_2(\rho).
 \tag{3}
\]
For every $2\le m\le n$, the rate in (2) is zero exactly for the maximally mixed state; every other state has a positive rate.

This determines a regularized unitary-orbit entanglement measure, not a distillable-entanglement rate and not a local-operation protocol. It also does not give an exact one-copy maximum. Recent work [AMRS, v2] studies finite-dimensional negativity-from-spectrum bounds. Kondra et al. [K, Supplemental Lemma 6] already show finite-copy failure of absolute separability away from the maximally mixed state. Thus qualitative activation is not claimed as new here. The claim established below is the exact collective logarithmic-negativity exponent, including unequal local dimensions and every spectrum. Literature screening is not an exhaustive priority certification. No resolution of APPT=AS or of the unrestricted finite-copy APPT purity conjecture is asserted.

## 2. A finite-dimensional spectral envelope

For this section fix $2\le a\le b$, write $N=ab$, and let $\lambda_1\ge\cdots\ge\lambda_N\ge0$ sum to one. Define
\[
 L_r=\sum_{i=1}^r\lambda_i,\qquad
 w_r=\min\{a,\sqrt{N/r}\},\qquad
 T_{a,b}(\lambda)=\max_{1\le r\le N}w_rL_r.
 \tag{4}
\]
Let $F_{a,b}(\lambda)$ be the maximum trace norm of the partial transpose along the corresponding global unitary orbit. Also let $H_N=\sum_{r=1}^N1/r$.

**Theorem 3 (one-shot bounds).** Every spectrum satisfies
\[
 \frac{T_{a,b}(\lambda)}{12\log(8N)}
 \le F_{a,b}(\lambda)\le H_NT_{a,b}(\lambda).
 \tag{5}
\]
In particular, the envelope approximates the logarithm of the orbit optimum up to $O(\log\log N)$, uniformly over spectra and aspect ratios. This does not assert a constant-factor approximation for the unlogged negativity.

### 2.1 Duality and the upper envelope

Partial transpose is an involution, preserves the Hilbert--Schmidt norm, and is self-adjoint for the trace pairing. For a Hermitian matrix $X$,
\[
 \|X\|_1=\max_{H=H^*,\,\|H\|_\infty\le1}\operatorname{Tr}(HX).
 \tag{6}
\]
If $H$ is such a contraction, then
\[
 \|H^\Gamma\|_2\le\sqrt N,\qquad \|H^\Gamma\|_\infty\le a.
 \tag{7}
\]
For the second inequality, take any unit vector $v$ with Schmidt coefficients $s_j$. Its partially transposed rank-one projector has eigenvalues $s_j^2$ and $\pm s_i s_j$, so its trace norm is $(\sum_j s_j)^2\le a$. Consequently
\[
 |\langle v,H^\Gamma v\rangle|
 =|\operatorname{Tr}H(|v\rangle\langle v|)^\Gamma|\le a.
\]
Taking the supremum over $v$ proves (7). If $s_i(H^\Gamma)$ are the decreasing singular values, (7) implies $s_i(H^\Gamma)\le w_i$. The singular-value trace inequality and (6) therefore give
\[
 F_{a,b}(\lambda)\le\sum_i\lambda_iw_i
 \le\sum_i\frac{L_iw_i}{i}\le H_NT_{a,b}(\lambda).
 \tag{8}
\]
The middle step uses the ordering, $i\lambda_i\le L_i$.

### 2.2 A sharper Renyi family of upper bounds

For $1<\alpha\le2$, put $q=\alpha/(\alpha-1)\ge2$. From (7),
\[
 \|H^\Gamma\|_q^q\le a^{q-2}\|H^\Gamma\|_2^2\le a^{q-2}N.
\]
Holder's inequality in (6) yields
\[
 F_{a,b}(\lambda)\le
 \biggl(a\,b^{\alpha-1}\sum_i\lambda_i^\alpha\biggr)^{1/\alpha}.
 \tag{9}
\]
At $\alpha=1$ the same formula is the bound $F_{a,b}\le a$. Thus (9) holds on the whole closed interval $[1,2]$. There is no full-rank assumption.

## 3. Projections with a small partial-transpose norm

We prove the lower bound in (5) by constructing a projection of rank at least $r$. The rank need not equal $r$; increasing the rank only increases the mass $L_r$ used later.

Set $J=\lfloor b/a\rfloor$ and $N_0=a^2J$. Decompose the first $aJ$ coordinate directions of the second factor into $J$ disjoint blocks of dimension $a$. Let $I_0$ project onto $\mathbb C^a\otimes\mathbb C^{aJ}$. Since $b/a\ge1$,
\[
 N/2\le N_0\le N.
 \tag{10}
\]
No divisibility assumption on $b$ is needed.

Let $\omega=\exp(2\pi\mathrm i/a)$. For $0\le j<J$ and $0\le u,v<a$, define
\[
 |\phi_{juv}\rangle
 =\frac1{\sqrt a}\sum_{t=0}^{a-1}\omega^{ut}
 |t\rangle\,|ja+(t+v\bmod a)\rangle.
 \tag{11}
\]
These $N_0$ vectors form an orthonormal basis of the range of $I_0$. Indeed different blocks or shifts are orthogonal, and for the same block and shift the inner products are $a^{-1}\sum_t\omega^{(u'-u)t}=\delta_{u,u'}$.

Index them by $i$, and put $P_i=|\phi_i\rangle\langle\phi_i|$ and $W_i=P_i^\Gamma$. Each vector is maximally entangled inside its coordinate $a\times a$ block. The partial transpose of the standard Bell projector is the swap operator divided by $a$; changing Bell vectors conjugates this matrix by a unitary. Hence, writing $I_j$ for the identity on the corresponding product block,
\[
 \|W_i\|_\infty=1/a,\qquad W_i^2=I_j/a^2,
 \qquad \sum_iW_i=I_0,\qquad\sum_iW_i^2=I_0.
 \tag{12}
\]
The last equality counts $a^2$ Bell vectors per block. The third follows from $\sum_iP_i=I_0$ and $I_0^\Gamma=I_0$. All statements hold for composite $a$ as well as prime $a$.

Assume first $1\le r\le N_0/8$. Choose independent Bernoulli variables $\xi_i$ with parameter $p_0=4r/N_0\le1/2$. The random matrix
\[
 P=\sum_i\xi_iP_i
\]
is an orthogonal projection, because its rank-one summands are mutually orthogonal. Its rank $K=\sum_i\xi_i$ has expectation $4r$ and variance at most $4r$. Chebyshev's inequality gives
\[
 \Pr\{K<r\}\le\frac4{9r}\le\frac49.
 \tag{13}
\]
On the $N_0$-dimensional range of $I_0$, set
\[
 Y=P^\Gamma-p_0I_0=\sum_iX_i,\qquad X_i=(\xi_i-p_0)W_i.
\]
The summands are independent, centered, self-adjoint, satisfy $\|X_i\|_\infty\le1/a$, and by (12) have variance parameter
\[
 \left\|\sum_i\mathbb E X_i^2\right\|_\infty
 =p_0(1-p_0)\le p_0.
 \tag{14}
\]
Apply the self-adjoint matrix Bernstein bound [T, Theorem 1.4] to $Y$ and $-Y$, then use the union bound:
\[
 \Pr\{\|Y\|_\infty\ge t\}
 \le 2N_0\exp\left(-\frac{t^2}{2(p_0+t/(3a))}\right).
 \tag{15}
\]
This is an application of a proved external theorem, not an inference from sampled matrices.

Put $L=\log(8N_0)>1$ and $t=2\sqrt{p_0L}+2L/a$. With $x=\sqrt{p_0L}$ and $y=L/a$, the exact identity
\[
 t^2-2L\bigl(p_0+t/(3a)\bigr)
 =2x^2+\frac{20}3xy+\frac83y^2\ge0
 \tag{16}
\]
shows that the right side of (15) is at most $1/4$. Combining (13) and (15), the probability that either desired condition fails is at most $4/9+1/4=25/36<1$. There consequently exists a projection with $K\ge r$ and $\|P^\Gamma\|_\infty\le p_0+t$.

Since $p_0\le1$ and $L\ge1$,
\[
 p_0+t\le 3L\sqrt{p_0}+2L/a
 \le 12\log(8N)\max\{\sqrt{r/N},1/a\}.
 \tag{17}
\]
For clarity, $\sqrt{p_0}=2\sqrt{r/N_0}\le2\sqrt2\sqrt{r/N}$, and $6\sqrt2+2<12$. Thus the constants in (17) are dimension independent.

## 4. Completing the finite-dimensional lower bound

For a rank-$K$ projection supplied by Section 3, choose a global unitary so that $\sigma=U\operatorname{diag}(\lambda)U^*$ has its $K$ largest eigenvalues on the range of $P$. This is possible by extending orthonormal bases; it neither modifies the spectrum nor appends or discards a system. Let $c=\|P^\Gamma\|_\infty>0$. The matrix $H=P^\Gamma/c$ is a Hermitian contraction, so (6) and the trace-pairing identity give
\[
 \|\sigma^\Gamma\|_1
 \ge\operatorname{Tr}(\sigma^\Gamma P^\Gamma)/c
 =\operatorname{Tr}(\sigma P)/c
 =L_K/c\ge L_r/c
 \ge\frac{w_rL_r}{12\log(8N)}.
 \tag{18}
\]
This proves the required lower bound for $r\le N_0/8$.

If $r>N_0/8$, then (10) gives $w_r\le\sqrt{N/r}<4$, hence $w_rL_r\le4$. Every partial transpose of a density matrix has trace one, and therefore trace norm at least one. Thus (18), with its last lower bound, follows trivially in this range as well, since $12\log(8N)>4$. This also handles the cases where $N_0<8$ and no positive integer belongs to the small-$r$ range. Taking the maximum over all $r$ proves (5).

## 5. Tensor powers and spectral types

Let $s$ denote the number of positive eigenvalues of $\rho$, and restrict distributions below to that support. For a probability vector $q$, write
\[
 H(q)=-\sum_iq_i\log q_i,\qquad
 D(q\|p)=\sum_iq_i\log(q_i/p_i),
 \tag{19}
\]
using $0\log0=0$.

**Lemma 4 (type size).** If $kq_i$ are integers summing to $k$, the corresponding type has size
\[
 r_q=\frac{k!}{\prod_i(kq_i)!},\qquad
 (k+1)^{-s}e^{kH(q)}\le r_q\le e^{kH(q)}.
 \tag{20}
\]
For a self-contained proof, consider multinomial sampling with probabilities $q$. The probability of its own type is $r_q e^{-kH(q)}$, which is at most one. This proves the upper bound. That type is a mode: for any other counts $h_i$, its probability divided by that of counts $kq_i$ is
\[
 \prod_i\frac{(kq_i)!}{h_i!}(kq_i)^{h_i-kq_i}.
\]
The factors $k^{kq_i-h_i}$ have canceled. Each displayed factor is at most one, by comparing the factorial factors with $kq_i$. If $q_i=0$ but $h_i>0$, the competing probability is zero and can be discarded; coordinates with both counts zero contribute one. Since there are at most $(k+1)^s$ types, the modal probability is at least $(k+1)^{-s}$. This proves the lower bound.

Every eigenvalue in type $q$ equals $\exp(k\sum_iq_i\log p_i)$, so the total eigenvalue mass in that type is at least
\[
 (k+1)^{-s}e^{-kD(q\|p)}.
 \tag{21}
\]
The sum of the largest $r_q$ eigenvalues of $\rho^{\otimes k}$ is no smaller than the mass of this particular type. Applying (18) in dimensions $a=m^k,b=n^k$ and using the upper bound on $r_q$ in (20), we obtain
\[
 F_k(\rho)\ge
 \frac{\exp\{k g(q)\}}{12\log(8(mn)^k)(k+1)^s},
 \quad
 g(q)=\min\!\left\{\log m,\frac{\log(mn)-H(q)}2\right\}-D(q\|p).
 \tag{22}
\]
No assertion is made that a full type consists of exactly the largest eigenvalues. Only the elementary maximal-prefix comparison is used.

Every distribution $q$ on the positive support is a limit of types $q^{(k)}$ with denominator $k$. Both $H$ and $D(\cdot\|p)$ are continuous on this simplex. The logarithm of the denominator in (22), divided by $k$, tends to zero. Hence
\[
 \liminf_{k\to\infty}\frac{\log F_k}{k}\ge\max_q g(q).
 \tag{23}
\]
On the other hand (9), applied to tensor powers, gives for every $1\le\alpha\le2$
\[
 \limsup_{k\to\infty}\frac{\log F_k}{k}\le h(\alpha),
 \quad
 h(\alpha)=\frac{A+(\alpha-1)B+\log Z(\alpha)}\alpha,
 \tag{24}
\]
where $A=\log m$, $B=\log n$, and $Z(\alpha)=\sum_{p_i>0}p_i^\alpha$.

## 6. Exact matching of the variational bounds

Let $\delta=B-A\ge0$ and define the escort distribution
\[
 q_{\alpha,i}=p_i^\alpha/Z(\alpha),\quad 1\le\alpha\le2.
 \tag{25}
\]
Direct differentiation on the positive support gives
\[
 h'(\alpha)=\frac{\delta-H(q_\alpha)}{\alpha^2},\qquad
 \frac{d}{d\alpha}H(q_\alpha)
 =-\alpha\operatorname{Var}_{q_\alpha}(\log p_i)\le0.
 \tag{26}
\]
These formulas remain valid when some original eigenvalues are zero because all differentiation occurs on their fixed positive support.

If $H(p)\le\delta$, then $h$ is nondecreasing and its minimum is $h(1)=A$. Taking $q=p$ gives $g(p)=A$.

If $H(q_2)\ge\delta$, then $h$ is nonincreasing and its minimum is $h(2)$. In this case
\[
 g(q_2)=\frac{A+B-H(q_2)}2-D(q_2\|p)
       =\frac{A+B+\log Z(2)}2=h(2).
 \tag{27}
\]

In the remaining case $H(q_2)<\delta<H(p)$, continuity gives $\alpha_*\in(1,2)$ with $H(q_{\alpha_*})=\delta$. It minimizes $h$ by (26). If the positive eigenvalues are not all equal, the variance in (26) is positive, so this parameter is unique. When all are equal, the strict intermediate case cannot occur. Write $\ell_\alpha=\sum_iq_{\alpha,i}\log p_i$. Since
\[
 H(q_\alpha)=-\alpha\ell_\alpha+\log Z(\alpha),\quad
 D(q_\alpha\|p)=(\alpha-1)\ell_\alpha-\log Z(\alpha),
\]
substitution at $H(q_{\alpha_*})=\delta$ yields
\[
 g(q_{\alpha_*})=A-D(q_{\alpha_*}\|p)=h(\alpha_*).
 \tag{28}
\]
Boundary equalities are covered by either endpoint case. Equations (23)--(28) match the lower and upper bounds, prove existence of the limit, and prove Theorem 1. They also show directly that
\[
 \max_q g(q)=\min_{1\le\alpha\le2}h(\alpha).
 \tag{29}
\]
No unproved exchange of minimization and maximization is used.

When $m=n=d$, $\delta=0$ and $H(q_2)\ge0$, so (27) proves Corollary 2. In general, if $\rho$ is maximally mixed, every unitary fixes it, so $F_k=1$. Conversely, if $p$ is not uniform on all $mn$ entries, then $H(p)<\log(mn)$; using $q=p$ in (23) gives the strictly positive lower bound
\[
 R\ge\min\{\log m,(\log(mn)-H(p))/2\}>0.
 \tag{30}
\]

## 7. Consequences and limits of the conclusion

For a pure input the rate is $\log m$, as it must be because a global unitary can map a pure vector to a maximally entangled vector. For a state uniform on a support of size $r$, (2) reduces to
\[
 R=\min\{\log m,\tfrac12\log(mn/r)\}.
\]
For general unequal dimensions an interior escort parameter may be essential; one cannot replace (2) merely by the minimum of its $\alpha=1$ and $\alpha=2$ endpoint values.

An exact interior example occurs on $\mathbb C^2\otimes\mathbb C^8$. Put $v=2^{4/3}$ and take
\[
 p=\frac{(v,1,1,1,1,0,\ldots,0)}{v+4},
 \tag{31}
\]
with eleven zero entries. At $\alpha=3/2$, $v^{3/2}=4$, so the escort law is $(1/2,1/8,1/8,1/8,1/8)$. Its entropy is $2\log2=\log(8/2)$. Strict decrease in (26) proves that $\alpha_*=3/2$ is the unique minimizer, and the exact rate is
\[
 R=\frac{11}{3}\log2-\log(4+2^{4/3}).
 \tag{32}
\]
It is strictly smaller than both endpoint values. No numerical optimizer is used to establish this example.


In the balanced qutrit example with spectrum $(3,1,1,1,1,1,1,1,1)/11$, whose single-copy APPT property is proved in the preceding project, (3) gives
\[
 R=\tfrac12\log(153/121)>0.
\]
Thus the orbit has zero one-copy logarithmic negativity but positive collective rate. The qutrit purity theorem is not used in the proof of Theorem 1; it only supplies a previously certified example. Rate measured with base-two logarithms is obtained by dividing every displayed rate by $\log2$.

The theorem is existential over unrestricted global unitaries. It does not supply polynomial-size circuits or a local entanglement-distillation protocol. It does not prove that Haar-typical unitaries attain the optimum. The random selection in Section 3 is over a Bell basis and is used solely to prove existence. The result addresses all fixed local dimensions and all input spectra in the regularized problem; the exact finite-copy orbit maximum and the original higher-dimensional APPT purity conjecture remain separate problems.

## References

[T] Joel A. Tropp, *User-friendly tail bounds for sums of random matrices*, Foundations of Computational Mathematics 12 (2012), 389--434. Theorem 1.4 (matrix Bernstein), arXiv:1004.4389v7. DOI: 10.1007/s10208-011-9099-z.

[VW] G. Vidal and R. F. Werner, *A computable measure of entanglement*, Physical Review A 65, 032314 (2002), arXiv:quant-ph/0102117.

[AMRS] Jofre Abellanet-Vidal, Guillem Müller-Rigat, Albert Rico and Anna Sanpera, *Bounding the entanglement of a state from its spectrum*, arXiv:2604.02420v2, revised 9 July 2026. Used for problem context and comparison, not as a premise in the rate proof.

[K] Tulja Varun Kondra, Pedro Barrios Hita, Justus Neumann, Hermann Kampermann and Dagmar Bruß, *Fundamental limitations on entanglement extraction from purity*, arXiv:2605.29197v1. Supplemental Lemma 6 gives prior finite-copy activation. Used for attribution, not as a premise in the rate proof.
