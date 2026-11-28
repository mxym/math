# The lattice phase of classically assisted quantum compression

## 1. Operational input and notation

Let \(p=(p_i)_{i=1}^d\) be the positive eigenvalues of a finite-dimensional source state, counted with multiplicity. A draw \(i\) has law \(p\), and \(S=-\ln p_i\). Let \(H=\mathbb E S\), \(V=\operatorname{Var}(S)>0\). Throughout the proof logarithms are natural except when converting dimension logs to the base-two costs of [FG]. Suppose \(S=b+hZ\) for an integer-valued \(Z\), where \(h>0\) is the maximal lattice span; equivalently, the gcd of all differences of support points of \(Z\) is 1. The anchor \(b\) may be any point of the lattice. Let \(\kappa=\mathbb E Z\), \(\sigma=\sqrt V/h>0\), and \(\beta=\mathbb E[(Z-\kappa)^3]/\sigma^3\). Write \(\phi,\Phi\) for the standard normal density and cdf.

Fix \(F\in(0,1)\), the **root** fidelity \(1-\varepsilon\) of [FG], not its square. Their Theorems 5 and 7 and Lemma 4 give the minimum quantum dimensions on \(n\) copies as
\[
 M_{\rm LO}(n)=\lceil L_n\rceil,\qquad M_{\rm LOCC}(n)=\lceil Q_n\rceil. \tag{1}
\]
Here \(L_n\) is the minimum of \(\sum_x f_x\) and \(Q_n\) is the minimum of \(\sum_x f_x^2\), in both cases over \(0\le f_x\le1\) and \(\sum_x p_x^{(n)} f_x\ge F\); the index \(x\) ranges over all positive eigenvalue strings, \(p_x^{(n)}=\prod_i p_{x_i}\). For LO this fractional program is the usual greedy spectral cutoff followed by rounding up (the fractional last direction has the same eigenvalue as every other direction in its shell). For LOCC the weights have the known form
\[
 f_x=\min\{1,e^{\tau_n-S_n(x)}\},\qquad S_n(x)=-\ln p_x^{(n)},
 \quad \sum_x p_x^{(n)} f_x=F. \tag{2}
\]
The scalar \(\tau_n\) is unique: the left side is continuous and strictly increasing below the largest \(S_n(x)\), with limits 0 and 1 at the two ends. Both formulas apply to compression of the source and its inaccessible reference, with a noiseless quantum message of dimension \(M\); LOCC additionally has free classical communication, but no preshared entanglement. We use these operational theorems as input.

Let \(K_n=Z_1+\cdots+Z_n\) under the source law. Set \(k_n=\min\{k\in\mathbb Z:\Pr(K_n\le k)\ge F\}\), \(B_n=nb+hk_n\), \(P_n=\Pr(K_n=k_n)>0\), and
\[
 \vartheta_n=\frac{F-\Pr(K_n<k_n)}{P_n}\ \in(0,1].
 \tag{3}
\]
Other conventions at an exact tie give the same conclusions. We use the conventional \([0,1]\) endpoints to state the limiting function. Put
\[
 A=\frac1{e^h-1},\quad z=\Phi^{-1}(F),\quad
 C=\frac12-\frac{\sigma\beta}{6}(1-z^2),\quad
 \Gamma_n=n\kappa+\sigma\sqrt n\,z+C.
 \tag{4}
\]
For real \(t\), write uniquely \(t=jh+\delta\), \(j\in\mathbb Z,\ 0\le\delta<h\). Define
\[
 G_h(t)=j+1+A e^\delta,\qquad
 K_h(t)=e^{jh}(1+A+A e^{2\delta}). \tag{5}
\]
The letter \(K_h(t)\) denotes this deterministic function, whereas \(K_n\) in (3) is the random integer sum. At each integer multiple of \(h\), both functions are continuous: \(A e^h=1+A\) verifies the left and right endpoint values. The first function is strictly increasing onto \(\mathbb R\); put \(t_\vartheta=G_h^{-1}(\vartheta)\).

Define the functions of phase on \(0\le\vartheta\le1\) by
\[
 \begin{split}
 U_h(\vartheta)&= e^{-h\vartheta}(A+\vartheta),\\
 W_h(\vartheta)&= e^{-h\vartheta}K_h(t_\vartheta),\\
 R_h(\vartheta)&=W_h(\vartheta)/U_h(\vartheta).
 \end{split} \tag{6}
\]
All three extend continuously with period 1: \(G_h(t+h)=G_h(t)+1\), \(K_h(t+h)=e^hK_h(t)\), and \(A+1=e^h A\) give the seam identities. In particular \(t_\vartheta=jh+\delta\) is computable by finding the unique \(j\) for which \(A\le\vartheta-j-1<1+A\) and putting \(\delta=\ln((\vartheta-j-1)/A)\). No floor convention at a seam affects \(U_h,W_h,R_h\).

The first line of the theorem is the classical lattice cardinality correction of Strassen [S, Theorem 1.1 and §2]; we give a direct rederivation with the LOCC normalization. The second line and their phase-dependent comparison are the results here.

**Theorem.** In this model both of the following are asymptotic equalities as \(n\to\infty\):
\[
 \begin{split}
 M_{\rm LO}(n)
 &= \frac{e^{nH+\sqrt{nV}z}}{\sqrt n}\,
       \frac{\phi(z)}{\sigma}\,e^{hC}
       \bigl(U_h(\Gamma_n)+o(1)\bigr),\\
 M_{\rm LOCC}(n)
 &= \frac{e^{nH+\sqrt{nV}z}}{\sqrt n}\,
       \frac{\phi(z)}{\sigma}\,e^{hC}
       \bigl(W_h(\Gamma_n)+o(1)\bigr).
 \end{split} \tag{7}
\]
Equivalently the ratio is \(R_h(\vartheta_n)+o(1)=R_h(\Gamma_n)+o(1)\), and the base-two communication saving is \(-\log_2 R_h(\Gamma_n)+o(1)\). These conclusions hold along the full sequence and are insensitive to phases that approach a seam. The function \(R_h\) is nonconstant, lies strictly between 0 and 1, and tends uniformly to \(2/e\) as \(h\downarrow0\).

If \(z\ne0\) or \(\kappa\) is irrational, the phases \(\Gamma_n\bmod 1\) are equidistributed. The ratio has the full nondegenerate interval \(R_h([0,1])\) as its cluster set and has no limit. If \(z=0\) and \(\kappa=u/v\) in lowest terms, the cluster set is exactly \(\{R_h(C+j/v):j=0,\ldots,v-1\}\); the set may contain fewer than \(v\) values.

## 2. Local probabilities and the fractional threshold

For \(x_k=(k-n\kappa)/(\sigma\sqrt n)\) and \(\Delta=1/(\sigma\sqrt n)\) we use the one-term lattice local expansion
\[
 \Pr(K_n=k)=
    \Delta\phi(x_k)\left(1+\frac{\beta}{6\sqrt n}(x_k^3-3x_k)\right)
    +O(n^{-3/2}), \tag{8}
\]
uniformly in the integer \(k\). For completeness, use Fourier inversion on \([-\pi,\pi]\) and the span-one condition: equality of the characteristic-function modulus to 1 implies that \(e^{it(z-z')}\) is 1 for all support differences, so this occurs there only at zero. The integral outside a fixed neighborhood of zero is exponentially small by compactness. In the neighborhood, set \(u=\sigma\sqrt n\,t\) and center the characteristic function. The logarithm of its \(n\)-th power is
\[
 -u^2/2-i\beta u^3/(6\sqrt n)+O(u^4/n).
\]
On \(|u|\le n^{1/12}\), expansion of the exponential leaves an error bounded by \(O(n^{-1}(u^4+u^6)e^{-u^2/4})\). In the remaining part of the neighborhood the characteristic-function power is \(O(e^{-c u^2})\) for some \(c>0\). Integrating the errors, with the overall factor \(\Delta\), gives the error in (8) independently of \(k\). The Gaussian transform and its third derivative give the displayed Gaussian and the cubic Hermite correction, with the plus sign shown.

To sum (8) into a cdf for bounded \(x_k\), first restrict to \(x_j\ge-D\sqrt{\ln n}\) with a large fixed \(D\). The discarded true tail is \(o(n^{-1/2})\) by the bounded-variable Hoeffding inequality, and the Gaussian and Hermite tails satisfy the same bound. The summed local error is \(O(\sqrt{\ln n}/n)=o(n^{-1/2})\). For the Gaussian, trapezoidal summation with mesh \(\Delta\) gives the upper endpoint contribution \(\Delta\phi(x_k)/2\) (the error is bounded by a constant times \(\Delta^2\int|\phi''|\)). The Hermite term can be summed using its integral, the Riemann-sum error being \(O(\Delta)\) before multiplication by \(1/\sqrt n\). Its integral to \(x_k\) is \((1-x_k^2)\phi(x_k)\). Consequently
\[
 \Pr(K_n\le k)=\Phi(x_k)+
  \frac{\phi(x_k)}{\sigma\sqrt n}
  \left(\frac12+\frac{\sigma\beta}{6}(1-x_k^2)\right)+o(n^{-1/2})
 \tag{9}
\]
uniformly for bounded \(x_k\).

The central limit theorem first gives \(x_{k_n}\to z\) from the two consecutive cdf bounds on \(F\). Using (9) at \(k_n\) and \(k_n-1\), their difference is \(O(n^{-1/2})\); hence \(|x_{k_n}-z|=O(n^{-1/2})\), since the Gaussian density is positive near \(z\). The exact interpolation \(F=\Pr(K_n\le k_n)-(1-\vartheta_n)P_n\), together with (8) and (9), now yields
\[
 k_n+\vartheta_n=\Gamma_n+o(1),\qquad
 P_n=\frac{\phi(z)}{\sigma\sqrt n}(1+o(1)).
 \tag{10}
\]
In particular \(\vartheta_n\) and \(\Gamma_n\) are \(o(1)\) apart on the circle, including at ties. From (8) the ratio \(\Pr(K_n=k_n+l)/P_n\) tends to 1 for each fixed integer \(l\); it is bounded by a common constant uniformly over all integer \(l\) and sufficiently large \(n\) (bounded Gaussian/Hermite terms and a positive central limiting density). These are the only local estimates needed for the geometric sums below.

## 3. The two operational dimensions

Write \(\pi_{n,l}=\Pr(K_n=k_n+l)/P_n\), extended by zero outside the support. Each string in shell \(l\) has probability \(e^{-B_n-lh}\); thus the number of such strings is \(e^{B_n+lh}P_n\pi_{n,l}\), without any integrality approximation. Greedy cutoff gives
\[
 \frac{L_n}{e^{B_n}P_n}
 =\sum_{l\le-1}e^{lh}\pi_{n,l}+\vartheta_n
 =A+\vartheta_n+o(1). \tag{11}
\]
The local bounds after (10) justify dominated convergence of the geometrically weighted series, also for shells that are absent at finite \(n\).

For \(\tau=B_n+t\), where \(t=jh+\delta\) as in (5), consider the acceptance probability of (2). Subtract \(\Pr(K_n<k_n)\) and divide by \(P_n\), obtaining
\[
 \sum_{l\in\mathbb Z}\pi_{n,l}
   \bigl(1_{l\le j}-1_{l\le-1}\bigr)
 + e^\delta \sum_{l>j} e^{-(l-j)h}\pi_{n,l}
   = G_h(t)+o(1). \tag{12}
\]
For the first sum the signed number of shells is exactly \(j+1\), whether \(j\) is negative or nonnegative. For the second the geometric sum tends to \(A\). The errors are uniform for \(t\) in a fixed compact interval, because \(j\) then has finitely many values and \(e^\delta\) is bounded. Choose two fixed cutoffs whose \(G_h\) values are strictly below 0 and strictly above 1. By (12) the actual \(\tau_n-B_n\) lies between them for sufficiently large \(n\). There, continuity and strict monotonicity of \(G_h\) imply uniform continuity of its inverse on a closed range containing \([0,1]\). Since (12) equals \(\vartheta_n\) at the true cutoff, it follows that
\[
 \tau_n-B_n=t_{\vartheta_n}+o(1). \tag{13}
\]

The unrounded quadratic objective for this same cutoff is
\[
 \frac{1}{e^{B_n}P_n}\sum_x \min\{1,e^{\tau-S_n(x)}\}^2
 =\sum_{l\le j}e^{lh}\pi_{n,l}
  + e^{2(jh+\delta)}\sum_{l>j}e^{-lh}\pi_{n,l}
 =K_h(t)+o(1). \tag{14}
\]
This convergence is again uniform on compact intervals. In the first sum the limiting factor is \(e^{jh}(1+A)\), and in the second \(e^{jh}A e^{2\delta}\). Since \(K_h\) is continuous, (13) and (14) give \(Q_n/(e^{B_n}P_n)=K_h(t_{\vartheta_n})+o(1)\). Thus both objectives are of order \(e^{B_n}P_n\), which grows exponentially: (10) gives \(B_n=nH+\sqrt{nV}z+O(1)\), and \(V>0\) implies \(H>0\). Ceilings in (1) give relative \(o(1)\) errors.

Finally (10) gives \(B_n=nH+\sqrt{nV}z+hC-h\vartheta_n+o(1)\). Substitution into (11) and (14) proves (7), first with \(\vartheta_n\), then with \(\Gamma_n\) by continuity on the circle. Positivity holds directly. To prove a strict gain at every phase, work with the infinite shell array. On this array, \(t_\vartheta\) corresponds to the weights \(g_l=\min(1,e^{t_\vartheta-lh})\) and satisfies \(\sum_l(g_l-1_{l\le-1})=\vartheta\). It minimizes \(\sum_l e^{lh}g_l^2\) subject to this shifted-sum constraint among feasible competitors with both sums absolutely convergent: for each \(l\), the weight \(g_l\) minimizes \(e^{lh}g^2-2 e^{t_\vartheta}g\) on \([0,1]\), so the objective difference is nonnegative after summing the pointwise inequalities and canceling the absolutely convergent weight differences. For \(0<\vartheta<1\), the competitor with weights 1 below the cutoff, \(\vartheta\) at 0, and 0 above has objective \(A+\vartheta^2<A+\vartheta\). At \(\vartheta=0\), lower the weight at \(l=-1\) from 1 to \(1-r\) and increase that at \(l=0\) from 0 to \(r\). The objective falls by \((2r-r^2)e^{-h}-r^2>0\) when \(0<r<2/(1+e^h)\). Periodicity handles \(\vartheta=1\). Hence \(R_h<1\) uniformly on the phase circle for each fixed \(h>0\).

On any open interval of phases where \(j\) is fixed, the numerator of
\[
 R_h(\vartheta)
 =\frac{ e^{jh}\bigl(1+A+(\vartheta-j-1)^2/A\bigr)}{A+\vartheta}
 \tag{15}
\]
has nonzero quadratic coefficient. Such an interval always exists; the function is not constant. As \(h\downarrow0\), \(A=h^{-1}+O(1)\) and \(\delta\in[0,h)\) imply \(jh=-1+O(h)\) uniformly in phase. The remaining factor in (15), or in (5) and (6), tends uniformly to 2. This recovers \(2/e\) as a small-span limit of the functions, not as an assertion of a fixed-span limit in \(n\).

## 4. Which phases occur?

Write \(\alpha=\sigma z\) and \(\Gamma_n=n\kappa+\alpha\sqrt n+C\). By Weyl's criterion, to prove equidistribution it suffices to show that each nonzero integer Fourier mode has average tending to zero. If \(\kappa\) is irrational, the partial sums of \(e^{2\pi i m\kappa n}\) are bounded for fixed \(m\ne0\). Summation by parts against \(e^{2\pi i m\alpha\sqrt n}\), whose total variation over the first \(N\) integers is \(O(\sqrt N)\) for fixed \(m,\alpha\), proves the claim. If \(\kappa=u/v\) is rational and \(\alpha\ne0\), split into residue classes modulo \(v\). On one such progression the linear term is constant modulo 1, and the sum of \(e^{2\pi i m\alpha\sqrt{v j+r}}\) differs by \(O(\sqrt N)\) from the integral of the same function over the corresponding interval in \(j\) (use the integrated modulus of the derivative on each unit interval; finitely many initial terms are harmless). Substitution \(w=\sqrt{v j+r}\) reduces the integral to a constant times \(\int w e^{2\pi i m\alpha w}\,dw\), bounded by \(O(\sqrt N)\) by integration by parts. This proves equidistribution also in this case. In the remaining case \(\alpha=0,\ \kappa=u/v\), the phases run through exactly \(C+j/v\bmod1\) periodically. Continuity, the \(o(1)\) in (7), and compactness now give the asserted cluster sets.

For an example not requiring (8) or (9), take \(p=(1/2,1/4,1/4)\), \(h=\ln2\), \(b=h\), and \(F=1/2\). Under the source law \(K_n\) is a fair binomial. Its symmetry gives \(\vartheta_{2m}=1/2\) and \(\vartheta_{2m+1}=1\) exactly, including the equality at the odd cutoff. Equation (15) specializes to
\[
 R_{\ln2}(\vartheta)=
 \tfrac14\left(1+\vartheta+\frac{2}{1+\vartheta}\right),
 \qquad 0\le\vartheta\le1 .
 \tag{16}
\]
Thus the two subsequential limits are \(17/24\) and \(3/4\). More generally for this spectrum and \(F\ne1/2\), its whole cluster interval is \([1/\sqrt2,3/4]\); the minimum in (16) occurs at \(1+\vartheta=\sqrt2\). This is an example, not a universal upper bound across all lattice spans.

## 5. Classical uniform-alternative test

One can independently see the need for a lattice phase even on the unassisted side. For the preceding \(p\) and the uniform law \(q=(1/3,1/3,1/3)\), use type-I error \(1/2\) and let \(\beta_n^{\rm test}\) be the optimal type-II error, allowing randomized acceptance at the boundary. The test definition is \(\min\mathbb E_{q^{\otimes n}}f\) subject to \(\mathbb E_{p^{\otimes n}}f\ge1/2,\ 0\le f\le1\), so \(\beta_n^{\rm test}=L_n/3^n\) exactly, before any rounding. Here \(D(p\|q)=\ln3-\tfrac32\ln2\). By the central binomial coefficient asymptotics, \(\sqrt n\,P_n\to\sqrt{2/\pi}\); the neighboring binomial atom ratios converge to 1 and are at most 1, since \(k_n\) is a mode. Equation (11) follows by geometric summation without Edgeworth. Along the even subsequence \(B_n=nH,\ \vartheta_n=1/2\); along the odd one \(B_n=nH-h/2,\ \vartheta_n=1\). It follows that
\[
 \sqrt n\,e^{nD(p\|q)}\beta_n^{\rm test}\ \longrightarrow\
 \begin{cases}
  \tfrac32\sqrt{2/\pi}, & n\ {\rm even},\\
  \sqrt2\,\sqrt{2/\pi}, & n\ {\rm odd}.
 \end{cases}
 \tag{17}
\]
Thus the lattice-inclusive statement of Hayashi [H, arXiv v2, Theorem 2, PDF Eq. (46); HTML Eq. (47)] with a single constant term for this randomized test cannot hold as printed. In its §X-A, PDF Eq. (131) (HTML Eq. (135)), the expansion used at a deterministic cutoff lacks the order-\(n^{-1/2}\) lattice continuity term; accounting for a randomized tie gives (9) and (10) here. This corollary concerns just the fixed arXiv version's stated testing formula in the lattice case. It does not change the nonlattice result or make a claim about the other tasks in that work.
