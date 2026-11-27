# Real spanning by discrete Gaussian samples at the smoothing width

**Scope.** This note concerns the span over the reals of samples from an
arbitrary full-rank Euclidean lattice. It proves a quantitative refinement of
a sampling statement used in the positive discrete-Gaussian-to-independent-
vectors argument. It does not assert generation over the integers or over a
number ring, an improved end-to-end Ring-LWE reduction, or a new computational
procedure.

## 1. Statement

Write \(\rho_s(x)=\exp(-\pi\|x\|^2/s^2)\), and let
\(D_{\Lambda,s,c}\) put mass proportional to \(\rho_s(x-c)\) at \(x\in\Lambda\).
For \(0<\epsilon\le e^{-8}\) write \(b=\log(1/\epsilon)\), and use the convention
\[
  \eta_\epsilon(\Lambda)=\inf\{s>0:\sum_{0\ne \xi\in\Lambda^*}
  e^{-\pi s^2\|\xi\|^2}\le\epsilon\}.
\]
There are universal \(C,c_0>0\) with the following property. Let
\(\Lambda\subset\mathbb R^n\) be full rank. Given the past, suppose each new
sample has law \(D_{\Lambda,s,c}\), with \(s\ge\eta_\epsilon(\Lambda)\).
The center and width can be fixed or chosen using the past. This includes
the ordinary case of independent samples with the same center and width.
If \(T\) is the first sample count that gives real span \(\mathbb R^n\), put
\(S=b^{-1/2}+n\epsilon\). Then
\[
 \Pr(T>n)\le C S,\qquad
 \mathbb E(T-n)\le C S,\qquad
 \Pr(T>n+\ell)\le \exp(C S-c_0\ell)\quad(\ell=0,1,\ldots).
 \tag{1}
\]
In particular, \(n+O(1+\log(1/\delta))\) samples suffice for failure
at most \(\delta\) whenever \(n\epsilon=O(1)\), and exactly \(n\) suffice
with probability \(1-o(1)\) whenever \(n\epsilon=o(1)\). The general
sample bound is \(n+O(1+n\epsilon+\log(1/\delta))\). All the constants
are uniform in the lattice and the choice of centers and widths. The
logarithmic term in the square-sample bound cannot be replaced by
\(o(b^{-1/2})\) uniformly over all dimensions, including dimension one.

**Comparison.** [Regev (2009), Lemma 3.15 and Corollary 3.16](https://cims.nyu.edu/~regev/papers/qcrypto.pdf)
use width \(s\ge\sqrt 2\,\eta_\epsilon(\Lambda)\) at \(\epsilon\le 1/10\),
obtain a constant lower bound on escape from one proper subspace, and
use \(n^2\) independent samples to obtain exponentially small failure.
That same constant escape bound already yields \(O(n+\log(1/\delta))\)
samples by a conditional geometric argument. Thus the additional
content here is the width \(s\ge\eta_\epsilon\) at the same (small)
tolerance and the near-square or exactly square sample statement, not
merely linear order in \(n\). [On Basing Search SIVP on NP-Hardness,
Lemmas 4.2 and 4.6](https://eprint.iacr.org/2016/906) instead use the
different width hypothesis \(s\ge\lambda_n(\Lambda)\), a constant
escape bound, and \(n^2\) samples in their proof; this note does not
replace the successive-minimum hypothesis in that theorem. The
affine-subspace estimate below applies to canonical embeddings of
ideal lattices, but only to this Euclidean ingredient. In particular
it does not remove unrelated width factors in the core convolution
and oracle steps of [original Ring-LWE](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf)
or of its [any-ring/modulus reduction](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf).

## 2. Two dual subgaussian bounds

Fix \(s,c\) as above. Use normalized variables
\[
 Z=\frac{\sqrt{2\pi}}s(X-c),\qquad
 U=\sqrt{2\pi}s\,\Xi,\qquad X\sim D_{\Lambda,s,c},\quad
 \Xi\sim D_{\Lambda^*,1/s,0}.
\]
Set \(\theta=\sum_{\xi\in\Lambda^*}e^{-\pi s^2\|\xi\|^2}\) and
\(\theta_c=\sum_\xi e^{-\pi s^2\|\xi\|^2}e^{-2\pi i\langle \xi,c\rangle}\).
Thus \(1-\epsilon\le\theta_c\), \(\theta\le1+\epsilon\), and
\(\Pr(U\ne0)\le\epsilon\). For real \(v\), square completion and the
fact that shifted Gaussian mass is maximized at zero on a lattice give
\[
 \mathbb E e^{\langle v,U\rangle}\le e^{\|v\|^2/2}.
 \tag{2}
\]
For the maximum assertion, apply Poisson summation and use the triangle
inequality on its nonnegative unshifted Fourier coefficients. In
particular if \(P\) projects orthogonally onto a \(k\)-dimensional
space, independent ordinary \(G\sim N(0,I_k)\) and Tonelli give
\[
 \mathbb E e^{t\|PU\|^2/2}
 =\mathbb E_G\mathbb E e^{\sqrt{t}\langle G,PU\rangle}
 \le(1-t)^{-k/2}\quad(0\le t<1).
 \tag{3}
\]
Neither (2) nor (3) assumes independent coordinates of \(U\).

Apply Poisson summation to the modulated primal Gaussian. With the
Fourier convention \(\mathbb E e^{i\langle u,Z\rangle}\) this gives
\[
 \big|\mathbb E e^{i\langle u,Z\rangle}\big|
 \le \frac{e^{-\|u\|^2/2}}{\theta_c}
   \left(1+\theta\,\mathbb E[
      1_{\{U\ne0\}} e^{\langle u,U\rangle}]\right).
 \tag{4}
\]
Indeed its dual summand, before taking absolute values, is
\(e^{-\|u\|^2/2}e^{-\pi s^2\|\xi\|^2}
e^{\langle u,\sqrt{2\pi}s\xi\rangle}e^{-2\pi i\langle \xi,c\rangle}\).
By Cauchy--Schwarz and (2) the expectation on the right of (4) is
at most \(\sqrt\epsilon\,e^{\|u\|^2}\). Consequently
\[
 |\widehat Z(u)|\le 2e^{-\|u\|^2/2}
 \quad\text{for }\|u\|\le\sqrt b/2.
 \tag{5}
\]
Also at \(\|u\|=1\), the right of (4) is less than \(3/4\) for
\(\epsilon\le e^{-8}\) (bound it by
\(e^{-1/2}[1+(1+e^{-8})e^{-3}]/(1-e^{-8})\)).
For a unit direction \(u\), if \(\langle u,Z\rangle\) has an atom
of mass \(p\) at any point, the modulus of its characteristic function
at frequency 1 is at least \(p-(1-p)\). Thus every proper affine
subspace has mass at most \(7/8\).

For the second estimate take \(0<a<1\), set \(h=1-a\), and take any
target \(z_0\) in the range of \(P\). Since the integrand below equals
1 on the atom and is nonnegative,
\[
 \begin{split}
 \Pr(PZ=z_0)&\le
 \mathbb E\exp\left(-\tfrac{a^{-1}-1}{2}\|PZ-z_0\|^2\right)\\
 &\le \frac{a^{k/2}}{1-\epsilon}
 \left(1+\theta\,\mathbb E[1_{\{U\ne0\}}e^{h\|PU\|^2/2}]\right).
 \end{split}
 \tag{6}
\]
For the second inequality, complete the primal square: its new
dimensionless precision matrix is \(I+(a^{-1}-1)P\), its inverse
is \(I-hP\), and its determinant factor in Poisson summation is
\(a^{k/2}\). The changed center contributes phases of modulus one;
the outside multiplier from completing the square is
\(\exp(-(1-a)\|z_0\|^2/2)\le1\). Both factors matter if using equality
instead of (6). For every real \(r>1\) with \(rh<1\), Hölder and (3) give
\[
 \Pr(PZ=z_0)\le \frac{a^{k/2}}{1-\epsilon}
 \left(1+(1+\epsilon)\epsilon^{1-1/r}(1-rh)^{-k/(2r)}\right).
 \tag{7}
\]

## 3. A summable codimension bound

Let \(p_k\) be the supremum of the probability of an affine subspace
of codimension \(k\) under the permitted laws (even the lattice can
vary). In normalized coordinates such a subspace has the form \(PZ=z_0\).
We prove
\[
 \sum_{k=1}^n p_k\le C(b^{-1/2}+n\epsilon),\qquad
 p_k\le 7/8.
 \tag{8}
\]
The second assertion was proved after (5). For the first, use two
ranges of Fourier information.

**Low codimension.** For \(B>0\), let
\[
 K_B(x)=\left(\frac{\sin(Bx/2)}{Bx/2}\right)^2
       =\frac{1}{B}\int_{-B}^{B}(1-|t|/B)e^{itx}\,dt,\quad K_B(0)=1 .
\]
Use the product of these kernels in orthonormal coordinates of
\(PZ-z_0\) with \(B=\sqrt b/(2\sqrt k)\). The Fourier box lies in
the ball for (5), and averaging the product bounds the atom from
above. Triangle inequality and the whole Gaussian integral give
\[
 p_k\le 2(2\sqrt{2\pi}\sqrt{k/b})^k .
 \tag{9}
\]
Fix a small absolute \(d>0\) with \(2\sqrt{2\pi d}\le1/4\). The sum
of (9) for \(k\le db\) is \(O(b^{-1/2})\): the \(k=1\) term has
this order; for \(2\le k\le\sqrt b\) bound the base by
\(2\sqrt{2\pi}b^{-1/4}\) and sum a geometric series from its square;
for \(\sqrt b<k\le db\) use the base \(1/4\). Those estimates are
for large enough absolute \(b\); bounded \(b\) is handled below.

**Higher codimension.** Put
\[
 a=(k+1)^{-4/k},\qquad h=1-a,\qquad
 r=\frac{k}{64\log^2(k+1)}.
\]
For all sufficiently large absolute \(k\), \(r\ge2\),
\(h\le4\log(k+1)/k\), \(rh\le1/2\), and \(krh^2/2\le 1/8\).
The estimates \(\log(1-h)\le-h\) and
\(-\log(1-rh)\le rh+(rh)^2\) thus give
\[
 a^{k/2}(1-rh)^{-k/(2r)}\le e^{1/8}.
\]
Using (7), we obtain
\[
 p_k\le C\left((k+1)^{-2}+\epsilon e^{\,64b\log^2(k+1)/k}\right).
 \tag{10}
\]
For sufficiently large absolute \(b\), (10) works for all \(k>db\).
The first term sums to \(O(1/b)\). For \(db<k<b^2\), the second
term is at most \(\sqrt\epsilon\), by \(r\ge2\); the sum is at most
\(b^2\sqrt\epsilon=O(b^{-1/2})\). For \(k\ge b^2\),
\(64b\log^2(k+1)/k\) is bounded by an absolute constant:
\(\log^2(k+1)/k\) decreases for \(k\ge e^2\), and
\(\log^2(b^2+1)/b\) is bounded. Therefore this last portion contributes
\(O(n\epsilon)\). For the bounded absolute interval \(8\le b\)
below the eventual cutoffs, \(\sum p_k\le n\le C n\epsilon\) with
another universal constant. This proves (8).

## 4. Waiting for rank and checking the scope

Rank increases by zero or one per sample. Let \(W_k\) be the number
of failures before rank increases at codimension \(k\), in descending
order of \(k\). Conditional on the history when this codimension is
first reached, the chance of \(j\) consecutive failures is at most
\(p_k^j\) by conditional multiplication: at each step the span is
known, and (8) applies to the next conditional law. This is
stochastic domination by the number of failures in a geometric
experiment with success probability \(1-p_k\). In particular all
levels are reached almost surely. It follows that \(\Pr(T>n)\le
\sum p_k\) and \(\mathbb E(T-n)\le\sum p_k/(1-p_k)\). For fixed
\(t>0\) with \(e^t(7/8)<1\), successive conditioning bounds
\[
  \mathbb E e^{t(T-n)}
  \le\prod_{k=1}^n\frac{1-p_k}{1-e^t p_k}
  \le\exp(C_t\textstyle\sum p_k).
\]
There is no claim that the waits are independent. Markov's inequality
now proves (1).

For a check on the logarithmic scale, take \(n=1\), \(\Lambda=\mathbb Z\),
\(c=0\), and \(s^2=\log(4/\epsilon)/\pi\). Its nonzero dual tail is
\(2\sum_{j\ge1}(\epsilon/4)^{j^2}\le\epsilon\); its failure after one draw
is exactly \(1/(s\theta)\), by Poisson summation in dimension one, hence
asymptotic to \(\sqrt{\pi/b}\). This lower example says nothing about the
sharp failure probability for \(n\to\infty\) or about the necessity of
the \(n\epsilon\) term.

For the ordinary centered spherical oracle, length control is
orthogonal to this rank argument. For example, the scaled primal law
is also exactly 1-subgaussian by the unshifted Gaussian maximum in
(2). Repeating the spherical Gaussian integral in (3) and taking
\(t=1/2\) shows
\(\Pr(\|X\|>\sqrt n\,s)\le e^{-(\pi-\log 2)n/2}\).
A union bound handles a specified number of calls. This preserves
the use of the rank lemma as a proof ingredient for *short*
independent vectors without implying that an oracle can already
sample at this width or that the rank statement improves other
parts of a hardness proof.

**Replay:** run `node verify-discrete-gaussian-span-at-smoothing.js`
with no dependencies. The script checks transform normalizations on
small, generated lattices, exact rational inequalities for the
elementary comparison, the bounded range for (10), and conditional
waiting formulas. The proof, not floating-point quadrature, certifies
the infinite sums and arbitrary lattices.
