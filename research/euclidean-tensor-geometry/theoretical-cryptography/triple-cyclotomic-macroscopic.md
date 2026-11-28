# Exact macroscopic theta transition on a three-factor cyclotomic torus

Let \(H_i=\{x\in\mathbb R^{n_i}:\sum_a x_a=0\}\) and \(A_{n_i-1}=H_i\cap\mathbb Z^{n_i}\) for \(i=1,2,3\), and give the tensor space its usual Euclidean metric. Write
\[
 F=A_{n_1-1}\otimes A_{n_2-1}\otimes A_{n_3-1},
 \qquad \Lambda=F^*.
\]
Equivalently \(F\) is the integer array space with zero sum along each coordinate line. Put \(\Theta(a)=\sum_{X\in F}a^{\|X\|^2}\), \(0<a<1\), using the sum of squared entries.

Let a common scale \(N\to\infty\) satisfy \(n_i/N\to\beta_i\in(0,\infty)\), and suppose \(Na\to c\in[0,\infty)\). Define the circle mean rate function
\[
 \ell(t)=\log I_0(t),\qquad
 I_0(t)=\int_{-\pi}^{\pi}\exp(t\cos u)\,\frac{du}{2\pi},\qquad
 I(r)=\sup_{t\geq0}\{tr-\ell(t)\},\quad 0\leq r\leq1.
\]
The endpoint \(I(1)=+\infty\) is allowed.

**Theorem.** The exact normalized logarithm is
\[
 \lim_{N\to\infty}\frac{\log\Theta(a)}{N^2}
 =\max_{r_1,r_2,r_3\in[0,1)}
 \left\{2c\beta_1\beta_2\beta_3 r_1r_2r_3
      -\beta_1\beta_2I(r_1)-\beta_2\beta_3I(r_2)-\beta_3\beta_1I(r_3)\right\}.
 \tag{1}
\]
For balanced side sizes \(\beta_1=\beta_2=\beta_3=1\) this equals
\[
 \mathcal F(c)=\max_{0\leq r<1}\{2cr^3-3I(r)\}.
 \tag{2}
\]
There is a strict first-order transition at
\[
 c_*=\frac{3I(r_*)}{2r_*^3}=\frac{t_*}{2r_*^2},
 \qquad
 3\ell(t_*)=2t_*\ell'(t_*),\quad r_*=\ell'(t_*),
 \tag{3}
\]
where the displayed equation has exactly one solution \(t_*>0\). In particular \(2.3808873<c_*<2.3808877\), certified by the rational series checker below. Below \(c_*\) only \(r=0\) maximizes (2). At \(c_*\) the two maximizers are \(0\) and \(r_*\); above \(c_*\) there is a unique maximizer with \(r>0\). The left and right derivatives of \(\mathcal F\) at \(c_*\) are respectively \(0\) and \(2r_*^3\).

**Consequence for smoothing.** Write \(a=e^{-\pi s^2}\). For balanced side sizes and every fixed \(\epsilon>0\), standard smoothing \(\eta_\epsilon(\Lambda)\) obeys
\[
 \liminf_{N\to\infty}\big(\pi\eta_\epsilon(\Lambda)^2-\log N\big)
 \geq -\log c_*.
 \tag{4}
\]
In contrast the shortest shell is of squared norm 8 with multiplicity \(2\prod_i\binom{n_i}{2}\), predicting \(a\asymp N^{-3/4}\) if only that shell were relevant. At that apparent scale the theta is much larger: whenever \(a\to0\) and \(Na\to\infty\), one has \(\log\Theta(a)\sim 2a n_1n_2n_3\). In particular \(a\asymp N^{-3/4}\) gives a logarithm of order \(N^{9/4}\). The theorem determines the onset of positive normalized logarithm, not the subcritical unnormalized theta, an upper bound matching (4), or a total-variation curve.

There is an exact arithmetic instance: for three distinct odd primes \(p_i=n_i\), the canonical integer-ring lattice of conductor \(p_1p_2p_3\) is isometric to \(\sqrt{p_1p_2p_3}\,\Lambda\). Apply the theorem in normalized units, or multiply squared widths by \(p_1p_2p_3\) for this unscaled lattice.

### Context and scope

[Lyubashevsky–Peikert–Regev, Definition 2.1 and Lemma 2.3](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) use the Gaussian smoothing condition in an abstract residue comparison; [Micciancio–Peikert, Corollary 2.7](https://web.eecs.umich.edu/~cpeikert/pubs/LWsE.pdf) gives a general tensor-product smoothing bound. The [two-factor companion](https://github.com/mxym/math/blob/8b07ee5d6d29575c8d1f27cb76d1c0d7f078f5d9/research/euclidean-tensor-geometry/theoretical-cryptography/bipartite-cycle-torus.md) has a finite-theta limit governed by disjoint sparse cycles, not a macroscopic triangle interaction. The method below is related in spirit to the dense entropy variational principle of [Chatterjee–Diaconis, Theorem 3.1](https://arxiv.org/abs/1102.2650), but is proved directly for three rectangular matrices of independent circle variables and then identified with the exact lattice theta. We do not assert exhaustive priority. No hidden data, scheme, attack, or computational hardness statement is involved.

## 1. Exact Fourier enforcement of the line constraints

The tensors of \((e_a-e_{n_i})\) for \(a<n_i\), one in each factor, are an integral basis of \(F\). In fact the interior entries of an array with the line constraints uniquely determine the remaining entries by zero sums, and a linear combination of these basis tensors realizes every prescribed interior. Dualizing gives \(\Lambda=\bigotimes_i A_{n_i-1}^*\).

Take independent Haar unit complex entries in matrices \(A\) of size \(n_1\times n_2\), \(B\) of size \(n_2\times n_3\), and \(C\) of size \(n_3\times n_1\). Define \(\vartheta_a(z)=\sum_{k\in\mathbb Z}a^{k^2}z^k\) for \(|z|=1\). Absolute convergence and character integration give the exact identity
\[
 \Theta(a)=\mathbb E\prod_{i,j,k}\vartheta_a(A_{ij}B_{jk}C_{ki}).
 \tag{5}
\]
Indeed each independent phase integral forces the sum of the powers on the corresponding line to be zero. For all sufficiently small \(a\), each factor in (5) is positive and
\(\log\vartheta_a(z)=2a\,\operatorname{Re}z+O(a^2)\) uniformly on the circle, by bounding the higher harmonics and expanding \(\log(1+v)\) for small real \(v\). Thus
\[
 \log\Theta(a)=
 \log\mathbb E\exp(2a\,\operatorname{Re}\operatorname{tr}(ABC))
                 +O(n_1n_2n_3a^2).
 \tag{6}
\]
At \(Na\to c<\infty\) the error is \(O(N)\). This error estimate is only on the macroscopic \(N^2\) scale.

## 2. Reduction of the entropy optimization to means

First, for a probability law \(P\) on the circle with complex mean \(u\), its relative entropy from Haar is at least \(I(|u|)\) by testing the variational entropy bound with \(t\,\operatorname{Re}(e^{-i\arg u}z)\). For \(0\leq r<1\), the exponential tilt proportional to \(e^{t\operatorname{Re}z}\) with \(\ell'(t)=r\) has real mean \(r\) and entropy \(I(r)\). Strict increase of \(\ell'\) follows since its derivative is the variance of the tilted cosine; it maps \([0,\infty)\) onto \([0,1)\) because tilt increasingly concentrates near the maximum cosine. Also \(I(1)=+\infty\) by dominated convergence of \(e^{-t}I_0(t)\to0\); the same variational formula implies \(I(r)\to\infty\) as \(r\uparrow1\).

We need more than convexity in \(r\): \(x\mapsto I(\sqrt x)\) is convex on \([0,1)\). To see it put \(r(t)=\ell'(t)\). The positive power series of \(I_0(t)\) gives
\[
 \frac{r(t)}t
  =\frac12 \frac{\sum_{k\geq0}(t^2/4)^k/((k!)^2(k+1))}
                    {\sum_{k\geq0}(t^2/4)^k/(k!)^2}.
\]
This ratio strictly decreases for \(t>0\): it is half the expectation of the strictly decreasing function \(k\mapsto1/(k+1)\) under a nondegenerate family of probabilities proportional to \((t^2/4)^k/(k!)^2\), whose derivative in \(\log(t^2/4)\) is its covariance with \(k\), strictly negative. Since \(I'(r(t))=t\), the derivative of \(I(\sqrt x)\) at \(x=r(t)^2\) is \(t/(2r(t))\), increasing. The limit at zero exists by the power series. It follows that for any rectangular array of mean entries \(D_{ij}\) of modulus at most one, the sum of their entropy costs satisfies
\[
 \sum_{ij}I(|D_{ij}|)
 \geq kl\, I\!\left(\frac{\|D\|_F}{\sqrt{kl}}\right)
 \quad(D\text{ of size }k\times l).
 \tag{7}
\]

For a lower bound in (1), let entries in the respective matrices be independent tilts of means \(r_1,r_2,r_3\). Their total relative entropy from the product Haar law is \(n_1n_2 I(r_1)+n_2n_3 I(r_2)+n_3n_1 I(r_3)\), and the expected real trace is \(n_1n_2n_3 r_1r_2r_3\). Applying Jensen to the likelihood change of measure gives the expression in (1) as a lower bound after scaling; take the supremum.

For the upper bound we show why it suffices to see the conditional means on a subexponential partition. Fix \(0<\varepsilon<1\). Matrices of size \(k\times l\) with entries of modulus at most one have \(\|D\|_F\leq\sqrt{kl}\); normalize to a matrix of Frobenius norm at most one. Dropping singular values below \(\varepsilon\) gives rank at most \(\varepsilon^{-2}\) and operator error at most \(\varepsilon\). These truncated matrices have an operator \(\varepsilon\)-net of cardinal \(\exp(O_\varepsilon(k+l))\): approximate each of the bounded number of singular values by a grid and the left and right unit singular vectors by Euclidean sphere nets with fixed mesh depending only on \(\varepsilon\). For a rank-one term, the operator error of perturbing the unit vectors is at most the sum of their Euclidean errors by splitting the outer product difference. Standard Euclidean sphere nets with fixed mesh have size exponential in the real dimension by packing. Taking the first arm of a finite list of approximants that meets the bound gives a measurable partition with
\[
 \|D-D_0\|_{\rm op}\leq 2\varepsilon\sqrt{kl}
\]
on each cell for its representative \(D_0\).

Apply the partition to \(A,B,C\), getting at most \(\exp(O_\varepsilon(N))\) triple cells. For a positive-mass cell \(E\), let \(\bar A,\bar B,\bar C\) be its conditional means under product Haar. They have modulus at most one entrywise and have the same operator distance to the representatives, by convexity. Thus, by telescoping the trace product,
\[
 |\operatorname{tr}(ABC)-\operatorname{tr}(\bar A\bar B\bar C)|
 \leq12\varepsilon\,n_1n_2n_3 \quad\text{on }E.
\]
For each term use \(|\operatorname{tr}(XYZ)|\leq\|X\|_{\rm op}\|Y\|_F\|Z\|_F\) with the differing matrix first by cyclicity. The entropy of the conditional law relative to its product Haar reference is exactly \(-\log\Pr(E)\), and is at least the sum of relative entropies of all its coordinate marginals by the entropy chain rule. Equations (7) and the mean entropy bound show that the logarithm of the cell mass is at most
\(-n_1n_2 I(r_1)-n_2n_3 I(r_2)-n_3n_1 I(r_3)\),
where \(r_1=\|\bar A\|_F/\sqrt{n_1n_2}\), and analogously for the other two. These \(r_i<1\) on any positive-mass cell, as a marginal with modulus-one mean would be a point mass, of infinite entropy. Finally
\[
 |\operatorname{tr}(\bar A\bar B\bar C)|
 \leq \|\bar A\|_F\|\bar B\|_F\|\bar C\|_F
      =n_1n_2n_3 r_1r_2r_3 .
\]
Together these bound the contribution of the cell by the exponential of the finite-size expression in (1) times \(N^2\), plus \(O(a\varepsilon n_1n_2n_3)\) in the exponent. Sum all cells; their logarithmic count is \(o(N^2)\) for fixed \(\varepsilon\). In maximizing the finite-size expression, the \(r_i\)'s can be confined to a common compact subinterval of \([0,1)\), since all penalty coefficients stay bounded below, \(I(r)\to\infty\), and the zero triple attains zero. The maxima therefore converge to the one in (1). Letting \(\varepsilon\downarrow0\) proves the upper bound. No independence of the variables after conditioning on a cell is assumed. Keeping the net cardinality bound explicitly gives a finite-size error as well: for bounded \(Na\) and side proportions bounded above and below, the difference between \(\log\Theta(a)\) and the unnormalized three-scalar maximum \( \max[\,2a n_1n_2n_3 r_1r_2r_3-\sum_i n_i n_{i+1} I(r_i)\,]\) (cyclic sizes) is \(O(N^{5/3}(\log N)^{1/3})\). Indeed the singular-vector and singular-value meshes may be taken proportional to \(\varepsilon^3\) for rank at most \(\varepsilon^{-2}\), giving logarithmic count \(O(N\varepsilon^{-2}\log(1/\varepsilon))\). Balance this against \(O(\varepsilon N^2)\) at \(\varepsilon=(\log N/N)^{1/3}\) and include the \(O(N)\) error of (6).

## 3. Balanced scalar optimum and uniqueness

For equal side proportions, the entropy \(I\) is increasing and convex, so \(u\mapsto I(e^u)\) is convex where \(e^u<1\). If all \(r_i>0\), Jensen on \(\log r_i\) shows \(\sum I(r_i)\geq3I((r_1r_2r_3)^{1/3})\), with strict inequality if they are unequal (its derivative is strictly increasing). If any \(r_i=0\), the objective is nonpositive and zero is attainable by all zero. Equality of the three values is achievable for each scalar choice, proving (2).

Near zero, \(r(t)=t/2-t^3/16+O(t^5)\) from the positive series, so \(I(r)=r^2+O(r^4)\); hence \(3I(r)/(2r^3)\to\infty\) at zero and also at one. Differentiation gives the sign of the derivative of \(I(r)/r^3\) as the sign of
\(h(t)=3\ell(t)-2t r(t)\) with \(t=I'(r)\). We show that \(h\) has a unique positive root. Integration by parts of the defining circle integral gives \(I_0''+I_0'/t=I_0\), whence \(r'=1-r/t-r^2\). Put
\[
 q(t)=\frac{t r'}r,\qquad
 q+1=t(1/r-r),\qquad
 q'=(q+1)/t-q(1/r+r).
\]
Here \(0<q<1\): increase of \(r\) gives positivity, and strict negativity of the derivative of \(r/t\) established above gives the upper bound. At any stationary point of \(q\), differentiate once more and use the relation for \(q+1\) to obtain \(q''=(q+1)(q^2-1)/t^2<0\). The power series gives \(q=1-t^2/4+O(t^4)\), so \(q'<0\) initially. There can be no first zero of \(q'\): at such a point \(q''<0\) would give \(q'>0\) immediately to its left. Thus \(q\) strictly decreases. It tends to zero at infinity, since a positive limiting lower bound would make \(\log r(t)=\log r(1)+\int_1^t q(u)\,du/u\) unbounded. Consequently \(h'(t)=r(t)(1-2q(t))\) changes from negative to positive exactly once. Also \(h(0)=0\) and \(h(t)/t\to1\): \(r(t)\to1\) and \(\ell(t)/t\to1\) follow by concentration at the maximum of cosine and a lower bound integrating any fixed small arc around it. This gives the unique \(t_*\), and (3) is the unique inner minimizer of \(3I(r)/(2r^3)\). The equality \(c_*=t_*/(2r_*^2)\) follows from \(r_*t_*=3I(r_*)\).

The objective in (2) is \(r^3(2c-3I(r)/r^3)\) off \(r=0\), giving the maximizers below and at the threshold. Above the threshold the maximum is positive, and its positive maximizer is unique: \(r\mapsto t/r^2\) has strictly negative derivative before \(q=1/2\) and strictly positive derivative after, since its logarithmic derivative with respect to \(\log r\) is \(1/q-2\). The objective derivative is \(3r^2(2c-t/r^2)\), so there is at most one positive local maximum. On approaching \(c_*\) from above, the positive maximizer must converge to \(r_*\): it stays away from one by the entropy penalty, cannot approach zero since the small-\(r\) objective is uniformly negative near zero at bounded \(c\), and any accumulation point maximizes at \(c_*\). Comparing the objectives at \(r_*\) and at those maximizers bounds the right derivative between \(2r_*^3\) and its limiting equal upper bound. The left derivative is zero.

## 4. Geometry and the smoothing consequence

A nonzero two-dimensional slice with zero row and column sums has at least four nonzero entries, with equality only for a signed rectangle up to a nonzero scalar. Any nonzero three-dimensional array in \(F\) has at least two nonzero parallel slices because the third coordinate lines sum to zero. To have squared norm 8, there must be exactly two opposite four-entry signed rectangles with entries \(\pm1\) at the corresponding positions. This gives exactly \(2\prod_i\binom{n_i}{2}\) such vectors. If \(a\to0\) and \(Na\to\infty\), then \(|\operatorname{tr}(ABC)|\leq n_1n_2n_3\) gives an upper bound \(2a n_1n_2n_3\) on the logarithm of the expectation in (6). For a lower bound fix \(0<r<1\) as all three means in the same product tilt argument, giving \(2a n_1n_2n_3 r^3-O_r(N^2)\). Divide by \(2a n_1n_2n_3\), use (6), and let \(r\uparrow1\). This proves the stated asymptotic beyond the macroscopic scale. At a fixed \(c>c_*\), \(\Theta(c/N)>1+\epsilon\) eventually; since the theta decreases strictly as \(s\) increases with nome \(e^{-\pi s^2}\), this proves \(\pi\eta_\epsilon^2>\log N-\log c\) eventually. Let \(c\downarrow c_*\) to get (4).

For prime \(p\), the real canonical trace Gram on its power basis has diagonal \(p-1\), off-diagonal \(-1\), as for \(\sqrt p\) times the projected coordinate basis of \(A_{p-1}^*\). For distinct primes \(p_1,p_2,p_3\), the product power basis is an integral basis: it spans \(\mathbb Z[\zeta_{p_1},\zeta_{p_2},\zeta_{p_3}]=\mathbb Z[\zeta_{p_1p_2p_3}]\) by Bézout and the individual relations, and the number of elements is exactly the field degree. CRT on exponents makes all embeddings triples of independent choices in the factors, so the trace Gram is their tensor product. This proves the conductor-product instance.

## Reproduction

Run `python3 verify-triple-cyclotomic-macroscopic.py` (Python standard library only). It checks small exact line-array, Fourier and trace products and rigorously brackets the scalar transition by rational positive-series bounds. It does not simulate asymptotic theta or provide a matching subcritical smoothing upper bound.
