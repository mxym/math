# The four-thirds obstruction to exact Gaussian conversion on lattices

Let \(\Lambda\subset\mathbb R^d\) be a fixed full-rank lattice of covolume \(V\), and write \(\Gamma=\Lambda^*\) for its Euclidean dual. The width-\(t\) continuous Gaussian has density \(g_t(x)=t^{-d}\exp(-\pi\|x\|^2/t^2)\). One observation has law \(\theta+g_t\) for an unknown deterministic \(\theta\in\Lambda\). A single Markov kernel, allowed to be arbitrary and to use fresh randomness, must return exactly \(\theta+D_{\Lambda,s}\) simultaneously for every such \(\theta\), with \(D_{\Lambda,s}(u)\) proportional to \(e^{-\pi\|u\|^2/s^2}\) on \(\Lambda\).

**Theorem.** Every such kernel satisfies
\[
                          s^2\ge \tfrac43t^2-C_\Lambda                  \tag{1}
\]
for a finite constant depending only on the fixed lattice (for all \(t\ge1\)). In particular on \(\mathbb Z\) the earlier [exact construction](exact-gaussian-four-thirds.md) with \(s^2\ge\tfrac43 t^2+2\) for \(t\ge4\) gives
\[
               \inf_{\mathrm{exact\ kernels}}\ s^2=\tfrac43t^2+O(1).
 \tag{2}
\]
The same leading ratio holds for every fixed rectangular lattice: combine (1) with that construction coordinatewise. For an arbitrary skew lattice (1) is a necessary bound only. Neither the additive optimum, exact membership of the line \(s^2=\tfrac43t^2\), nor monotonicity of exact feasibility as \(s\) varies is asserted.

This improves the [previous all-lattice necessary bound](exact-lattice-gaussian-gap.md) of \(5/4\), closes the leading-constant question for rectangular lattices, and does not address efficiency, finite parameter sets, lattice quotients, or any cryptographic implication. The distinct approximation of Gaussian shifts by translates of a Gaussian has standard Fourier/alias methods; see [Gröchenig, Romero and Stöckler (2018)](https://doi.org/10.1007/s00222-017-0760-2) for sampling in Gaussian shift-invariant spaces. Gaussian randomized rounding of [Peikert, Theorem 3.1 and §4.1](https://web.eecs.umich.edu/~cpeikert/pubs/pargauss.pdf) and [LPR Toolkit, §2.4.2](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) yields statistical approximation, not this exact unknown-center comparison. [Gama, Narayanan, LiuLin and Yue](https://opencryptology.org/2023/1288/versions/20240114T061341Z.pdf) instead synthesize a different continuous noise law and round around a given center; their input is not one noisy observation of an unknown center. The proof here uses the sampling aliases as a *necessity certificate* against any nonnegative kernel.

## 1. Exactness as a positive annihilator

Exactness allows translation averaging to make the kernel equivariant. To see this, average its conjugates under simultaneous lattice translation over growing lattice boxes. Every average is still exact, and its equivariance error under each fixed translation tends to zero in the sup norm by the relative boundary of the box. For the countably many possible output atoms, take a common diagonal weak-* limit in the unit ball of \(L^\infty(\mathbb R^d)\); on this ball weak-* subsequence extraction is allowed by separability of \(L^1(\mathbb R^d)\). Positivity, finite subset mass at most one, equivariance, and all exact Gaussian-integral identities pass to the limit. At center zero the limiting output masses sum to one, so monotone convergence against the strictly positive \(g_t\) restores total kernel mass one almost everywhere. Equivariance is then expressed as \(K(u\mid x)=V p(u-x)\) for a density \(p\ge0\), with
\[
 \sum_{u\in\Lambda}p(u-x)=1/V\quad\text{a.e.},\qquad
 (g_t*p)(u)=\frac{e^{-\pi\|u\|^2/s^2}}{V Z_s}=C_s g_s(u),
 \quad
 Z_s=\sum_{u\in\Lambda}e^{-\pi\|u\|^2/s^2},\quad
 C_s=s^d/(VZ_s).
 \tag{3}
\]
Integrating the periodization on a fundamental domain proves the density normalization, and its nonzero Fourier coefficients give \(\widehat p(w)=0\) for \(w\in\Gamma\setminus\{0\}\), using \(\widehat p(w)=\int p(x)e^{-2\pi i w\cdot x}\,dx\). No regularity or pointwise Gaussian envelope for \(p\) is assumed.

We use the weaker \(s^2\ge\tfrac54t^2-O_\Lambda(1)\), with its short proof reproduced in §5, just to localize \(A=s^2/(s^2-t^2)\) to a fixed bounded interval. Thus for large \(t\) it suffices to consider
\[
          D=s^2-t^2>0,\qquad 4\le A\le6,\qquad
          \omega=(1-1/A)D,\qquad \beta=1/A .
\]
Indeed \(A<4\) already gives the asserted \(4/3\), and the weaker bound implies \(A\le6\) for large \(t\). In this region \(D\ge t^2/5\) and tends to infinity. Define a locally integrable function
\[
                        h(x)=\frac{p(x)}{C_s g_{\sqrt D}(x)}-1 .
\]
The identity \(g_t(u-x)g_{\sqrt D}(x)=g_s(u)g_{\sqrt\omega}(x-\beta u)\) gives
\[
      \int h(x)g_{\sqrt\omega}(x-u/A)\,dx=0
               \quad(u\in\Lambda).
 \tag{4}
\]
Since \(h\ge-1\), the integral with \(|h|\) in (4) is at most 2, for every translate. Choose a shortest nonzero \(v\in\Gamma\) and set \(\lambda=\|v\|\), \(e=v/\lambda\). The vanished Fourier coefficient of \(p\) at \(-v\) gives
\[
 \int h(x) f(x)\,dx=-e^{-\pi D\lambda^2},
       \qquad f(x)=g_{\sqrt D}(x)e^{2\pi i v\cdot x},\qquad
       \widehat f(\xi)=e^{-\pi D\|\xi-v\|^2}.
 \tag{5}
\]
It is important that the left side is tested against a function exponentially well approximable by the translates in (4), in a norm that accommodates possibly unbounded \(h\).

## 2. A Fourier-aliased approximation and its derivatives

Use coordinates \(\xi=(u,y)\) along \(e\) and its orthogonal complement; the same coordinates will be used for \(x\). Set \(a=A\lambda/2\), \(b=a-\lambda\), and \(p_A=ae\). Let \(\mathcal V\) be the closed Voronoi cell at zero for \(\Gamma\); \(\mathcal V_A=A\mathcal V\) is a fundamental cell for \(A\Gamma\) up to its boundary. A finite set of facet normals \(w\in\Gamma\setminus\{0\}\) describes \(\mathcal V_A\) by
\[
       d_w(z):=\tfrac{A}{2}\|w\|-z\cdot w/\|w\|\ge0 .
\]
The midpoint \(v/2\) has precisely zero and \(v\) as its closest lattice points. In fact \(\|w-v/2\|^2-\|v/2\|^2=\|w\|^2-w\cdot v>0\) for \(w\ne0,v\), since \(\|w\|\ge\lambda\), with equality forcing \(w=v\). Thus \(v\) is a facet normal, and a fixed-radius neighborhood of \(p_A\), uniform for \(A\in[4,6]\), intersects no other facet. This also follows immediately by positive separation for the other finitely many facet inequalities.

Choose a fixed smooth cutoff \(\zeta\) with \(0\le\zeta\le1\), equal to 0 on \((-\infty,1]\) and 1 on \([2,\infty)\), and put \(\chi(z)=\prod_w\zeta(D\,d_w(z))\). Its compact support is inside the base cell, away from the whole boundary. Take the \(A\Gamma\)-periodic smooth function \(P\) with base-cell value
\[
 P(z)=\chi(z)e^{-\pi D\|z-v\|^2+\pi\omega\|z\|^2}.
\]
Let \(q\) have Fourier transform \(\widehat q(\xi)=e^{-\pi\omega\|\xi\|^2}P(\xi)\). The smooth torus function \(P\) has absolutely summable Fourier coefficients, indexed by the dual lattice \(\Lambda/A\), by repeated differentiation on a fundamental torus. Consequently \(q\) in physical space is an absolutely \(L^1\)-convergent combination of the Gaussian translates in (4). It is also absolutely integrable against \(|h|\), since every translate has weighted norm at most 2 and the coefficients are summable; termwise integration gives \(\int hq=0\). No bound on the coefficient sum uniform in \(D\) is needed.

Let \(E=f-q\), \(R_1=D\) and \(R_j=\sqrt D\) for the \(d-1\) perpendicular coordinates. We prove, for each \(\alpha_j\in\{0,2\}\), the bound
\[
       \|\partial^\alpha\widehat E\|_1
          \le C_\Lambda\, e^{-\pi D b^2}
               \prod_{j=1}^d R_j^{\alpha_j-1}.
 \tag{6}
\]
Constants here are uniform over \(A\in[4,6]\), \(D\) sufficiently large, and the finite derivative orders in (6).

**Zero tile and the original Gaussian tail.** Combine these into
\(E_0(\xi)=(1-\chi(\xi))e^{-\pi D\|\xi-v\|^2}\) on all of \(\mathbb R^d\), with \(\chi\) zero outside the cell. For any facet \(w\ne v\), its outward distance from \(v\) is
\(A\|w\|/2-v\cdot w/\|w\|>b\) uniformly over \(A\in[4,6]\). The strictness follows from shortestness and Cauchy–Schwarz; equality would force \(w=v\). If \(E_0\) or a derivative is nonzero, some \(d_w(\xi)<2/D\). For \(w\ne v\) this gives a uniform positive gap in \(\|\xi-v\|^2\) above \(b^2\). For \(w=v\) it gives \(u\ge a-2/D\); outside a fixed small ball about \(p_A\), either \(u-a\) is bounded below by a positive constant or the perpendicular norm \(\|y\|\) is bounded below by a positive constant, and again there is a positive gap. Bounds for derivatives away from that ball therefore follow from a polynomial in \(D,\|\xi-v\|\) times Gaussian tails, exponentially smaller than (6). More explicitly, if \(\|\xi-v\|^2\ge b^2+\delta\), split off \(e^{-\pi D(b^2+\delta/2)}\); the remaining Gaussian dominates an integrable polynomial weight, uniformly for \(D\ge1\), since \(b\) is bounded. Derivatives of a smooth cutoff localizing to the ball obey the same estimate off a smaller ball.

In the ball only the \(v\) facet affects \(\chi\) for large \(D\), so the expression is the cutoff \(1-\zeta(D(a-u))\) times \(e^{-\pi D(u-\lambda)^2} e^{-\pi D\|y\|^2}\). Its support satisfies \(u\ge a-2/D\). The lower endpoint exponent differs from \(Db^2\) by at most a fixed constant; after that endpoint the derivative of \((u-\lambda)^2\) is bounded below by a positive constant. Each derivative in \(u\) costs at most \(O_\Lambda(D)\) there, each perpendicular Gaussian derivative has integral scale \((\sqrt D)^{\alpha_j-1}\), and the \(u\) integral costs \(O_\Lambda(D^{-1})\). A localizing cutoff has bounded derivatives and does not increase these scales. This proves (6) for \(E_0\).

**Nonzero aliases.** At \(\xi=z+Aw\), \(z\in\mathcal V_A\), \(w\in\Gamma\setminus\{0\}\), the part of \(\widehat q\) corresponding to \(\chi\) is
\[
 \chi(z)e^{-\pi D F_w(z)},\qquad
 F_w(z)=\|z-v\|^2+(1-1/A)(\|z+Aw\|^2-\|z\|^2).
 \tag{7}
\]
Write \(r=\|w\|\), \(c=v\cdot w/r\), \(s=z\cdot w/r\). Since \(z\) is in the Voronoi cell, \(s\ge-Ar/2\), even if \(w\) is not a facet normal. The normal-variable expression in \(F_w\) is
\((s-c)^2+(A-1)(2rs+Ar^2)\). Its derivative at \(-Ar/2\) equals \((A-2)r-2c\ge0\), since \(A\ge4\) and \(|c|\le\lambda\le r\). It is therefore minimized on this half-line at \(-Ar/2\). Dropping the nonnegative perpendicular square gives
\[
                  F_w(z)\ge(Ar/2+c)^2\ge b^2 .
 \tag{8}
\]
Equality in the last comparison can occur only for \(w=-v\), because the positive quantity \(Ar/2+c\) is at least \(A\lambda/2-\lambda\) with equality only when \(r=\lambda\) and \(c=-\lambda\). For bounded \(r\) with \(w\ne-v\) there is a uniform positive gap by the finite lattice set and compact \(A\) interval. For large \(r\) the lower bound grows quadratically; choosing a fixed large radius, it exceeds \(b^2+\delta+c_0 r^2\) beyond that radius for some constants \(\delta,c_0>0\). On the translated bounded cells, every derivative of (7) has bound a fixed polynomial in \(D,1+r\) times this decaying exponential. Summing over all \(w\ne0,-v\) absorbs that polynomial in the gap, proving (6) for these tiles.

For \(w=-v\), \(u=z\cdot e\le a\) and
\[
 F_{-v}(z)=(u-\lambda)^2+(A-1)(-2\lambda u+A\lambda^2)+\|y\|^2 .
\]
The normal part is \(b^2\) at \(u=a\), and its derivative \(2(u-A\lambda)\le-A\lambda<0\) for \(u\le a\). Away from a small ball about \(p_A\) in the base coordinate \(z\), either \(a-u\) or \(\|y\|\) is bounded below, giving the same exponential-gap treatment. In the ball \(\chi(z)=\zeta(D(a-u))\), and the normal integral again has width \(O(D^{-1})\), perpendicular integrals width \(O(D^{-1/2})\), with the same derivative costs as for \(E_0\). Translation by \(-Av\) does not change derivative \(L^1\) norms. This proves (6), since \(\widehat E=E_0\) minus the sum of these nonzero alias contributions. The cutoffs vanish smoothly across all cell seams.

Applying Fourier inversion to \(\prod_j(1-(2\pi R_j)^{-2}\partial_{\xi_j}^2)\widehat E\) using (6) gives the pointwise envelope
\[
          |E(x)|\le C_\Lambda e^{-\pi D b^2}
                  \prod_{j=1}^d R_j^{-1}(1+x_j^2/R_j^2)^{-1}.
 \tag{9}
\]
Each integration by parts is justified either by the smooth Gaussian multiplier or by the integrable derivative bounds just proved.

## 3. Positivity removes every polynomial loss

The local size bound on \(h\) coming from (4) suffices to integrate (9). Tile physical space by cubes of side \(\ell=\sqrt\omega\) in the chosen coordinates. For each cube choose a point of \(\Lambda/A\) within its covering radius of the cube center; that radius stays bounded for \(A\in[4,6]\). For \(D\) large, the translate \(g_{\sqrt\omega}\) centered at that lattice point is at least \(c_\Lambda\ell^{-d}\) throughout the cube. Hence (4) and \(h\ge-1\) give the uniform estimate \(\int_{\rm cube}|h|\le C_\Lambda\ell^d\). Because \(\ell\le\sqrt D\le D\), taking the supremum of each one-dimensional envelope factor in (9) on a cell of length \(\ell\) and summing over the cells costs \(O(R_j/\ell)\) before the \(R_j^{-1}\) factor. For example compare to \(\sum_{k\in\mathbb Z}(1+(\ell k/R_j)^2)^{-1}=O(R_j/\ell)\); translating at most one cell changes the supremum estimate only by a constant. All physical scales therefore cancel and
\[
                  \int |h(x) E(x)|\,dx
                            \le C_\Lambda e^{-\pi D b^2}.
 \tag{10}
\]
This is why using just a global \(L^\infty\) envelope on a smoothed \(h\) is unnecessary; such a step would incur a spurious polynomial and logarithmic loss.

Now (5), \(\int hq=0\), and (10) give
\(e^{-\pi D\lambda^2}\le C_\Lambda e^{-\pi D b^2}\). Since
\[
 b^2-\lambda^2=\lambda^2 A(A-4)/4,\qquad
 D(A-4)=4t^2-3s^2,
\]
and \(A\ge4\), this implies \(4t^2-3s^2\le O_\Lambda(1)\), proving (1) for large \(t\). Enlarge the constant for bounded \(t\ge1\). For a rectangular lattice the exact construction applies to its independent orthogonal coordinates after scaling by their step lengths, giving the matching \(4/3+O_\Lambda(t^{-2})\) sufficient ratio.

## 4. What the spectral boundary does and does not decide

The mechanism is the least dual frequency \(v\), at distance \((A/2-1)\lambda\) from its nearest base-cell boundary. Once \(A>4\) by more than a constant over \(D\), a Gaussian at that frequency is too closely approximable by the allowed shifts to carry the required removed mass \(e^{-\pi D\lambda^2}\). The unique alias that attains the boundary exponent is the translate by \(-Av\); this explains why anisotropic physical scales \(D\) and \(\sqrt D\) are needed for the additive-constant precision. The companion standard-library checker tests the completed-square exponent, the Voronoi half-space minimization, and the gap for finite rational examples; the infinite-tail proof is (6)–(10). This method does not certify feasibility on the exact line, and a matching upper bound for arbitrary fixed skew lattices is separate.

## 5. The weaker localization bound (recalled)

Here are details so that the necessary theorem is usable without a second proof file. From (3), tilt \(p\) by \(e^{-\pi\|x\|^2/t^2}\) to form a probability \(\nu\), with normalizer \(t^d/(VZ_s)\). Completing the square in the sampled identities gives
\[
 \mathbb E_\nu e^{u\cdot X}=e^{\gamma\|u\|^2/(4\pi)}
       \quad (u\in(2\pi/t^2)\Lambda),\qquad
 \gamma=t^2(s^2-t^2)/s^2 .
\]
Cauchy–Schwarz with \(u,-u\ne0\) first implies \(\gamma\ge0\); equality would force \(u\cdot X\) to be deterministic despite the density. Thus \(\gamma>0\) and \(s>t\). Log-convex interpolation over a fundamental mesh parallelepiped yields the upper bound
\( \mathbb E_\nu e^{u\cdot X}\le\exp(\gamma\|u\|^2/(4\pi)+O_\Lambda(\gamma/t^4))\) at every real \(u\): use barycentric mesh vertices and the identity for their squared lengths as the barycenter square plus the mean square displacement. Undo the tilt by averaging the moment bound at \(u+Y\) for \(Y\sim\mathcal N(0,(2\pi/t^2)I)\), since \(\mathbb E e^{Y\cdot x}=e^{\pi\|x\|^2/t^2}\). Gaussian integration gives \(\int e^{u\cdot x}p(x)\,dx\le K_\Lambda e^{D\|u\|^2/(4\pi)}\) for \(t\ge1\), with \(D=s^2-t^2\): the constant includes \(C_s\le1\) by Poisson summation. In particular \(\widehat p\) is entire, and \(G(z)=e^{\pi D z\cdot z}\widehat p(z)\) has \(|G(x+iy)|\le K_\Lambda e^{\pi D\|x\|^2}\). The dot product in the exponential is bilinear.

Poisson summation of the sampled convolution (Schwartz, since \(p\) has all moments and \(g_t\) has Schwartz derivatives) gives
\[
   \sum_{w\in\Gamma}e^{-\pi s^2(z+w)\cdot(z+w)}(G(z+w)-C_s)=0 .
\]
First this is a real-frequency identity; on \(z=\zeta v\) it extends to complex \(\zeta\) by normal convergence on compacts, using \(s^2-D=t^2>0\), then the identity theorem. On the imaginary axis \(\operatorname{Re}\zeta=0\), isolate the \(w=0\) term to obtain \(|G(\zeta v)-C_s|\le C_\Lambda e^{-\pi t^2\lambda^2}\) by the displayed bound on \(G\) and the shortest dual norm. On \(\operatorname{Re}\zeta=2\), the upper bound is \(C_\Lambda e^{4\pi D\lambda^2}\). Three-lines at \(\zeta=1\), where \(G(v)=0\), and \(C_s\) is bounded below for \(s\ge t\ge1\), yields
\(C_s\le C_\Lambda e^{-\pi t^2\lambda^2/2+2\pi D\lambda^2}\). Hence \(D\ge t^2/4-O_\Lambda(1)\), the only localization input needed in §1.
