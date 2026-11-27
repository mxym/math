# Exact Gaussian discretization on a lattice: a universal variance gap and Voronoi-dependent sufficiency

Let \(\Lambda\subset\mathbb R^d\) be any fixed full-rank lattice, of covolume \(V_\Lambda\), and let \(L=\Lambda^*\) be its Euclidean dual. For \(t>0\) let \(g_t(x)=t^{-d}\exp(-\pi\|x\|^2/t^2)\) be the continuous Gaussian density, and let \(D_{\Lambda,s}\) be the centered discrete Gaussian on \(\Lambda\) of width \(s>0\). The center \(\theta\) is an unknown deterministic point of \(\Lambda\). A kernel sees only \(X\sim \theta+g_t\); can it output exactly \(\theta+D_{\Lambda,s}\), simultaneously for every \(\theta\in\Lambda\)? Kernels may be arbitrary Markov kernels; no efficiency is required.

Write \(\lambda=\lambda_1(L)\) and \(\mathcal V\) for the closed Euclidean Voronoi cell of \(L\) at zero. Set
\[
 B=\max\{\|v\|:v\in L\cap 2\mathcal V,\ v\ne0\},\qquad
 \kappa_\Lambda=1+\frac1{1+\min(1,2\lambda/B)}.                          \tag{1}
\]
Equivalently, \(B\) is the largest shortest-representative length over the residue classes of \(L/2L\): the condition \(v/2\in\mathcal V\) is precisely that \(v\) have least norm in its class. This is a finite, positive geometric quantity.

**Theorem.**
1. If an exact kernel exists then \(s>t\), and for \(t\ge1\) it must satisfy
   \[
                         s^2\ge \tfrac54\,t^2-O_\Lambda(1).              \tag{2}
   \]
   The additive constant is independent of \(t,s\).
2. For every fixed \(\kappa>\kappa_\Lambda\), for all sufficiently large \(t\) an exact kernel exists for every \(s^2\ge\kappa t^2\). Here \(3/2\le\kappa_\Lambda<2\), so in particular a ratio \(s^2/t^2=2\) always suffices for a fixed lattice. If \(B\le2\lambda\), the sufficient condition is any fixed ratio strictly above \(3/2\), as on the line. No optimality is asserted for (1) or at either endpoint.

This is a substantial strengthening and geometric extension of [the one-dimensional exact-discretization note](exact-integer-gaussian-discretization.md): it improves its \(1.02\) obstruction to \(1.25-o(1)\) and works on all fixed lattice shapes, while extending the exact positive construction beyond orthogonal products. Standard Gaussian randomized rounding in [Peikert, Theorem 3.1 and §4.1](https://web.eecs.umich.edu/~cpeikert/pubs/pargauss.pdf) and [Lyubashevsky–Peikert–Regev, Toolkit §2.4.2](https://web.eecs.umich.edu/~cpeikert/pubs/toolkit.pdf) gives statistically approximate conversion, not this exact unknown-lattice-center experiment. No bounds on approximation error, finite-range parameters, modulo lattices, efficient implementation, or concrete schemes follow from (2).

## 1. Equivariance and growth in vertical strips

As in the one-dimensional argument, translation averaging over a growing lattice box preserves exactness and makes the kernel asymptotically equivariant under every fixed lattice translation: the error is bounded by the relative size of the translated box's symmetric difference. Take weak-star limits in \(L^\infty(\mathbb R^d)\) for each countably many output atoms along a diagonal subsequence. Nonnegativity and finite-sum bounds pass to the limit. For center zero the Gaussian integrals of all output atoms pass to the limit and sum to one, so monotone convergence against the strictly positive \(g_t\) gives normalization almost everywhere. Translating a test function is allowed in \(L^1\), hence equivariance holds in the limit. Taking one exceptional null set for all countably many relations, it follows that the problem is equivalent to finding a probability density \(p\ge0\) on \(\mathbb R^d\) with
\[
 \sum_{u\in\Lambda}p(u-x)=V_\Lambda^{-1}\quad\text{a.e. in }x,
 \qquad
 (g_t*p)(u)=\frac{\exp(-\pi\|u\|^2/s^2)}{V_\Lambda Z_s}
                  \quad(u\in\Lambda),                                  \tag{3}
\]
where \(Z_s=\sum_{u\in\Lambda}\exp(-\pi\|u\|^2/s^2)\). In one direction take \(p(x)=K(0\mid-x)/V_\Lambda\) for an equivariant kernel, and in the other take \(K(u\mid x)=V_\Lambda p(u-x)\). Integrating its periodization verifies the stated \(p\) normalization. With Fourier convention \(e^{-2\pi i z\cdot x}\), (3) implies \(\widehat p(v)=0\) for \(v\in L\setminus\{0\}\).

Put \(\Delta=s^2-t^2\), \(\gamma=t^2\Delta/s^2\), and let \(\nu\) be the law with density proportional to \(e^{-\pi\|x\|^2/t^2}p(x)\). Its normalizer is \(t^d/(V_\Lambda Z_s)\), by (3) at zero. Completing the square at each output point gives
\[
      \mathbb E_\nu e^{w\cdot X}=\exp(\gamma\|w\|^2/(4\pi))
           \qquad(w\in (2\pi/t^2)\Lambda).                              \tag{4}
\]
Using \(w,-w\) and Cauchy–Schwarz rules out \(\gamma<0\), and if \(\gamma=0\) the same equality on basis directions forces a point mass, impossible for a density. Thus \(0<\gamma<t^2\).

Fix a basis of \(\Lambda\) and let \(B_0\) be the sum of its vector lengths. Any \(w\in\mathbb R^d\) is a convex combination of vertices of a parallelotope in the mesh of (4), each of distance at most \(2\pi B_0/t^2\) from \(w\). Log-convexity of the moment transform and \(\sum_i a_i\|w_i\|^2=\|w\|^2+\sum_i a_i\|w_i-w\|^2\) show that
\[
 \mathbb E_\nu e^{w\cdot X}
   \le \exp\left(\gamma\|w\|^2/(4\pi)+\pi\gamma B_0^2/t^4\right).
\]
Undo the tilt using \(e^{\pi\|x\|^2/t^2}=\mathbb E_Y e^{Y\cdot x}\) for \(Y\sim N(0,(2\pi/t^2)I)\). Gaussian integration gives
\[
 \int e^{w\cdot x}p(x)\,dx
   \le C_s\exp\!\left(\pi\gamma B_0^2/t^4+\Delta\|w\|^2/(4\pi)\right),
 \qquad
 C_s=\frac{s^d}{V_\Lambda Z_s}
      =\left(\sum_{v\in L}e^{-\pi s^2\|v\|^2}\right)^{-1}\le1 .
\]
Here the untilt multiplies the normalizer by \((1-\gamma/t^2)^{-d/2}=(s/t)^d\), and replaces \(\gamma\) by \(\gamma/(1-\gamma/t^2)=\Delta\). Poisson summation gives the second expression for \(C_s\).

In particular \(\widehat p\) is entire, by domination on each bounded complex region using the finite exponential moments. Let
\[
       G(z)=e^{\pi\Delta z\cdot z}\widehat p(z),
 \qquad |G(x+iy)|\le K_\Lambda e^{\pi\Delta\|x\|^2},\quad t\ge1,         \tag{5}
\]
where \(z\cdot z\) is complex bilinear. The estimate follows because the factor from the imaginary coordinates in the exponential cancels the Fourier-transform growth from the moment bound. The resulting bound is uniform in the **entire** vertical strip in each real direction.

## 2. The stronger lower bound from one complex line

The convolution \(g_t*p\) is Schwartz: differentiate the Gaussian and use all finite moments of \(p\) to bound polynomially weighted derivatives. Therefore Poisson summation of (3) in real Fourier coordinates gives
\[
    \sum_{v\in L} e^{-\pi s^2(z+v)\cdot(z+v)}
                  [G(z+v)-C_s]=0.                                      \tag{6}
\]
Indeed the sum of translates of the convolution's Fourier transform equals \(V_\Lambda\) times the Fourier series of its samples, whose coefficients are \(D_{\Lambda,s}/V_\Lambda\). Applying Poisson again to \(D_{\Lambda,s}\) yields the factor \(C_s\), and \(t^2+\Delta=s^2\) gives the expression with \(G\).

Fix a shortest nonzero \(v_0\in L\). Equating (6) along \(z=u v_0\) is valid for every \(u\in\mathbb C\): the sums are normally convergent on compact subsets of the complex line, by (5) and \(s^2-\Delta=t^2>0\); the equality on the real line then extends by the identity theorem. Set \(F(u)=G(u v_0)-C_s\). On the boundary \(\operatorname{Re}u=0\) isolate \(v=0\) in (6). After division by its Gaussian factor, every other factor has modulus \(e^{-\pi s^2\|v\|^2}\), independent of \(\operatorname{Im}u\), because \(z\) is purely imaginary. From (5),
\[
 \sup_y|F(iy)|
  \le (K_\Lambda+1)\sum_{v\in L\setminus\{0\}} e^{-\pi t^2\|v\|^2}
  \le C_\Lambda e^{-\pi t^2\lambda^2}.                                  \tag{7}
\]
The last step factors out the least squared length and uses \(t\ge1\). The other boundary, \(\operatorname{Re}u=2\), satisfies \(\sup_y|F(2+iy)|\le (K_\Lambda+1)e^{4\pi\Delta\lambda^2}\) by (5). The same estimate bounds \(F\) throughout the strip. Hadamard's three-lines theorem at \(u=1\) gives
\[
 C_s=|F(1)|
      \le C'_\Lambda\exp(-\pi t^2\lambda^2/2+2\pi\Delta\lambda^2).
\]
Here \(G(v_0)=0\), by the first part of (3). Also \(C_s\) is bounded away from zero uniformly for \(s\ge t\ge1\). Rearranging gives (2).

## 3. A Voronoi choice of companion directions

For every \(k\in L\setminus\{0\}\) there is \(v_k\in L\cap2\mathcal V\) with
\[
                  v_k\ne0,\qquad k\cdot v_k\ge \|v_k\|^2.              \tag{8}
\]
If \(k\in2\mathcal V\) take \(v_k=k\). Otherwise a facet inequality of \(2\mathcal V\) is violated, with normal some \(v\in L\setminus\{0\}\) and threshold \(\|v\|^2\). Such a facet normal satisfies \(v/2\in\mathcal V\): for a point \(x\) on that facet of \(\mathcal V\), the equality \(\|x\|=\|x-v\|\) implies \(x\in v+\mathcal V\) as well (the two lattice points are both closest). Thus \(v-x\in\mathcal V\) by central symmetry, and the midpoint \(v/2\) is in \(\mathcal V\). This proves (8). Choose \(v_{-k}=-v_k\) by choosing on opposing pairs. Every chosen direction has norm between \(\lambda\) and \(B\).

## 4. Positive exact construction

Fix \(s^2/t^2=\kappa>\kappa_\Lambda\) and let \(t\to\infty\). Put
\[
       \beta=\Delta/s^2,\quad L_0=1/\beta,\quad \omega=t^2\beta,\qquad
       \Delta=t^2/(L_0-1).
\]
At any sample \(x\in\Lambda\), completion of squares gives
\(g_t(x-w)g_{\sqrt\Delta}(w)=g_s(x)g_{\sqrt\omega}(w-\beta x)\).
Choose pairs of real frequencies \(\alpha_k,\zeta_k\) for \(k\in L\setminus\{0\}\):
* For \(1<L_0<2\) take \(\alpha_k=k,\ \zeta_k=(1-L_0)k\) and \(D_k=1\).
* For \(2\le L_0<3\), put \(b=L_0-2\). The strict ratio condition says \(b<\min(1,2\lambda/B)\). Choose a fixed \(e\) with \(b/2<e<\min(1/2,\lambda/B)\), and set
  \[
    \alpha_k=k+e v_k,\quad
    \zeta_k=k+(e-L_0)v_k=(k-2v_k)+(e-b)v_k,\quad
    D_k=e^{-\pi\Delta e^2\|v_k\|^2}.
  \]

The difference \(\beta(\alpha_k-\zeta_k)\) is always in \(L\). Write
\(a_k=e^{-\pi\omega(\|\alpha_k\|^2-\|\zeta_k\|^2)}\).
It lies in \((0,1]\): for \(L_0<2\) the exponent difference is \(\omega L_0(2-L_0)\|k\|^2\); for \(L_0=2+b\), (8) gives a lower bound \(t^2(2e-b)\|v_k\|^2>0\) for the same quantity. Hence the functions
\[
 U_k(w)=e^{2\pi i \alpha_k\cdot w}
                        -a_k e^{2\pi i\zeta_k\cdot w}
\]
are bounded by two and have exactly zero mean under \(g_{\sqrt\omega}(w-\beta x)\) for every \(x\in\Lambda\): the Gaussian damping matches by definition and both phases coincide at the mean because \(\beta(\alpha_k-\zeta_k)\in L\).

We seek a bounded perturbation \(u=\sum_k c_k U_k\) such that \(g_{\sqrt\Delta}(1+u)\) has zero nonzero dual Fourier coefficients. This is the real matrix equation \(Tc=-h\) on \(L\setminus\{0\}\), where
\[
  h_j=e^{-\pi\Delta\|j\|^2},\qquad
  T_{jk}=e^{-\pi\Delta\|j-\alpha_k\|^2}
                       -a_k e^{-\pi\Delta\|j-\zeta_k\|^2}.
\]
Let \(\mathsf D\) be diagonal with entries \(D_k\). We show
\(\|T\mathsf D^{-1}-I\|_{\ell^1\to\ell^1}=o(1)\). For the primary term in the first case this follows immediately from the nonzero lattice Gaussian sum. Companion terms have uniformly small \(a_k\le e^{-\pi t^2(2-L_0)\lambda^2}\) and their shifted-Gaussian column sums are uniformly bounded for \(\Delta\ge1\). The latter follows, for instance, by reducing the shift to a bounded fundamental parallelepiped and bounding the ensuing tails.

In the second case \(v_k/2\in\mathcal V\) implies
\(|v_k\cdot w|\le\|w\|^2\) for all \(w\in L\). Thus
\[
 \|w-e v_k\|^2-e^2\|v_k\|^2\ge(1-2e)\|w\|^2.
\]
After normalization by \(D_k\) the primary diagonal is one and the off-diagonal columns tend to zero uniformly. Also \(|e-b|<1/2\). Using the same estimate centered now at \(k-2v_k\) gives
\[
 \sum_{j\in L} e^{-\pi\Delta\|j-\zeta_k\|^2}
   \le C_{\Lambda,e,b} e^{-\pi\Delta(e-b)^2\|v_k\|^2}.
\]
Multiply by \(a_k\) and divide by \(D_k\). The exponent bound is
\[
 -\pi[t^2(2e-b)-\Delta(e^2-(e-b)^2)]\|v_k\|^2
   = -\frac{\pi t^2(2e-b)}{1+b}\|v_k\|^2
   \le -\frac{\pi t^2(2e-b)}{1+b}\lambda^2.
\]
Here \(e^2-(e-b)^2=b(2e-b)\) and \(\Delta=t^2/(1+b)\). So the companion columns tend to zero also. This proves the norm claim.

Solve \(T\mathsf D^{-1}y=-h\) by the Neumann series and take \(c=\mathsf D^{-1}y\). We have
\[
 \|y\|_1=O_\Lambda(e^{-\pi\Delta\lambda^2}),\qquad
 \|c\|_1=o(1),
\]
since in the second case all \(D_k^{-1}\le e^{\pi\Delta e^2 B^2}\) and \(e^2B^2<\lambda^2\); in the first case \(\mathsf D=I\). The solution is real and satisfies \(c_{-k}=c_k\) by uniqueness and reflection of the real matrix. Since \(U_{-k}=\overline{U_k}\), the function \(u\) is real and \(\|u\|_\infty\le2\|c\|_1=o(1)\). Thus \(f_0=g_{\sqrt\Delta}(1+u)\) is positive.

The periodization of \(f_0\) is continuous by its Gaussian bound and all its nonzero Fourier coefficients vanish. Therefore its periodization is constant. The probability density \(p=f_0/\int f_0\) has periodization \(1/V_\Lambda\), as required in (3). The Gaussian product identity and the exact zero-mean property of every \(U_k\), summing the absolutely convergent series, give \((g_t*f_0)(x)=g_s(x)\) at all lattice sample points. Therefore the normalized \(g_t*p\) samples have the discrete-Gaussian shape; multiplied by \(V_\Lambda\) they sum to one by their periodization property. This proves (3) and constructs the kernel.

For a fixed sufficient \(\kappa\), a larger target width \(s^2\ge\kappa t^2\) is attained by first adding independent continuous Gaussian noise to bring the input width up to \(s/\sqrt{\kappa}\), which keeps its unknown center unchanged, and then applying the established fixed-ratio kernel. This proves the full positive statement.

**Replay.** Run `python3 verify-exact-lattice-gaussian-gap.py`. It checks rational Voronoi choices and companion exponents on synthetic lattice metrics and finite normalized-operator truncations. The proof uses the infinite operators and does not depend on numerical truncation.
