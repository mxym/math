# Adaptive Gaussian-noisy low-coordinate summaries in broad ring learning

Small low-coordinate-degree correlations do not by themselves control an arbitrary nonlinear decision on the values of those observables. In particular, exact real values can carry far more information than a linear mean test. This note gives an unconditional bound after a specified Gaussian/noise-energy constraint. A complex deformation of the adaptive transcript likelihood shows that every bounded transcript decision is uniformly approximable by a low-coordinate-degree test, without requiring a smooth decoder.

## 1. A transfer inequality for arbitrary product experiments

Let \(Q=\bigotimes_{j=1}^N Q_j\) be a reference probability space, and \(P\ll Q\) an alternative with likelihood \(L\in L^2(Q)\). The coordinate-degree-\(D\) space \(\mathcal H_{\le D}\) is the closed span in \(L^2(Q)\) of functions depending on at most \(D\) input coordinates. Let \(\Pi_{\le D}\) be the orthogonal projection, and put \(Z(D)=\|\Pi_{\le D}(L-1)\|_2^2\).

A transcript channel makes a finite number \(J\) of queries to the **same** input \(y\). Given the previous responses \(z_{<j}\), it receives
\[
 Z_j=x_j(y,z_{<j})+G_j,
 \qquad G_j\sim N(0,I_{m_j})
\]
with independent fresh Gaussians. The centered scale absorbs the chosen noise standard deviation, so \(\|x_j\|^2\) is the normalized energy, not the number of output coordinates. For every transcript prefix, each component of \(x_j(\cdot,z_{<j})\) has coordinate degree at most the given integer \(p_j\ge1\). Query choices can otherwise be arbitrary measurable functions of the previous transcript and public data, including randomization independent of \(y\). We require a deterministic bound, for some \(u>1\), valid on every input and transcript path:
\[
 \sum_{j=1}^J u^{2p_j}\|x_j(y,z_{<j})\|^2\le W(u).                \tag{1}
\]
Known offsets depending only on the public data and past can be subtracted without changing the channel's information.

For every integer \(D\ge0\), let \(e_D(u)=\exp(W(u)/2)u^{-D}/(u-1)\). If \(P^{\rm tr},Q^{\rm tr}\) are the laws of the whole transcript, then
\[
 \operatorname{TV}(P^{\rm tr},Q^{\rm tr})
 \le \tfrac12(1+e_D(u))\sqrt{Z(D)}+e_D(u).                         \tag{2}
\]
The bound is uniform over the queries, unrestricted postprocessing, their vector dimensions, and the number of adaptive steps, subject to (1). If the degrees are all at most a common \(p\), one can instead use the unweighted budget \(\sum_j\|x_j\|^2\le W\) and obtain (2) with \(Z(mp)\), for integer \(m\ge0\), and with
\[
 e_m^{\rm eq}(u)=\exp(u^2 W/2)\,u^{-m}/(u-1).                     \tag{3}
\]
This is a restriction on transcript access, not the class of arbitrary real-valued query computation or arbitrary algorithms.

## 2. Proof of adaptive approximation

Fix \(y\), and let \(\gamma\) be the baseline transcript law consisting of successive independent standard Gaussian vectors, with the same coordinate dimensions. The conditional transcript likelihood relative to \(\gamma\) is obtained by multiplying the one-step translated Gaussian likelihoods. On a fixed realized transcript \(z\), introduce a complex parameter \(w\):
\[
 G_y(w,z)=\exp\sum_{j=1}^J
 \left(w^{p_j}\langle z_j,x_j(y,z_{<j})\rangle
       -\tfrac12 w^{2p_j}\|x_j(y,z_{<j})\|^2\right).
                                                                    \tag{4}
\]
Here \(G_y(1,z)\) is the true channel density; it is essential that \(x_j\) in the formula is evaluated at the realized earlier coordinates \(z_{<j}\), not at coordinates recomputed under the deformation.

For \(|w|=u\), write \(a_j=\Re(w^{p_j})\), \(c_j=\Im(w^{p_j})\). Taking absolute values in (4) gives the real-mean shifted Gaussian transcript density with conditional shift \(a_j x_j\), times \(\exp(\frac12\sum c_j^2\|x_j\|^2)\). This real-mean likelihood integrates to 1 under \(\gamma\) by conditional Gaussian normalization, even under the history dependence. Consequently
\[
 \|G_y(w,\cdot)\|_{L^1(\gamma)}\le \exp(W(u)/2).                   \tag{5}
\]
One also has \(\|G_y(w,\cdot)\|_{L^2(\gamma)}\le \exp(W(u)/2)\): its squared magnitude is the likelihood with conditional shifts \(2a_jx_j\), times \(\exp(\sum(a_j^2+c_j^2)\|x_j\|^2)\). The \(L^1\) form is enough for bounded decisions.

For fixed \(y,z\), expand \(G_y(w,z)=\sum_{n\ge0}w^n C_n(y,z)\). Cauchy's integral formula and (5) give
\(\|C_n(y,\cdot)\|_{L^1(\gamma)}\le u^{-n}\exp(W(u)/2)\).
Their sum at \(w=1\) converges absolutely in \(L^1(\gamma)\) to \(G_y(1,\cdot)\). For every measurable real \(\varphi\) with \(|\varphi|\le1\), put \(F(y)=\mathbb E[\varphi(Z)\mid y]\), and
\[
 F_{\le D}(y)=\mathbb E_\gamma\left[\varphi(z)\sum_{n=0}^D C_n(y,z)\right].
\]
Then \(|F(y)-F_{\le D}(y)|\le e_D(u)\) uniformly in \(y\). Also \(F_{\le D}\in\mathcal H_{\le D}\). In fact for fixed \(z\) the coefficient \(C_n\) is a finite sum of products of factors of degree at most \(p_j\) (from a linear drift term of weight \(p_j\)) or \(2p_j\) (from a squared drift term of weight \(2p_j\)), with total weight \(n\). Products of bounded coordinate-degree functions have degree at most the sum: on a finite product, their ANOVA components are obtained by inclusion-exclusion of conditional expectations, are bounded, and each product term depends on a union of its component coordinates. The budget bounds each queried function on fixed \(z\). The integrated coefficient is in the same closed space: it is bounded by (5) and its inner product with any \(L^2\) orthogonal function is zero by Fubini. Absolute integrability in this interchange follows from the uniform \(L^1(\gamma)\) coefficient bound and \(L^2(Q)\subseteq L^1(Q)\).

Thus \(\|F_{\le D}\|_2\le1+e_D(u)\), and
\[
 |\mathbb E_P F-\mathbb E_Q F|
 \le (1+e_D(u))\|\Pi_{\le D}(L-1)\|_2+2e_D(u).
\]
Take the dual TV supremum to obtain (2). For (3), deform **every** drift by \(w\) rather than \(w^{p_j}\); the \(n\)-th coefficient then has degree at most \(np\), and the identical proof uses \(u^2W\) in place of \(W(u)\).

If the planner uses independent random seeds, reveal the seeds also to the decision and condition on their values; the same bound holds uniformly and averaging gives (2). There is no bound on the subsequent nonlinear computation. Zero drifts or padding after a bounded stopping rule are also covered. Without the pathwise normalized energy condition this proof gives no control of the tail.

## 3. Prescribed label features

Suppose a label \(S\) with fixed prior is used to generate \(Y\), each conditional likelihood \(L_s\) relative to \(Q\) is square integrable, and the channel operates on \(Y\) as above (not on \(S\)). For any centered label function \(h\) of unit \(L^2\) norm, write \(H_h=\mathbb E_S h(S)L_S\). For every bounded transcript decision \(\varphi\),
\[
 |\mathbb E[h(S)\varphi(Z)]|
 \le (1+e_D)\|\Pi_{\le D}H_h\|_2+e_D.                            \tag{6}
\]
This is the same approximation with residual cost \(e_D\mathbb E|h|\le e_D\), not \(2e_D\). It applies even if the function \(h\) is selected after public data, provided the projected bound used is simultaneous over that selection.

For a finite feature \(U=f(S)\) with class probabilities \(a_v>0\), define \(h_v(S)=(\mathbf1_{\{U=v\}}-a_v)/\sqrt{a_v(1-a_v)}\) if \(a_v<1\). The joint independence TV is bounded by
\[
 \operatorname{TV}(P_{U,Z},P_U\otimes P_Z)
 \le \frac{1+e_D}{2}\sum_v\sqrt{a_v(1-a_v)}\|\Pi_{\le D}H_{h_v}\|_2+e_D.       \tag{7}
\]
Indeed a bounded test can depend separately on \(v\); apply the polynomial approximation to each of its \(v\)-sections and sum the centered-indicator correlations. The tail cost is bounded by \(e_D\sum_v2a_v(1-a_v)\le2e_D\) before dividing by two. This avoids multiplying the approximation error by the number of classes.

## 4. Explicit range in a broad wrapped ring model

Use the setting of the [conditional coordinate-degree spectrum theorem](https://github.com/mxym/math/blob/1aaf3b754c946fbefcfadcdee20fd3ae10648a1b/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-coordinate-degree-and-tv.md): fixed odd \(q\ge3\), \(R=(\mathbb Z/q)[X]/(X^d+1)\), uniform label in \(R\), independently uniform public rows, wrapped coefficient noise with Fourier coefficients \(b^{h^2}\), \(b=\beta/d\), \(T b^2\to t\in(0,\infty)\), and grid-shift-averaged product reference. Fix the whole design \(A\) before applying the theorem. The channel may select all its queries using \(A\).

For any constant \(\alpha>0\) such that
\[
 K_t(\alpha):=\max_{0\le x\le\alpha} x(1+\log(2t/x))<\log q,         \tag{8}
\]
put \(D=\lfloor\alpha d\rfloor\). The prior theorem implies \(\mathbb E_A\sqrt{Z_A(D)}\le e^{-c d}\) for some \(c>0\). In its binomial expression the product of the number of scalar coordinates and the scalar nonconstant squared weight is \(2td(1+o(1))\), so \(\binom Nj B^j\le (e N B/j)^j\) gives exponential upper rate \(K_t(\alpha)\); the prior absolute-error bound is itself exponentially small. The convention at \(x=0\) is zero. This reasoning uses the actual bound behind (8), not merely the fact that \(D=o(d)\).

For equal maximal query degree \(p=p_d=o(d)\), take \(m=\lfloor D/p\rfloor\to\infty\). If \(p W/d\) stays below \(\alpha/e\) by a positive fixed margin, the adaptive transcript TV tends to zero in expectation over \(A\), and hence in probability. In fact choose \(u>1\) fixed with \((u^2/2)(W/m)<\log u\) by a strict margin for large \(d\): the maximum of \(2\log u/u^2\) is \(1/e\) at \(u=\sqrt e\). Then (3) is exponentially small in \(m\); (2) handles the rest uniformly. For mixed degrees, the directly usable condition is \(\exp(W(u)/2)u^{-D}/(u-1)\to0\) for any sequence of radii \(u>1\), with \(W(u)\) from (1). The factor \(1/e\) is only a sufficient condition for this Taylor bound, not a proved boundary for allowed channels.

The phenomenon applies even for fixed \(t>\log q\), when the **uncompressed** response laws have TV tending to 1 by the prior theorem. There is still a positive allowed \(\alpha\) in (8), since \(K_t(\alpha)\to0\) as \(\alpha\downarrow0\). For a prescribed balanced label bit, use (6) and the corresponding prior exponential bound on its projected likelihood to get vanishing advantage. For a prescribed feature with multiple classes, the same argument proves (7) when the sum of their square roots times the projected bound tends to zero, including exponentially many classes with sufficiently small rate. The summable classes here must be prescribed before the design for that exponential estimate; a design-selected normalized bit is instead controlled by the simultaneous polynomial estimate from the prior theorem, still giving vanishing advantage. These statements do not imply full label indeterminacy for all rates or access through unperturbed, infinite-precision values.

## 5. Prior and boundary

[Kunisky, Low Coordinate Degree Algorithms I](https://arxiv.org/abs/2403.07862) sets out the ANOVA projection framework for local-coordinate observables. [Kunisky–Wein–Bandeira, Notes on Computational Hardness of Hypothesis Testing](https://arxiv.org/abs/1907.11636) explains the general low-degree likelihood-ratio method and separates its predictions from unrestricted computational statements. The projected spectrum and uncompressed TV in §4 are from the linked earlier work and are not newly claimed here. The new ingredient is the positive real-Gaussian normalization after complexifying an arbitrarily adaptive transcript likelihood, producing (2) and (7) for bounded nonlinear decisions on one repeatedly queried batch. That is a different access model from independent fresh-batch communication or an oracle for exact real-valued observables.

All examples in the checker are small probability and polynomial identities. No method of solving the ring problem, any scheme security inference, or a general time lower bound is supplied.
