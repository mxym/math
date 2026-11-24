# Central Goldbach spectrum: uniform signed-cell quantization

This note proves a finite-dimensional approximation for the old central signed operator. It does not give the pointwise arithmetic estimates needed to certify its spectral criterion. No GRH is used in this approximation.

## 1. Exact rescaling and the obstruction to transferring the old counterexample

Let \(N\) be even and large, \(a=1/3,\ b=2/3,\ L=b-a\), and \(S(N)=2C_2\prod_{p\mid N,p>2}(p-1)/(p-2)\) be the binary Goldbach singular series, where \(C_2=\prod_{p>2}(1-(p-1)^{-2})>0\). Define the central operator on \(L^2([\log(Na),\log(Nb)],dr)\). Its kernel uses the difference
\[
S(N)\int_{N-Y}^{X}\sqrt{x(N-x)}\,dx
-\sum_{\substack{N-Y\le n\le X\\(n,N)=1}}\Lambda(n)\Lambda(N-n)\sqrt{n(N-n)}
\]
multiplied by \(2\pi\sqrt{W_N(r)W_N(s)}/(XY)\), with \(X=e^r,\ Y=e^s\). The kernel is zero if \(X+Y<N\). Here \(W_N(r)=e^{-2\alpha r}+e^{-2\beta r}\), \(\alpha=1/\log N,\ \beta=1/8\). The kernel definition and its Goldbach quadratic form follow directly by Fubini, independently of the identification under GRH with the original Hardy-space operator.

Use the unitary \(f\mapsto u^{-1/2}f(\log(Nu))\) to transport this to \(L^2([a,b],du)\); denote the transported operator by \(T_N\). Introduce reflected (under \(t\mapsto1-t\)) measures
\[
\nu_N=\frac1N\sum_{\substack{n/N\in[a,b]\\(n,N)=1}}\Lambda(n)\Lambda(N-n)\delta_{n/N},
\quad \tau_N=S(N)\,dt-\nu_N,\quad
d\sigma_N(t)=\sqrt{t(1-t)}\,d\tau_N(t).
\]
Set \(\rho_N(u)=\sqrt{2\pi W_N(\log(Nu))}\,u^{-3/2}\) and \(v_t(u)=\rho_N(u)\mathbf1_{\{u\ge t\}}\). The rescaled kernel is
\[
T_N=\int_{[a,b]} v_t\otimes v_{1-t}\,d\sigma_N(t).
\]
Indeed, \(x=Nt\) makes the integrand/measure product in the first term of the braces scale by \(N^2\); the discrete term divided by \(N^2\) is the \(\nu_N\)-integral. The unitary adds \(1/\sqrt{uv}\) to the scaled kernel. The condition \(1-v\le t\le u\) gives the two indicators. If equality makes a discrete jump, the above formula specifies it; changing its pointwise boundary value on a null set does not affect \(T_N\). The rank-one tensor is \(f\mapsto v_t\langle v_{1-t},f\rangle\) with the inner product linear in its second input. Reflection makes \(T_N\) self-adjoint. Uniformly for \(N\ge4\), \(\|\rho_N\|_\infty\le C_\rho=\sqrt{4\pi}\,a^{-3/2}\).

Yilin Liu's counterexample for the old Theorem R is [the HexagonMath preprint 2611.00788v1](https://hexagonmath.org/pdf/2611.00788v1), not the unrelated arXiv record with those digits. The witness in the bilinear formulation uses one argument supported at \(t\asymp m/N\), where \(m\) is polylogarithmic in \(N\), and the other near \(1\), at distance \(O(m/N)\). In logarithmic coordinates these arguments live near \(r\sim\log m\) and \(s\sim\log N\), respectively, not in \([\log(N/3),\log(2N/3)]\). More directly, in the compressed kernel \(X,Y\in[N/3,2N/3]\) force every possible correlation input \(n\in[N-Y,X]\) to be in \([N/3,2N/3]\), so the near-endpoint correlations used in Liu vanish identically from the compression. This explains why *that witness* cannot be transplanted or its global norm ratio used as a lower bound here. It is not a proof (or evidence from the witness alone) that the central positive-spectrum threshold holds. In particular, independently finding a different central witness remains logically possible.

## 2. One signed mass per cell captures the top spectrum

Take \(m\ge1\) equal cells \(I_j\) of length \(h=L/m\), viewed as closed for mass upper bounds, with midpoints \(x_j=a+(j-\tfrac12)h\). Let \(\chi_j\) be the characteristic membership weight, except that at an internal boundary the two adjacent weights are each \(1/2\). Assign an interval endpoint wholly to its unique incident cell. These weights sum to one and satisfy \(\chi_{m+1-j}(1-t)=\chi_j(t)\). Define
\[
s_j=\int\chi_j(t)\,d\sigma_N(t),\quad
T_{N,h}=\sum_{j=1}^{m}s_j\,v_{x_j}\otimes v_{1-x_j},
\quad M=|\sigma_N|([a,b]),\quad \Gamma_h=\max_j|\sigma_N|(I_j).
\]
The approximant is self-adjoint because \(s_j=s_{m+1-j}\). Its nonzero action is represented by the real symmetric matrix
\[
A_{N,h}=G^{1/2}\operatorname{diag}(s_j)J G^{1/2},\quad
G_{ij}=\int_{\max(x_i,x_j)}^{b}\rho_N(u)^2du,
\]
where \(J\) reverses indices. In fact \(V e_j=v_{x_j}\) gives \(V^*V=G\), the distinct nested step vectors are linearly independent on intervals of positive length (and \(\rho_N>0\)), and \(VG^{-1/2}\) is an isometry onto their span. The operator is zero on its orthogonal complement. The Gram integrals are explicit:
\[
G_{ij}=2\pi\sum_{\gamma=\alpha,\beta}
\frac{N^{-2\gamma}}{2+2\gamma}
\big(\max(x_i,x_j)^{-2-2\gamma}-b^{-2-2\gamma}\big);
\]
the sum has two terms even in case of equal parameters.

Define \(\lambda_+(T)=\max(0,\sup_{\|f\|_2=1}\langle f,Tf\rangle)\) for a self-adjoint \(T\). Then
\[
\big|\lambda_+(T_N)-\max(0,\lambda_{\max}(A_{N,h}))\big|
\le\|T_N-T_{N,h}\|\le 2C_\rho^2\sqrt{Lh\,M\Gamma_h}. \tag{1}
\]
To prove the norm estimate, split the difference at a pair \((t,j)\) into
\[
(v_t-v_{x_j})\otimes v_{1-t}+v_{x_j}\otimes(v_{1-t}-v_{1-x_j}).
\]
The difference vector in the first summand is bounded by \(C_\rho\), supported in \(I_j\), and has support length at most \(h\). Its absolute row integral is uniformly at most \(C_\rho^2 L\Gamma_h\): outside the null set of cell boundaries the first coordinate determines the only possible cell. Its absolute column integral is at most \(C_\rho^2 h M\): integrate the difference-support length over \(t\) and the partition weights. The second summand has the reflected cell in the second coordinate, so the bounds are interchanged. Schur's test gives the estimate; the spectral inequality then follows by the variational formula. Atoms at grid boundaries are handled by the membership split; the coordinate boundary set excluded in estimating essential suprema has Lebesgue measure zero.

If one wants the matrix to use *unweighted* signed cell totals \(\int\chi_j\,d\tau_N\), replace \(s_j\) by \(\sqrt{x_j(1-x_j)}\int\chi_j\,d\tau_N\). The additional operator error is \(O(h|\tau_N|([a,b]))\) because the weight is Lipschitz on the central interval, and \(\|v_{x_j}\otimes v_{1-x_j}\|\le C_\rho^2L\). The signed counts can therefore be plain central interval Goldbach counts at essentially the same accuracy.

## 3. Elementary uniform upper bound for the variation in a cell

Uniformly for intervals \(I\subseteq[a,b]\), and large even \(N\),
\[
\nu_N(I)\ll S(N)(|I|+N^{-1})+N^{-1/2}\log^3 N. \tag{2}
\]
Here is a self-contained Selberg upper sieve argument. Put \(z=N^{1/12}\), \(P(z)=\prod_{p<z}p\), \(\mathcal D=\{d:d\mid P(z),\ d\le z\}\), and let \(X\) be the number of integers of \(NI\), so \(X\le N|I|+2\). For any squarefree \(d\mid P(z)\), let \(\omega(d)=\prod_{p\mid d}\omega(p)\) with \(\omega(p)=1\) when \(p\mid N\) and \(2\) otherwise, and let \(g(d)=\omega(d)/d\). Counting residue classes with \(d\mid n(N-n)\) gives \(Xg(d)+O(\omega(d))\) by CRT. Since \(N\) is even, \(0<g(p)<1\) including at \(p=2\).

Let \(H(d)=\prod_{p\mid d}\frac{g(p)}{1-g(p)}\) and \(F(z)=\sum_{r\in\mathcal D}H(r)\). Weights \(\lambda_1=1\) and \(\lambda_d\) supported on \(\mathcal D\) give an upper bound on the sifted count by summing \((\sum_{d\mid n(N-n)}\lambda_d)^2\). The main quadratic form is
\[
\sum_{d,e\in\mathcal D}\lambda_d\lambda_e g([d,e])
=\sum_{r\in\mathcal D}\frac{y_r^2}{H(r)},\quad
y_r=\sum_{\substack{d\in\mathcal D\\r\mid d}}\lambda_d g(d).
\]
This follows from \(g([d,e])=g(d)g(e)/g((d,e))\) and \(1/g(k)=\sum_{r\mid k}1/H(r)\) for squarefree \(k\), both checked primewise. Take \(y_r=\mu(r)H(r)/F(z)\). Möbius inversion on this divisor-closed set gives
\[
\lambda_dg(d)=\mu(d)F(z)^{-1}\sum_{\substack{r\in\mathcal D\\d\mid r}}H(r),
\]
so \(\lambda_1=1,\ |\lambda_d|\le1/g(d)\le d\), and the quadratic form is \(1/F(z)\). The elementary remainder is \(O(z^6)\): at most \(z^2\) pairs \(d,e\), coefficient product at most \(z^2\), with CRT remainder at most \(\omega([d,e])\le[d,e]\le z^2\).

For a small absolute \(\delta>0\) let \(y=z^\delta\). Independently include each prime \(p\le y\) in a squarefree random \(d\) with probability \(g(p)\). Its probability mass is \(H(d)/\prod_{p\le y}(1+H(p))\), and
\(\mathbb E\log d\le2\sum_{p\le y}(\log p)/p\ll \log y\).
The latter follows by dyadic central binomial coefficient bounds for \(\sum_{p\le x}\log p\ll x\) and partial summation. Choosing \(\delta\) small makes the expected logarithm at most \(\tfrac12\log z\), so at least half the mass lies on \(d\le z\) by Markov. Thus \(F(z)\ge\tfrac12\prod_{p\le y}(1-g(p))^{-1}\). Computing the finite Euler product gives
\[
\prod_{p\le y}(1-g(p))=
2\prod_{p\le y}(1-1/p)^2\!
 \prod_{2<p\le y}(1-(p-1)^{-2})\!
 \prod_{\substack{2<p\le y\\p\mid N}}\frac{p-1}{p-2}
\ll \frac{S(N)}{(\log N)^2}.
\]
Indeed the truncated \(N\)-divisor product is bounded by the full one; the middle product is at most one and \(C_2>0\); and \(\prod_{p\le y}(1-1/p)^{-1}\ge\sum_{k\le y}1/k\gg\log y\). No prime number theorem nor asymptotic Mertens product is needed.

The sifted count is consequently \(O(S(N)(N|I|+1)/\log^2 N+\sqrt N)\). It includes all prime pairs with central inputs once \(N/3>z\); the coprimality condition only decreases the upper bound. There are \(O(\sqrt N\log N)\) proper prime powers \(\le N\), by a trivial count by exponent, hence at most twice as many inputs \(n\) with either coordinate such a power. Each weight is at most \(\log^2N\). Multiplication by the weight bound and division by \(N\) now prove (2).

As \(S(N)\gg1\) and the factor \(\sqrt{t(1-t)}\le1/2\), (2) gives \(M\ll S(N)\) and \(\Gamma_h\ll S(N)(h+N^{-1/2}\log^3N)\). Absorb \(N^{-1}\) into the latter additive term. In (1) this yields the uniform estimate
\[
\big|\lambda_+(T_N)-\max(0,\lambda_{\max}(A_{N,h}))\big|
\ll S(N)\big(h+\sqrt{h}\,N^{-1/4}\log^{3/2}N\big). \tag{3}
\]
For any fixed normalized accuracy \(\epsilon>0\) and large \(N\), one can use \(m=O(\epsilon^{-1})\) signed cell totals to approximate \(\lambda_+(T_N)/S(N)\) to accuracy \(\epsilon\). The dimension is independent of \(N\). The comparison (1) also gives a measurable alternative error bound in terms of actual variation; (3) does not supply a numerical constant suitable for a particular finite cutoff.

## 4. What has and has not been reduced

Write the old central identity as \(G_\varphi(N)=c_\varphi S(N)-\langle T_N F_{v,N},F_{v,N}\rangle\), with \(c_\varphi=\int\varphi^2>0\) and \(Q_N=\|F_{v,N}\|^2\). The matrix upper bound plus (1) implies \(G_\varphi(N)>0\) if \(Q_N(\max(0,\lambda_{\max}(A_{N,h}))+\mathrm{err})<c_\varphi S(N)\). A margin bounded below as a fraction of \(S(N)\), together with the negligible contribution of proper prime powers, gives the desired prime rather than prime-power conclusion for large \(N\). Neither such a margin nor a useful signed arithmetic bound on the matrix cells is proved here. With the hypothetical measure \(\nu_N=0\), the old identity is at equality in the wrong direction and no strict spectral criterion can hold; (2) permits that measure. This illustrates in the exact finite-dimensional model why a one-sided upper sieve is only an approximation input, not a positivity proof.

The public reference project's accepted arc-major-floor and conditional arc-budget-transfer isolate the same missing pointwise arithmetic in a different representation. A prime existing in a short *target interval* is not control of a cell in the *summand variable for each fixed target*; accepted central support-overlap/many/weighted-witness results also do not furnish prime-pair cell masses. Relevant references for comparison: [arc-major-floor accepted run](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45427083174), [conditional budget transfer](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45400934956), [RH short-interval run](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45379729647), [central overlap run](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45432474202). The approximation is an unconditional analytic reduction, not a new result about pointwise signed minor arcs, and priority/novelty has not been searched fully.
