# Identical absolute spectra do not determine a signed fixed-target remainder

This is a diagnostic for the [direct binary signed problem](DirectGoldbachThinRationalArcs.md): a pair of artificial, nonnegative, locally admissible weights can have identical absolute Fourier spectra, square-root-scale one-point proximity to the same background, and the same positive signed major main term, yet completely different signed complements. Neither weight is the prime indicator. This is separate from the [single prime-supported weight construction](SignedMinorFourierObstruction.md), which retains actual prime support but does not impose identical spectra of two models.

Fix a nonzero nonnegative symmetric \(C^\infty\) function \(w\) supported in the interior of \([1/3,2/3]\). Let \(N\) be even and large, \(L=\log N,\ z=L/100,\ W=\prod_{p\le z}p,\ \gamma=W/\varphi(W)\). The prime number theorem and Mertens' theorem give \(W\le N^{.02}\), \(\gamma\ll\log L\). Put \(b(n)=\gamma w(n/N)1_{(n,W)=1}\), \(F_f(\alpha)=\sum_n f(n)e(n\alpha)\).

## Exact magnitudes and two different totals

In each two-element orbit of \(n\mapsto N-n\) in \([1,N-1]\), independently select at most one admissible element, with probability \(\gamma/L\) for each admissible element (and otherwise none). The midpoint is omitted. Let \(f_-(n)=Lw(n/N)\) at selected elements and zero elsewhere, and \(f_+(n)=f_-(n-W)\). Since \(W=o(N)\), both supports stay within \([N/3,2N/3]\) for sufficiently large \(N\). The translation is on the integers, not a cyclic shift. It preserves the true unit condition modulo \(W\), and
\[
 |F_{f_-}|=|F_{f_+}|\quad\text{everywhere},\qquad (f_-*f_-)(N)=0 .
\]

The translated target count is \((f_-*f_-)(N-2W)\). Its entries are from different independent original orbits except for \(O(1)\) ordered pairs affected by equal input indices or the omitted midpoint. The admissible periodic density for this convolution is
\[
 \delta_W=\prod_{\ell\le z,\ \ell\ {\rm prime}}(1-\nu_\ell/\ell),
 \qquad
 \nu_\ell=\begin{cases}1&\ell\mid N,\\2&\ell\nmid N.\end{cases}
\]
The two translated-sum forms have actual target \(N-2W\equiv N\bmod W\). Let \(\mathfrak S_z(N)=\gamma^2\delta_W\); it is bounded below by a positive constant on even \(N\). Summation along the true period \(W\) and symmetry and smoothness of \(w\) give
\[
 \mathbb E(f_+*f_+)(N)=N\mathfrak S_z(N)\int w^2+O_w(\gamma^2W+L^2).
\]
In detail, the product \(w(n/N)w(1-2W/N-n/N)\) has uniformly bounded variation as a function of \(n/N\); period summation costs \(O_w(\gamma^2W)\), and replacing \(2W/N\) by zero costs the same. Resampling any one orbit changes only \(O(1)\) terms of size \(O_w(L^2)\), so bounded difference or its variance inequality gives deviations \(o(N)\) with probability tending to one (for example use the threshold \(N^{3/4}\)). The truncated local factor is asymptotic relatively to the usual \(\mathfrak S(N)\): for target primes exceeding \(z\), their total reciprocal mass is \(O(L/(z\log z))=o(1)\), and the remaining universal tail is absolutely convergent.

## Uniform one-point comparison and signed major term

For each frequency, the independent centered orbit summands of \(F_{f_-}-F_b\) have size \(O_w(L)\) and total variance \(O_w(NL)\). Indeed the variance is bounded by the sum of the second moments, at most \(O_w(\gamma L\sum_n w(n/N)^2 1_{(n,W)=1})=O_w(NL)\), using the period and \(W\ll N^{.02}\); the midpoint mean discrepancy is \(O_w(\gamma)\). Bernstein and a union bound on an \(N^{-3}\)-mesh give \(\|F_{f_-}-F_b\|_\infty\ll_w\sqrt N L\) with probability tending to one. Their deterministic derivatives have size \(O_w(N^2L)\), so the mesh extends this to all frequencies. Translating \(b\) by \(W\) changes its \(\ell^1\) norm difference by \(O_w(\gamma W)\), hence the same estimate relative to \(b\) holds for \(f_+\). Fix an outcome with these estimates and the required translated target count. Also \(\|F_{f_\pm}\|_2^2=O_w(NL)\), since each \(f_\pm\le L\|w\|_\infty\) and \(F_{f_\pm}(0)=O_w(N)\). The deterministic background has this squared norm bound as well.

Take \(\mathcal M\) to be the union of arcs of radius \(H/N\) centered at all \(a/W\), with \(H=L^3\). The \(W\)-periodic function \(\gamma1_{(n,W)=1}\) has Fourier coefficients \(c_a\) with \(|c_a|\le1,\ \sum_a|c_a|^2=\gamma\). By Poisson for the smooth window, the translated profile at \(a/W\) is bounded by \(C_{w,k}N(1+N\|\alpha-a/W\|)^{-k}|c_a|\). On a nearest-center cell all other profiles together are \(O_{w,k}(N(W/N)^k)\), by their spacing. The squared mass off \(\mathcal M\) of the nearest profiles is \(O_{w,k}(N\gamma H^{1-2k})\); including the other profiles still gives \(o(N)\). Hence the real signed major coefficient at \(N\) for the background equals its exact convolution up to \(o(N)\), namely \(N\mathfrak S_z(N)\int w^2+o(N)\).

On a set of measure \(m\), replacing \(F_b^2\) by either actual model square changes the signed integral by at most
\[
 \|F_{f_\pm}-F_b\|_\infty\,\sqrt m\,\|F_{f_\pm}+F_b\|_2
       \ll_w NL^{3/2}\sqrt m .
\]
Here \(|\mathcal M|\ll WH/N\), so both signed majors are the same positive \(N\mathfrak S_z(N)\int w^2+o(N)\). Both absolute spectra, and consequently their absolute integrals on *every* subset, agree exactly. The signed complements nevertheless are \(-N\mathfrak S_z(N)\int w^2+o(N)\) for \(f_-\) and \(o(N)\) for \(f_+\).

## Conventional low denominators for a dyadic target

When \(N=2^k\), the same dichotomy already holds for reduced \(a/q\), \(q\le z\), and radius \(H/N\). The background has matching periodic Fourier coefficient \(\mu(q)/\varphi(q)\) if \(q\mid W\) and zero otherwise; nonmatching centers in the \(W\)-bank are at distance at least \(1/(qW)\) and give negligible smooth tails. Integrating the matching profile gives \(N\int w^2\) times \(\sum_{q\le z}\mu^2(q)c_q(N)/\varphi(q)^2\), up to \(o(N)\), with \(c_q\) the Ramanujan sum. On the squarefree support and for dyadic \(N\), \(|c_q(N)|=1\); the tail is absolutely summable, and the truncated sum differs from \(\mathfrak S_z(N)\) by \(o(1)\). The major-set measure is now \(O(z^2H/N)\), so the two comparison errors are also \(o(N)\).

The translation ambiguity of Fourier magnitude is standard; the exclusion and concentration here match it to this particular signed coefficient and positive major model. These sequences depend on \(N\) and imitate stated distribution data, not arithmetic identities for \(\Lambda\). Thus this example rules out deducing a uniform signed minor floor from the stated magnitude, local support and one-point major data alone. It gives no bound and no counterexample for actual Goldbach representations.
