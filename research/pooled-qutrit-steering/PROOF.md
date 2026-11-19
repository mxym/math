# A uniform gap for the pooled qutrit Werner steering witness

**Research note by Yongxian Zhang.** AI-assisted; independently checked in an internal AI review, not externally peer reviewed. For every number of measurements and every choice of complete complex qutrit projective bases, the Yang–Qiao direct-sum majorization Werner threshold in their Table 1 satisfies
\[
 \eta^* \ge \frac23+\frac4{2223}=\frac{1486}{2223}.
\]
Consequently the Werner half of the conjectured convergence immediately following Eq. (25) and Fig. 2 in [the published paper](https://doi.org/10.1038/s41534-026-01204-3) cannot hold for this particular witness. This does **not** change the physical projective-steering threshold \(2/3\), assert an optimal numerical pooled threshold, or cover all steering witnesses/aggregations. The isotropic prediction \(5/12\) is treated by a different argument [in the companion proof](ISOTROPIC.md).

## Which bound is pooled?

In [the published manuscript](https://www.nature.com/articles/s41534-026-01204-3_reference.pdf), Eq. (16) sums the largest \(L\) entries of the full direct sum; Eq. (21) gives a Werner triple with two entries \((2+\eta)/6\) and one \((1-\eta)/3\). Equations (22), (24) and Table 1 identify the Werner cutoff at \(L=2N\):
\[
 \eta^*=1-\frac3N(N-\Omega_{2N}).
\]
Eq. (25) literally displays the isotropic objective \(\bar\Omega_N\); the surrounding Fig. 2(b), the separate Table 1 formula, Eq. (24), and the paragraph following the numerical results specify the Werner objective. The paper's [author manuscript](https://arxiv.org/html/2507.20950v2), Eqs. (32)–(33) and (S13)–(S14), defines \(\Omega_L\) by taking the operator norm of the sum of \(L\) rank-one basis projectors. Subsets in different settings may have different sizes, possibly zero; only their **total** must equal \(L\). Fixing exactly two per basis would change the result.

Each basis contributes total mass one at every state. By the variational principle one can equivalently maximize over pure states \(\psi\) the sum of the \(2N\) largest of the \(3N\) probabilities \(p_{Bj}(\psi)=|\langle b_j,\psi\rangle|^2\). Hence \(h=(N-\Omega_{2N})/N\) is the minimum over \(\psi\) of \(1/N\) times the sum of the \(N\) *smallest* pooled entries. If the least majorization upper bound is constructed by taking a concave Lorenz envelope rather than just these raw suprema, its height at \(2N\) can only be higher. In the Werner case the target Lorenz curve is piecewise affine, with its only possible non-endpoint corner at \(2N\); a concave bound above the target there and at both endpoints is above the entire target. Thus flattening does not remove the obstruction. Only the specified, aligned Werner vector is used here.

## One exact bound for all setting distributions

More generally let \(\mu\) be any probability distribution on ordered orthonormal bases of \(\mathbb C^3\) (a measure on unordered bases can be randomly ordered). For a fixed \(\psi\), define \(G(\psi)\) as the least cost of selecting total mass one from the three units of outcome mass:
\[
 \inf\left\{\int\sum_{j=1}^3 u_j(B)p_{Bj}\,d\mu(B):\quad
 0\le u_j(B)\le1,\quad \int\sum_j u_j(B)\,d\mu(B)=1\right\}.
\]
Selection functions are measurable. For \(N\) equally weighted settings it equals the normalized sum of the \(N\) smallest entries, even at ties. An exactly equivalent cutoff formula is
\[
 G(\psi)=\max_{0\le t\le1} g_\psi(t),\qquad
 g_\psi(t)=t-\int\sum_j(t-p_{Bj})_+\,d\mu(B).
\]
Indeed any feasible choice costs at least \(g_\psi(t)\). At a lower one-third quantile of the pooled probability values (with total output mass three), take all outcomes strictly below it and a suitable common fraction at equality. This achieves that value, for arbitrary atoms including degenerate probability values. Both \(g_\psi(t)\) and its maximum are continuous in \(\psi\), by joint continuity on the compact bases, rays and cutoff domain; taking the minimum \(h=\min_\psi G(\psi)\) is legitimate. The formula is also jointly continuous in \(\mu\) with its weak topology: if \(\psi,t\) converge along with \(\mu\), the integrand converges uniformly in the basis, and the limit integrand is continuous. The ensuing proof is directly uniform in \(\mu\); no limiting ensemble or non-atomic choice of settings is needed.

Let \(x\le y\le z\) be a given basis's three values at state \(\psi\). Write \(\alpha(\psi)=\int x\,d\mu\), and \(\beta(\psi)=\mu\{B:y\le s\}\) for a scalar \(0<s<1/3\). Choosing the smallest outcome from each basis is permitted, so \(\alpha\ge G\ge h\). The exact cutoff deficit is
\[
 \alpha-g_\psi(t)=\int[(x-t)_+ +(t-y)_++(t-z)_+]\,d\mu.
\]
It is at least both \(\alpha-t\) and \(\beta(t-s)\). The maximum of a decreasing affine function and an increasing one is at least their common value at intersection (or use their convex combination cancelling \(t\)). Hence for every cutoff
\[
 \alpha-g_\psi(t)\ \ge\ \frac{\beta}{1+\beta}(\alpha-s).
\]
Provided \(h\ge s\), this yields \(\alpha-G\ge\tfrac12\beta(h-s)\), since \(0\le\beta\le1\).

Now average the *test state*, not the settings, with Haar measure. For every fixed complex qutrit basis, its probability triple is uniform on the two-dimensional probability simplex: normalize three independent standard complex Gaussian coordinates, whose squared moduli are independent unit-mean exponentials. The minimum \(x\) satisfies \(\Pr(x\ge t)=(1-3t)^2\) for \(0\le t\le1/3\), so \(\mathbb E_\psi\alpha=1/9\), independently of \(\mu\). Two prescribed coordinates are both \(\le s\) with probability \(2s^2\) (constant bivariate density 2 on their simplex). For \(3s<1\) the three pair events are disjoint. Thus \(\mathbb E_\psi\beta=6s^2\), again for every \(\mu\), by Fubini. Since \(G\ge h\),
\[
 \frac19-h\ge\mathbb E_\psi(\alpha-G)\ge 3s^2(h-s).
\]
Take \(s=2/27\), so \(3s^2=4/243\) and \(1/9-s=1/27\). Rearranging gives
\[
 h\le\frac19-\frac4{6669}.
\]
If \(h<s\) the same upper bound holds immediately as it exceeds \(s\). Substitution into \(\eta^*=1-3h\) proves the theorem. In particular it rules out convergence along **any** sequence of finite collections; it is stronger than nonattainment at finite \(N\).

The source of the gap is that a single cutoff allocates a fixed number of slots *across* the settings, and small coordinate pairs occur on positive Haar area. The true physical threshold [Wiseman–Jones–Doherty, PRL 98, 140402 (2007)](https://doi.org/10.1103/PhysRevLett.98.140402) is not a claim about the efficiency of this pooled witness and is unaffected. This argument does not compare the best visibility from arbitrary local alignments, all local-hidden-state models, unrestricted POVMs, or unrelated direct-product uncertainty bounds.
