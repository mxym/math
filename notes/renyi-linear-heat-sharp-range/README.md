# When is Rényi entropy concave under Gaussian smoothing in every dimension?

**Research draft; independently reviewed by an AI reviewer, not externally peer reviewed. Priority is not established.**

Let $u_t=e^{t\Delta}f$ on $\mathbb R^d$, where $f$ is a probability density (the noise has covariance $2tI$). For finite $\alpha>0$ put

$$
h_\alpha(t)=\frac{1}{1-\alpha}\log\!\left(\int_{\mathbb R^d} u_t(x)^\alpha\,dx\right),\qquad
N_{\alpha,\beta}(t)=\exp\!\left(\frac{\beta}{d} h_\alpha(t)\right),\quad\beta>0.
$$

Use the differential Shannon entropy when $\alpha=1$. We ask for concavity in **positive time**, wherever the entropy is finite, **simultaneously for every dimension and every initial density**.

| Quantity | Exactly when concavity holds in all dimensions |
|---|---|
| $h_\alpha$ | $1\le\alpha\le 2$ |
| $N_{\alpha,\beta}$ | $1\le\alpha<2$, $0<\beta\le 2(2-\alpha)$ |

The positive results are due to [Wu and Yu, Theorems 5 and 8](https://arxiv.org/html/2611.13040v1); the Shannon endpoint is Costa's theorem. **This note supplies the matching necessity:** at each excluded order or pair of parameters, some finite dimension admits smooth strictly positive radial initial data with a strictly positive second derivative on an interval of positive times. The dimension and data may depend on the parameters. For example, $h_2$ is concave, but no strictly positive power exponent works universally at order two.

[Wu and Yu's Remark 1](https://arxiv.org/html/2611.13040v1#S6.SS3) explicitly asks whether the **order interval** for plain entropy can be enlarged. This answers its dimension-uniform Euclidean, general-initial-data part (Theorem 5), not the separate fundamental-solution problem (Theorem 3). The sharp power-exponent statement concerns Theorem 8; Remark 1 did not pose it explicitly. No fixed-dimensional classification, nonlinear diffusion theorem or complete-monotonicity result is claimed.

## Why the upper bounds match

Write $w=u_t^{\alpha/2}$, and take expectations with respect to $w^2/\int w^2$. Set $A=\Delta w/w$, $B=|\nabla\log w|^2$ and $\delta=2/\alpha-1$. The heat equation and integration by parts give $h'_\alpha=(4/\alpha)\mathbb E B$ and the curvature ratio

$$
T=-\frac{d h''_\alpha}{(h'_\alpha)^2}
=\frac{\alpha d}{2}\,
\frac{\mathrm{Var}(A)+\delta\,\mathrm{Cov}(A,B)}{(\mathbb E B)^2}.
$$

Strict failures of ordinary and power concavity correspond to $T<0$ and $T<\beta$, respectively. Take an auxiliary shell $w(r)=r^m e^{-r^2/2}$, with $m+d/2=\lambda d/2$ for a fixed $\lambda>0$. Under its squared weight, $r^2$ has the gamma law with shape $\lambda d/2$ and unit scale. Both $A$ and $B$ are linear combinations of $r^2,1,r^{-2}$, so rational moment identities give

$$
\lim_{d\to\infty}T=2(2-\alpha)+\frac{2(\alpha-1)}{\lambda}.
$$

For $\alpha<1$, a sufficiently small $\lambda$ makes this limit negative. For $\alpha>2$, a sufficiently large $\lambda$ does so. For $1<\alpha\le 2$, a sufficiently large $\lambda$ puts it strictly below any proposed $\beta>2(2-\alpha)$. Choose $\lambda$ **first**, then choose a finite $d$ giving strict separation. For $\alpha=1$ a Gaussian has $T=2$.

The shell is only an auxiliary calculation: its $2/\alpha$ power need not even be integrable at the origin. [The complete proof, §5](reviewed/PROOF.md#5-making-the-test-into-an-actual-smooth-heat-trajectory) regularizes both the origin and tail at fixed $d$, proves convergence of all normalized moments, then fixes the regularization and proves that the strict sign persists under heat flow for positive times. The argument does not normalize a singular non-probability density. For a sample exact check, $\alpha=3,d=300,\lambda=5$ gives $T=-687070/1459161$ for the auxiliary shell.

## What was already known

- [Wu and Yu, Theorem 6 and Remark 2](https://arxiv.org/html/2504.01837v2#S2.SS4) already excluded universal power concavity for $\alpha\ne1$ and $\beta\ge2$ in our normalization. The nontrivial upper boundary below 2 here is $2(2-\alpha)$ for $1<\alpha\le2$.
- In [Sun, Theorem 2 and Remark 19](https://arxiv.org/html/2601.12944v3#S4), strict failures for Tsallis entropy at $\alpha>3$ already imply failures for ordinary Rényi entropy there: if $U=\int u^\alpha$ and $S=(1-U)/(\alpha-1)$, then $h''=S''/U+(\alpha-1)(S')^2/U^2$. The Tsallis Gaussian obstruction for $\alpha<1$ does not transfer by that implication. Sun also uses the power substitution behind the heat identities.
- [Wu, Yu and Guo](https://doi.org/10.1109/TIT.2025.3561384) prove a wider positive order interval in dimension one, including $0<\alpha\le3$ for plain entropy. The necessity results here concern an inequality meant to hold *in every dimension*, not its validity in dimension one.
- [Savaré and Toscani](https://arxiv.org/abs/1208.1035) and [Bukal](https://arxiv.org/abs/2202.12527) study related generalized powers along different, nonlinear evolutions. No matching full classification for the linear flow was found in the targeted prior-work search; this is not an exhaustive priority determination.

## Proof and verification

- [Complete, originally reviewed manuscript](reviewed/PROOF.md). The historical status line records the manuscript's status **before** the independent review. It is preserved byte-for-byte so its hash matches the [independent AI review](REVIEW.md).
- [Author-side exact checks](check.py): the escort calculation and direct radial Laplacian calculation agree on 550 finite parameter choices, with five exact boundary examples and an invalid-domain control. Python 3 standard library.
- [Independent symbolic check](independent.py): a separate local-score derivation also checks the large-dimension limit and the Shannon endpoint, using SymPy. These programs check algebraic moments, not the smooth approximation or the complete theorem. The latter requires the written argument.

From this directory:

```sh
python -B -O check.py
python -B -O independent.py
```
