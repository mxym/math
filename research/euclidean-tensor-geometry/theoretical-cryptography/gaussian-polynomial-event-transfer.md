# Which Gaussian changes preserve polynomial-probability events?

The bounded-sample spherical-error argument in the Ring-LWE reductions uses a Gaussian probability-transfer lemma: events with non-negligible mass under a slightly narrower ellipse must still have non-negligible mass under the sphere. We give an exact spectral criterion for this abstract transfer property, a sharp loss exponent in its critical window, and the effect of a single outlying variance direction. In the scalar-padding family the familiar fourth-root width inflation is necessary and sufficient for transfer of *all* measurable events.

The distributions below are unwrapped Gaussian error models, not full Ring-LWE transcripts. Necessity for this comparison method does not assert necessity for a reduction that only sees wrapped errors or uses special events.

## Exact characterization

For $D\to\infty$, let $P_D,Q_D$ be nondegenerate Gaussian distributions on $\mathbb R^D$. Let $\lambda_i>0$ be the eigenvalues of the covariance of $P_D$ after whitening $Q_D$, and let $m_i$ be the coordinates of the whitened mean difference in that eigenbasis. Write

$$
K_D=D_{\rm KL}(P_D\,\|\,Q_D)
=\frac12\sum_i(\lambda_i-1-\log\lambda_i+m_i^2).
$$

Here and below all logarithms are natural. Consider the property: for every $a>0$ there is $b>0$ such that, uniformly for all large $D$, every measurable event $A$ with $P_D(A)\ge D^{-a}$ has $Q_D(A)\ge D^{-b}$. The same property may use randomized tests taking values in $[0,1]$. Its necessary and sufficient conditions are

$$
\max_i\lambda_i=O(1),\qquad K_D=O(\log D).
\tag{1}
$$

Both conditions are needed. A single diverging eigenvalue can invalidate transfer even with $K_D=O(\log D)$; a bounded spectrum by itself does not control accumulation across coordinates. For two-way transfer apply (1) in both directions.

In the whitened coordinates under $P_D$, write observation coordinates as $m_i+\sqrt{\lambda_i}Z_i$ with independent standard real normals. Then the log likelihood ratio $L_D=\log(dP_D/dQ_D)$ has the expression

$$
L_D=K_D+\sum_i\left[\tfrac12 h_i(Z_i^2-1)+b_i Z_i\right],
\qquad h_i=\lambda_i-1,\quad b_i=\sqrt{\lambda_i}m_i .
\tag{2}
$$

For real $t$ with $1-th_i>0$ for all $i$, the centered log moment is

$$
\log\mathbb E_P e^{t(L_D-K_D)}
=\tfrac12\sum_i \left[-th_i-\log(1-th_i)
                         +\frac{t^2 b_i^2}{1-th_i}\right].
\tag{3}
$$

This follows by completing the square in each scalar Gaussian integral. If the eigenvalues are uniformly bounded above, then $\sum h_i^2+\sum b_i^2=O(K_D)$: the continuous ratio $(\lambda-1)^2/(\lambda-1-\log\lambda)$ is bounded on any interval $(0,C]$ after filling in its value at 1, and $b_i^2\le C m_i^2$. Choosing a sufficiently small fixed $t>0$, (3) gives $\log\mathbb E_P e^{t L_D}=O(K_D)$. Thus for every $a$ one can find a constant $c_a$ for which $P(L_D>c_a\log D)\le D^{-a}/2$. Intersect any event of $P$ mass at least $D^{-a}$ with the complementary likelihood region. On that region $dQ/dP\ge D^{-c_a}$, proving the sufficient direction.

For the first necessary condition, if $\lambda_{\max}$ is unbounded along a subsequence, choose its single whitened coordinate and the tail starting at $m_i+\sqrt{\lambda_i a\log D}$ for $m_i\ge0$; use the lower tail starting at $m_i-\sqrt{\lambda_i a\log D}$ for $m_i<0$. Under $P$ it has probability at least $D^{-a}$ for all large $D$ by the ordinary Gaussian tail bound. Under $Q$ it has probability at most $D^{-a\lambda_i/2}$ because the mean shift is in the outward direction. This violates any uniform $b$. If the eigenvalues are bounded but $K_D/\log D$ is unbounded along a subsequence, (2) gives variance $\tfrac12\sum h_i^2+\sum b_i^2=O(K_D)$. Thus $P(L_D\ge K_D/2)\to1$ along a further subsequence, while $Q(L_D\ge K_D/2)\le e^{-K_D/2}$. This proves (1), including the quantifiers in the presence of subsequences.

## Exact exponent in the vanishing-coordinate critical window

Define the worst event-transfer function

$$
\beta_D(u)=
 \inf\{\mathbb E_Q\varphi:\ 0\le\varphi\le1,\ \mathbb E_P\varphi\ge u\}.
$$

Assume $\max_i|\lambda_i-1|\to0$ and $K_D/\log D\to\kappa\in[0,\infty)$. Then for every fixed $a>0$,

$$
\boxed{\ \beta_D(D^{-a})=D^{-(\sqrt a+\sqrt\kappa)^2+o(1)}.\ }
\tag{4}
$$

Thus the log-likelihood budget dictates a specific loss in the polynomial exponent, not just qualitative preservation. In this regime $K_D=\tfrac14\sum_i h_i^2+\tfrac12\sum_i m_i^2+o(\log D)$, so the budget comes from the aggregate covariance mismatch and any whitened mean mismatch.

For the proof, on any fixed bounded $t$ interval the Taylor expansion of (3), with its first two derivatives, gives

$$
(\log D)^{-1}\log\mathbb E_P e^{tL_D}\ \longrightarrow\ \kappa(t+t^2).
\tag{5}
$$

Indeed $\sum|h_i|^3\le \max|h_i|\sum h_i^2=o(\log D)$, and replacing $\sum b_i^2/(1-th_i)$ by $\sum m_i^2$ costs at most $O_t(\max|h_i|\sum m_i^2)=o(\log D)$. These error bounds also hold for the needed derivatives. For $\kappa>0$, Chernoff gives right-tail exponent $(x-\kappa)^2/(4\kappa)$ for $L_D/\log D$ at $x>\kappa$. To see equality, tilt by $e^{tL_D}$ with $t>0$ chosen so that the limiting mean of $L_D/\log D$ is a point just above $x$; the tilted variance is $O(1/\log D)$ by the derivative estimate. Undoing the tilt on a shrinking-to-$x$ family of fixed small intervals gives the matching exponent. Similarly the right tail under $Q$ has exponent $(x-\kappa)^2/(4\kappa)+x$ at $x>\kappa$: on $L_D/\log D\ge x$ use $dQ=e^{-L_D}dP$ for the upper bound, and restrict to a small interval just above $x$ for the lower bound. The interval has the same limiting exponent as the tail as the interval shrinks, by the continuity and strict increase of the right-tail rate.

The extremal test in $\beta_D(u)$ is the top $u$ fraction of $L_D$ under $P$ with boundary randomization if needed. This follows directly since its integrand under $P$ is $e^{-L_D}$, decreasing with $L_D$: subtract the top-fraction test and multiply by the difference of $e^{-L_D}$ from its threshold value. Up to the log scale its threshold for $u=D^{-a}$ is $x_a\log D$ with $x_a=\kappa+2\sqrt{\kappa a}$, by comparing the tail estimates at $x_a\pm\eta$. The $Q$ rate at $x_a$ is $a+x_a$, proving (4). At $\kappa=0$, (5) with any fixed positive $t$ makes $P(L_D>\eta\log D)=o(D^{-a})$ for each $\eta>0$ by taking $t>a/\eta$. It follows that $\beta_D(D^{-a})\ge D^{-a-\eta}(1-o(1))$ for each $\eta$, and the constant randomized test gives $\beta_D(D^{-a})\le D^{-a}$. This includes the case of identical laws.

### One nonvanishing covariance spike

Keep the preceding assumptions on a $(D-1)$-dimensional bulk, but append one independent coordinate with whitened mean difference zero and eigenvalue $1+h$ where $h>0$ is fixed. This direction costs only $O(1)$ in $K_D$, but alters sufficiently far polynomial tails. For $\kappa>0$,

$$
-\frac{\log \beta_D(D^{-a})}{\log D}
\ \longrightarrow\
\begin{cases}
(\sqrt a+\sqrt\kappa)^2,&a\le\kappa/h^2,\\
(1+h)a+\kappa(1+1/h),&a\ge\kappa/h^2 .
\end{cases}
\tag{6}
$$

For $\kappa=0$ the limit is $(1+h)a$. In fact the spike adds $(h Z^2-\log(1+h))/2$ to $L_D$ under $P$. Its right-tail exponent at $z\log D$, $z>0$, is $z/h$. The Chernoff upper bound from (5) now restricts $0\le t<1/h$. For $x>\kappa$ the right-tail rate is therefore

$$
I(x)=\sup_{0\le t<1/h}\{t(x-\kappa)-\kappa t^2\}.
$$

In the interior range $x<\kappa+2\kappa/h$, the exponential tilt again gives equality; the fixed spike does not contribute to the limit of the tilted mean or variance there. In the boundary range let the bulk attain $(\kappa+2\kappa/h)\log D$ within a small interval and supply the remaining excess by the independent spike. The sum of the two exponents is precisely the boundary value of $I(x)$ as the interval shrinks. When $\kappa=0$, the bulk concentrates on the zero log scale and the same argument gives rate $x/h$. Undoing the likelihood transform and inverting $I(x_a)=a$ again gives loss exponent $a+x_a$, which is (6). In particular a log-scale KL limit alone does not determine the exact exponent without a spectral assumption.

## Consequence for spherical padding

For $0<\alpha<\xi$, use a centered spherical target $Q=N(0,\xi^2 I)$ and ellipses $P_\nu$ with covariance $\xi^2 I-\operatorname{diag}(\nu_i)$ where $0\le\nu_i\le\alpha^2<\xi^2$. This is the abstract event-transfer comparison between the desired sphere and the Gaussian padding used before independent elliptical error already present in the input. It is equivalent to comparing relative eigenvalues $1-\nu_i/\xi^2$. Uniformly over all those ellipses, the sharp threshold for transfer of all polynomial-probability events is

$$
D\alpha^4/\xi^4=O(\log D).
\tag{7}
$$

For necessity apply (1) to $\nu_i=\alpha^2$ in all directions. With $h_0=\alpha^2/\xi^2$, $-h_0-\log(1-h_0)\ge h_0^2/2$. For sufficiency, (7) forces $h_0\to0$, and the same scalar log expression is then $O(h_0^2)$ uniformly for $0\le\nu_i/\xi^2\le h_0$. Thus (1) holds with constants uniform over the family. Equivalently the width factor must be at least of order $(D/\log D)^{1/4}$.

The fully saturated ellipse $\nu_i=\alpha^2$ is extremal *even at finite $D$* for $\beta_D$. To see this, scale to $Q=N(0,I)$; for each $i$ apply the same Gaussian channel under both input laws, keeping an input with coefficient $\sqrt{\nu_i/\alpha^2}$ and adding independent standard Gaussian with coefficient $\sqrt{1-\nu_i/\alpha^2}$. It fixes the spherical law and maps $(1-h_0)I$ to the desired ellipse, so every test on the latter pair corresponds to a randomized test on the saturated pair with equal errors. In particular, if $\xi/\alpha\sim B(D/\log D)^{1/4}$ with $0<B<\infty$, the worst-case exponent for an event of $P$ probability $D^{-a}$ is

$$
\left(\sqrt a+\frac{1}{2B^2}\right)^2,
$$

by (4). In the repeated-error Gaussian model $D$ counts real coordinates across the batch, e.g. $D=n\ell$.

## Relation to sources

[Lyubashevsky–Peikert–Regev, Claim 5.15 and Theorem 5.2](https://cims.nyu.edu/~regev/papers/ideal-lwe.pdf) and [Peikert–Regev–Stephens-Davidowitz, §7](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) supply the sufficient coordinatewise bound and the fourth-root scale. Equations (1) and (7) characterize arbitrary-event transfer for the stated Gaussian comparison; (4) and (6) give the sharp polynomial loss and an explicit non-universal crossover. These conclusions do not concern whether a specific Ring-LWE distinguisher attains the worst unwrapped event or whether a different reduction could bypass this comparison.

[Prest](https://tprest.github.io/pdf/pub/renyi.pdf) treats the use of moments of likelihood ratios for event probability preservation in lattice security proofs. [Dong–Roth–Su](https://arxiv.org/abs/1905.02383) give the Gaussian shift trade-off and a hypothesis-testing view of likelihood composition. The exponent here concerns events tending to zero polynomially and a growing-dimensional covariance mismatch; it follows from the exact tilted quadratic Gaussian moments rather than using a fixed-probability normal approximation. This is a scoped source comparison, not an exhaustive priority claim.

The verifier checks the closed rate formulas and the saturation channel using exact finite arithmetic, and illustrates the saturated case with gamma-tail calculations. The asymptotic results follow from the proof above.
