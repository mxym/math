# A nested deterministic obstruction to the original-law three-endpoint gate

This construction addresses the precise positive-mask gate in version 2, not the pinned distance-set conjecture. It is a fully nested digit construction, so it does not infer infinite-scale divergence merely by intersecting unrelated finite-scale examples. Its finite-scale geometry is the classical train-track geometry of Guth--Iosevich--Ou--Wang (GIOW), Section 6. The conclusion below is narrower than a counterexample to existence of a good pinned distance law after a different preparation.

## 1. Construction and exact Frostman control

Fix a rational number $1<\alpha<4/3$ and put $\epsilon=2-3\alpha/2>0$. Choose positive integer stage lengths $L_j$, all multiples of twice the denominator of $\alpha$, and write $n_0=0$, $n_j=\sum_{i\le j}L_i$. Choose the lengths so rapidly increasing that
\[
 \epsilon L_j-\alpha n_{j-1}\longrightarrow+\infty. \tag{T1}
\]
For example, require the left side to be at least $j$; extra growth is harmless. We additionally require $L_j/n_{j-1}\to\infty$, with the convention that the first ratio is unrestricted. This is compatible with (T1) and gives the packing-dimension calculation below. Take $L_1$ large enough for the finitely many initial binary positions used below to be free in both coordinates.

In stage $j$, index binary positions relative to its start by $1,\ldots,L_j$. In the first coordinate $X$, make precisely the following positions free:
\[
 [1,(\alpha-1)L_j/2]\ \cup\ (L_j/2,L_j]. \tag{T2}
\]
All other positions are frozen at zero. In the second coordinate $Y$, the free positions are
\[
 [1,\alpha L_j/2], \tag{T3}
\]
with the rest frozen at zero. At free positions choose independent fair binary digits. This defines compact digit sets $X,Y\subset[0,1]$ and nonatomic probabilities $\kappa_X,\kappa_Y$. Both coordinates have infinitely many free and frozen positions; their probabilities have no atoms, including at dyadic boundaries. Let $F_X(n),F_Y(n)$ be the numbers of free positions through depth $n$.

For a relative depth $0\le l\le L=L_j$, the total new free-position count, up to a rounding error of at most two, is the continuous function
\[
 F(l)=
 \begin{cases}
 2l,&0\le l\le(\alpha-1)L/2,\\
 l+(\alpha-1)L/2,&(\alpha-1)L/2\le l\le L/2,\\
 2l-(2-\alpha)L/2,&L/2\le l\le\alpha L/2,\\
 l+(\alpha-1)L,&\alpha L/2\le l\le L.
 \end{cases} \tag{T4}
\]
Each formula gives $F(l)\ge\alpha l$, and $F(L)=\alpha L$ exactly. Thus
\[
 F_X(n)+F_Y(n)\ge\alpha n-2,
 \qquad F_X(n_j)+F_Y(n_j)=\alpha n_j. \tag{T5}
\]
There is no accumulation of stage errors: the counts agree exactly at every endpoint, and the error at an interior depth belongs only to its current stage.

Every occupied dyadic square of side $2^{-n}$ has $(\kappa_X\otimes\kappa_Y)$-mass exactly $2^{-F_X(n)-F_Y(n)}$. A ball of radius between $2^{-n-1}$ and $2^{-n}$ meets a bounded number of such squares. Consequently
\[
 (\kappa_X\otimes\kappa_Y)(B(z,r))\le C_\alpha r^\alpha. \tag{T6}
\]
The support has Hausdorff dimension exactly $\alpha$: the Frostman bound gives the lower bound; at depths $n_j$ it has exactly $2^{\alpha n_j}$ occupied squares, yielding the upper bound by the Hausdorff covering criterion for every exponent greater than $\alpha$.

Every nonempty fixed digit cylinder has upper box dimension two if $L_j/n_{j-1}\to\infty$: in the first $(\alpha-1)L_j/2$ positions of a sufficiently late stage, both coordinates are free, and the earlier count divided by this new depth tends to zero. This remains true inside any nonempty relatively open support subset, since it contains a cylinder. The countable-cover characterization of packing dimension and the Baire theorem then give packing dimension two. More explicitly, in a countable cover take relative closures; these preserve upper box dimension, and one closure contains a relatively open support subset. Thus $\dim_P(X\times Y)=2$, and the same argument holds after the fixed cylinder restrictions used next.

Fix a small dyadic $\eta=2^{-k}<1/8$, with the first $k$ positions free in both coordinates. Condition $\kappa_X$ on its leftmost depth-$k$ cylinder $[0,\eta]$. Denote the resulting probability by $\kappa$. Condition $\kappa_Y$ on $[0,\eta]$ for a pin-coordinate probability $\zeta_-$ and on $[1-\eta,1]$ for a source-coordinate probability $\zeta_+$. Define
\[
 E_1=\operatorname{supp}\kappa\times\operatorname{supp}\zeta_-,\quad
 \lambda=\kappa\otimes\zeta_-,
\]
\[
 E_2=\operatorname{supp}\kappa\times\operatorname{supp}\zeta_+,\quad
 \mu=\kappa\otimes\zeta_+. \tag{T7}
\]
The supports here are the fixed-prefix coding cylinders, rather than an unqualified closed-interval intersection that could add a zero-mass adjacent boundary point. These are fixed compact separated sets, with diameters $O(\eta)$ and cross directions in a vertical cone of aperture $O(\eta)$. Each law is $\alpha$-Frostman, with a fixed constant depending on $\eta$. Their occupied depth-$n$ cells, for $n\ge k$, have identical masses $2^{-F_X(n)-F_Y(n)+2k}$. Thus the actual numerical dyadic regularity/profile conditions hold with exact counts; the normalized count profile is nondecreasing, 2-Lipschitz and bounded below by $\alpha n/N-O(k/N)$. A class decomposition that only records uniform child counts and leaf masses introduces no further geometry.

## 2. Every original pin has divergent low-pass energy

Fix $p=(p_1,p_2)\in E_1$. Let $j$ be a sufficiently large stage, and write $n=n_{j-1}$, $L=L_j$, $N=n+L$, $\delta=2^{-N}$. At depth $\tau=n+L/2$, the first-coordinate cylinder $I$ containing $p_1$ has length
\[
 w=2^{-n-L/2}
\]
and $\kappa$-mass
\[
 m_j=2^{k-F_X(n)-(\alpha-1)L/2}. \tag{T8}
\]
At a possible support boundary, choose a digit representation of $p_1$ and its corresponding closed cylinder; the mass formula and distance upper bound remain valid. The source restriction to $I\times[1-\eta,1]$ has mass $m_j$.

The source second-coordinate support is covered by at most
\[
 M_j=2^{F_Y(n)+\alpha L/2-k} \tag{T9}
\]
occupied depth-$N$ intervals, each of length $\delta$. For $y$ in the indicated source track, $0\le |y_1-p_1|\le w$ and $y_2-p_2\ge1-2\eta$. Hence
\[
 0\le |y-p|-(y_2-p_2)
 =\frac{(y_1-p_1)^2}{|y-p|+y_2-p_2}
 \le C_\eta w^2\le C_\eta\delta, \tag{T10}
\]
since $w^2=\delta 2^{-n}$. Its distance image therefore lies in at most $M_j$ intervals of length $C_\eta\delta$. These intervals can be covered by at most $C_\eta M_j$ disjoint bins of width $\delta/4$. If $a_i$ are the masses in those bins, $\sum a_i=m_j$, so Cauchy--Schwarz gives
\[
 (\mu\otimes\mu)\{(y,y'):\big||p-y|-|p-y'|\big|\le\delta/4\}
 \ge c_\eta\frac{m_j^2}{M_j}. \tag{T11}
\]
All additional source pairs have nonnegative contribution.

For any finite positive measure $\nu$ on the real line, the Fejer identity is
\[
 \int_{-R}^{R}(1-|\xi|/R)|\widehat\nu(\xi)|^2d\xi
 =\iint R\,\operatorname{sinc}^2(\pi R(s-t))d\nu(s)d\nu(t), \tag{T12}
\]
where $\operatorname{sinc}(z)=\sin(z)/z$. The right kernel is nonnegative everywhere and is at least $cR$ for $|s-t|\le1/(4R)$. Applying this with $R_j=2^N$ and $\nu=(d_p)_*\mu$ yields
\[
 \int_{-R_j}^{R_j}|\widehat{(d_p)_*\mu}(\xi)|^2d\xi
 \ge c_\eta R_jm_j^2/M_j
 \ge c_\eta 2^{\epsilon L_j-\alpha n_{j-1}}. \tag{T13}
\]
Indeed the exact logarithm, apart from the fixed $3k$ contribution, is
\[
 \epsilon L_j+n_{j-1}-2F_X(n_{j-1})-F_Y(n_{j-1}),
\]
and the last three terms are at least $-\alpha n_{j-1}$ by (T5) and $F_X(n)\le n$. The lower bound diverges by (T1), uniformly for every pin in $E_1$.

**Theorem T.** The fixed probabilities (T7) have the exact Frostman and dyadic profile properties above, yet $(d_p)_*\mu$ has no $L^2$ density for any $p\in E_1$. For every probability pin law supported on any nonempty subset of $E_1$, the original-law averaged low-pass energy is unbounded along $R_j$. This does not say that the distance laws are singular or that their supports have zero Lebesgue measure.

## 3. These inputs also admit the source's critical angular cap preparation

We use the standard separated-measure radial-projection theorem quoted as GIOW Theorem 3.7: for separated compact planar $\alpha$-Frostman probabilities, $\alpha>1$, there is $p>1$ such that
\[
 \int\|g_x\|_{L^p(S^1)}^p\,d\lambda(x)<\infty,
 \quad g_x\,d\sigma=(\pi_x)_*\mu. \tag{T14}
\]
The reversed assertion holds as well, with a possibly different exponent; decrease to a common exponent greater than one. This is precisely the radial-$L^p$ input used by the specified source's planar preparation. It applies to (T7) after a fixed similarity into the unit disk; bounded support and separation are fixed, and this fixed similarity changes only constants in the preceding estimates. Choose jointly measurable versions of the densities, as supplied by disintegration of the joint radial-projection measures. Remove all pairs whose pin belongs to either exceptional null set where the corresponding density identity or finite norm is unavailable. These full-fiber deletions have product mass zero and allow the following cap assertion to hold for every retained pin, rather than only almost every pin.

For $R=2^N$ and a fixed $e>0$, delete the pair set
\[
 B_N=\{(x,y):g_x(\pi_x y)>R^{e/2}\}
       \cup\{(x,y):g'_y(\pi_y x)>R^{e/2}\}. \tag{T15}
\]
The product mass of $B_N$ is at most
\[
 C R^{-e(p-1)/2}, \tag{T16}
\]
by integrating $g\mathbf1_{g>D}\le D^{-(p-1)}g^p$ on both sides. On $G_N=(E_1\times E_2)\setminus B_N$, every angular cap of radius $u$ has unnormalized opposite-fiber mass at most $C R^{e/2}u\le R^eu$ for sufficiently large $N$. This holds on both sides and at all cap radii. Taking $\Gamma_N=E_1\times E_2$ supplies exactly the planar starting-pair conclusion: a decreasing full product, positive limiting mass, one product atom, and power-small exceptional pair sets giving the critical cap exponent $S=1$.

Thus Frostman, numerical profiles, separated small cross-direction patch and the stated critical angular-cap preparation do not imply an original-law $L^2$ gate. The example is an admissible prepared input under these numerical conclusions. It does not assert that the particular proof procedure must choose it: different positive spatial restrictions can separate the two horizontal marginals and destroy the shared-track mechanism.

## 4. Obstruction for every approximation returning to this original law

Let $P\subset E_1$ have positive original pin mass and let $\lambda_P$ be any probability supported on $P$. Let $k_N(x,y)\in[0,1]$ be arbitrary jointly measurable positive masks, including inherited masks depending on the same pin, and suppose their normalized retained source laws $\mu_N^x$ converge to $\mu$ in integrated total variation:
\[
 \int\|\mu_N^x-\mu\|_{\rm TV}\,d\lambda_P(x)\longrightarrow0. \tag{T17}
\]
Positive masks whose integrated deficit tends to zero have this property. Summable TV convergence from the version-2 pruning/selection theorem certainly has it. Let the source additionally undergo arbitrary, even pin-dependent and correlated, displacements of magnitude $A/R_N$, with $R_N\to\infty$ and fixed $A$. At every fixed Fourier cutoff $U$, their distance-law Fourier transforms converge in integrated uniform norm on $[-U,U]$, since distance is 1-Lipschitz and
\[
 |e^{-2\pi i\xi d_p(y+z)}-e^{-2\pi i\xi d_p(y)}|
 \le2\pi U A/R_N. \tag{T18}
\]
If their averaged low-pass energies at $R_N$ were bounded by a fixed constant, the averaged original energy at every fixed $U$ would have the same bound, by (T17)--(T18). Taking $U=R_j$ contradicts (T13).

Likewise a uniform positive three-endpoint collision gate would imply these uniformly bounded low-pass energies. One convenient positive comparison is: the triangular spatial kernel $R(1-R|s|)_+$ has nonnegative Fourier transform $\operatorname{sinc}^2(\pi\xi/R)$, bounded below on $|\xi|\le R/2$, so
\[
 \int_{-R/2}^{R/2}|\widehat\nu(\xi)|^2d\xi
 \le C R\iint\mathbf1_{|s-t|\le1/R}d\nu(s)d\nu(t). \tag{T19}
\]
Changing the cutoff by this fixed factor has no effect on the contradiction. For unnormalized masks of fiber mass at least $c_0>0$, normalization costs at most $c_0^{-2}$.

The obstruction is therefore universal over **all** filter sequences that return to this fixed original prepared law, on **every** positive pin set. It is not merely a bad choice of one finite-scale filter. At a single stage, deletion of each pin's own source track costs only $m_j$, a power-small quantity; the impossibility comes from uniform control of all earlier bands while converging back to the original infinite law.

## 5. Precise scope

A fixed distance weight $W(s)$ bounded above and below by positive constants on these separated supports does not remove the obstruction: the weighted positive distance law dominates a fixed multiple of the original law, and the collision and Fejer lower bounds remain valid. Thus the source's usual smooth stationary-phase distance weight cannot supply the missing cancellation.

The conclusion rules out a universal proof of the version-2 original-law gate from the actual Frostman/profile/angular-cap conclusions alone. A successful unrestricted common-pin argument may use a different positive prepared source law, a nonvanishing pin-dependent deletion, or a signed/smoothed good source as in current pinned-distance papers. The construction neither rules out those mechanisms nor claims a counterexample to common-pin positive distance measure. It also does not claim that every canonical mask retains every bad pair.

The classical train-track obstruction and the usefulness of nonpositive good-source decompositions are discussed in GIOW, Sections 1.2 and 6. Liu (2026) and Gan--Liu--Wu (2026) control their own good-source wave-packet laws, not arbitrary positive approximations returning in TV to a given original law. The nested allocation above makes explicit the stronger quantifier relevant to the current gate; no new unrestricted pinned-distance threshold is claimed. For the concrete choice $\alpha=13/10$, the current Gan--Liu--Wu two-set theorem already guarantees a positive-measure pinned cross-distance set for at least one pin. Our original-law $L^2$ obstruction is compatible with that conclusion: positive distance measure does not require the original natural distance probability to have an $L^2$ density. The pin support has Hausdorff dimension $\alpha$ and packing dimension two, so Liu's equal-Hausdorff/packing pin hypothesis is not available here.
