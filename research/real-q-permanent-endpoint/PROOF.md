# Why the endpoint derivative can be negative for a real Gram matrix

For an ordered real matrix $A$ of order $n$, define
$$
P_q(A)=\sum_{\pi\in S_n}q^{\operatorname{inv}(\pi)}\prod_{i=1}^n A_{i,\pi(i)},\qquad
\operatorname{inv}(\pi)=\#\{i<j:\pi(i)>\pi(j)\}.
$$
Write $P'(1)$ for the derivative in $q$ at 1. This part proves existence; [the companion](FINITE.md) specifies one finite rational matrix and comparison point.

## 1. Fischer-norm representation

Given real rows $v_1,\ldots,v_n\in\mathbb R^d$, put $A_{ij}=v_i^Tv_j$, $\ell_i(z)=v_i^Tz$, and define
$$
p(z)=\prod_i\ell_i(z),\qquad
F(z)=\sum_{i<j}(v_i\wedge v_j)\prod_{h\notin\{i,j\}}\ell_h(z).
$$
Give monomials the Fischer inner product $\langle z^\alpha,z^\beta\rangle=\mathbf1_{\alpha=\beta}\,\alpha!$, with $\alpha!=\prod_j\alpha_j!$, and give the increasing coordinate wedges the orthonormal inner product. The identities are
$$
\operatorname{per}A=\|p\|_F^2,\qquad
2P'(1)=\binom n2\operatorname{per}A-\|F\|_F^2. \tag{1}
$$
To see the first, expand the products of two lists of linear forms: assignments with occupancy $\alpha$ are matched by $\alpha!$ permutations. This gives the permanent of their cross Gram matrix. For each $i<j$, subtract twice the inverted-image contribution from the permanent. Group terms by the unordered image pair $k<l$. The difference for that pair is
$$
(A_{ik}A_{jl}-A_{il}A_{jk})\operatorname{per} A_{\widehat{ij},\widehat{kl}},
$$
where the indicated row and column pairs are deleted. The minor is the inner product of the row wedges, and the complementary permanent is the inner product of the complementary polynomials. Summing over $i<j$ and $k<l$ proves the second identity. The pair-minor and rank-two version are already in [Kitamura’s work](https://github.com/KitaKen1/bapat-lal-q-permanent-lean/tree/4200da4fc1a132d69c23fb877795b5b72089544b).

Let $\sigma$ be uniform probability on the unit sphere in $\mathbb C^d$. Monomials of a given degree $m$ are orthogonal there and $\int |z^\alpha|^2\,d\sigma=(d-1)!\alpha!/(m+d-1)!$. This follows, for example, by writing a vector of independent standard complex Gaussians as radius times an independent uniform direction and using the gamma radial moment. For nonzero rows define $d\mu_n=|p|^2d\sigma/\int|p|^2d\sigma$. Since $p,F$ have degrees $n,n-2$ respectively,
$$
\frac{\|F\|_F^2}{\operatorname{per}A}
=\frac{\mathbb E_{\mu_n}\|F(z)/p(z)\|^2}{(n+d-1)(n+d-2)}. \tag{2}
$$
The zero set of $p$ has sphere measure zero. For any unit $z,y\in\mathbb C^d$ off that zero set in $z$, bilinear contraction gives
$$
(z\wedge y)^T\frac{F(z)}{p(z)}
=\sum_{s=1}^n(2s-n-1)\frac{v_s^Ty}{v_s^Tz}. \tag{3}
$$
Each pair contributes its $j$ ratio minus its $i$ ratio. Bilinear Cauchy–Schwarz and $\|z\wedge y\|^2=1-|\langle z,y\rangle|^2\le1$ bound the modulus of the right side above by $\|F(z)/p(z)\|$. The integrating vectors are complex; all Gram entries are still real.

## 2. A row distribution with two maximizing phase circles

Let $T$ have density $1/[\pi(1+|t|^2)^2]$ on the complex plane. Independently pin it to zero with probability $\eta=1/100$ and also replace values with $|T|>R=100$ by zero; call the result $t$. Take an independent uniform phase $s=e^{i\phi}$. The real row and two probe vectors are
$$
v=(\Re s,\Im s,\Re(ts),\Im(ts)),\qquad
z_0=(1,i,0,0)/\sqrt2,\quad y_0=(0,0,1,i)/\sqrt2.
$$
Then $v^Tz_0=s/\sqrt2$, $(v^Ty_0)/(v^Tz_0)=t$, and $\|v\|\le\sqrt{1+R^2}$. Write $\Phi(z)=\mathbb E\log|v^Tz|$ on the complex unit sphere, with $\log0=-\infty$.

For arbitrary complex $a,b$ we have
$$
\mathbb E\log|a+bt|\le\tfrac12\log(|a|^2+|b|^2), \tag{4}
$$
strictly if $b\ne0$. Indeed for $a\ne0$, conditional on the initial radius $r=|T|$, the angular mean equals $\log|a|+\log^+(r|b/a|)$ by the circle mean formula. Here $\log^+(x)=\max(0,\log x)$ with value zero at $x=0$. The tail of $r$ is $1/(1+r^2)$ (at radius $r$). Thus for $x\ge0$ the original radial average is
$$
\mathbb E\log^+(x|T|)=\int_0^x \Pr(|T|>1/u)\,du/u=\tfrac12\log(1+x^2).
$$
Discarding the tail cannot increase the log-plus term; independent pinning multiplies the remaining term by $1-\eta$. This strictly decreases the original positive mean if $b\ne0$. If $a=0$, the positive probability of zero gives the asserted extended-real inequality directly.

For a unit $z$ write $u=(z_1-iz_2,z_3-iz_4)/\sqrt2$ and $w=(z_1+iz_2,z_3+iz_4)/\sqrt2$; $\|u\|^2+\|w\|^2=1$. Averaging in $\phi$ first yields
$$
\Phi(z)=-\tfrac12\log2+\mathbb E_t\log\max(|u_1+tu_2|,|w_1+\bar t w_2|).
$$
Conjugate the second entry in the maximum, which leaves its modulus unchanged. The circle mean formula now represents the log max as the mean over a new uniform phase $e^{i\alpha}$ of $\log|a+tb|$, with $(a,b)=u+e^{i\alpha}\bar w$. By (4) and Jensen,
$$
\Phi(z)\le-\tfrac12\log2+\tfrac12\mathbb E_\alpha\log\|u+e^{i\alpha}\bar w\|^2\le-\tfrac12\log2.
$$
The squared norm has mean one; all logs are bounded above, so the comparisons are valid even at minus infinity. At a finite maximizing point equality requires $b=0$ almost everywhere in $\alpha$, hence $u_2=w_2=0$. Equality in Jensen then requires the remaining squared norm to be constant, equivalently $u_1w_1=0$. The maximizers are therefore exactly the phase circles of $z_0$ and $\bar z_0$, and both attain the stated value row by row. Upper semicontinuity of the log potential on the compact sphere gives a strict uniform gap outside any open neighborhood of their union.

## 3. Why sorting produces enough derivative gain

For a real variable $X$ and an independent copy $\widetilde X$, write $G(X)=\mathbb E|X-\widetilde X|/2$. For continuous $X$, $G(X)=\mathbb E[X(2F_X(X)-1)]$. For $X=\Re T$ the marginal density is $1/[2(1+x^2)^{3/2}]$ and $2F_X(x)-1=x/\sqrt{1+x^2}$. Therefore
$$
G(\Re T)=\tfrac12\int_{\mathbb R}x^2(1+x^2)^{-2}\,dx=\pi/4.
$$
The change in $G$ under a coupling is at most the expected absolute displacement of one variable. The radial mean is $\pi/2$ and $\mathbb E(|T|;|T|>R)\le2/R$. Hence
$$
G(\Re t)\ge\pi/4-2/100-\pi/200>1/\sqrt2. \tag{5}
$$

Choose lists of $n$ rows with empirical $(t,\phi)$-law tending weakly to the compactly supported law, and order each list by nondecreasing $\Re t_s$. For example, choose a realization of an iid sequence with weakly converging empirical laws, then sort each prefix. Sorting does not change the integrals of functions of a single row. At $z_0,y_0$, the real part of (3) divided by $n^2$ is
$$
\frac1{2n^2}\sum_{i,j}|\Re t_i-\Re t_j|\longrightarrow G(\Re t).
$$
This is the exact sorted-pair identity, valid with arbitrary ties; convergence uses bounded continuity on the product support. At $\bar z_0$ use $\bar y_0$ and obtain the same real part. Fix any $1/\sqrt2<g<G(\Re t)$. For all sufficiently large $n$, the modulus of (3) divided by $n^2$ is at least $g$ on an open neighborhood $N$ of these two phase circles: denominators at the centers have modulus $1/\sqrt2$, row norms are uniformly bounded, and multiplication of $z$ by a common phase multiplies all ratios by the same unit scalar, leaving the modulus of the sum unchanged.

The measures $\mu_n$ concentrate on every such $N$. For $z_n\to z$, first clip $\log|v^T z_n|$ from below at $-K$; uniform convergence in the row on compact support and weak empirical convergence bound the limsup of the unclipped mean by the limiting clipped mean. Let $K\to\infty$ to obtain an upper bound $\Phi(z)$. Compactness applied to the complement of $N$ gives a strict uniform deficit below $-\log(2)/2$ for large $n$. In a fixed sufficiently small ball about $z_0$ every individual row log is closer than half that deficit to $-\log(2)/2$. That ball has positive fixed sphere probability. Exponentiation and comparison of its mass with the complement of $N$ give $\mu_n(N)\to1$.

By (2)–(3) and then $g\uparrow G(\Re t)$,
$$
\liminf_{n\to\infty}\frac{\|F\|_F^2}{n^2\operatorname{per}A}\ge G(\Re t)^2>\tfrac12.
$$
Thus (1) gives $P'(1)<0$ for all sufficiently large indices. At any one such order, continuity preserves the strict derivative sign after adding a sufficiently small positive multiple of the identity, giving a real PD necessarily non-diagonal matrix. A negative derivative at the right endpoint implies $P_q(A)>P_1(A)$ for $q<1$ close enough to one. Strictness and positive definiteness allow rational approximations within the real symmetric matrices. This argument does not specify the index. [FINITE.md](FINITE.md) bypasses that limitation.
