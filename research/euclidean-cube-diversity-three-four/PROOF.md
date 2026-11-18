# Exact vertex thresholds in dimensions three and four

Scale the cube to $C=[0,1]^d$ and use $K_s(x,y)=e^{-s\lVert x-y\rVert_2}$, $s>0$. Write $\mu$ for the uniform probability measure on its $2^d$ vertices. For $D=3,4$ define $s_D$ by

$$
\sum_{k=0}^{D-1}\binom{D-1}{k}
  \frac{e^{-s_D\sqrt{k+1}}}{\sqrt{k+1}}=1. \tag{1}
$$

The left side strictly decreases from a number greater than one to zero, so there is exactly one positive root.

**Theorem.** For $D\in\{3,4\}$ and all $d\ge D$, if $0<s\le s_D$ then $\mu$ is the unique simultaneous maximum-diversity probability measure on $C$. If $d=D$ and $s>s_D$, no probability supported on the vertices maximizes diversity simultaneously. Thus $s_D$ is sharp in the base dimension and is the best side bound valid at once for all $d\ge D$.

## 1. Test for the candidate

Let $E(\nu)=\iint K_s(x,y)\,d\nu(x)d\nu(y)$ and $U(x)=\int K_s(x,y)\,d\mu(y)$. The Fourier transform of $e^{-s\lVert x\rVert_2}$ is a positive constant times $s(s^2+\lVert\xi\rVert_2^2)^{-(d+1)/2}$. This is integrable and strictly positive, so $E(\eta)>0$ for every nonzero finite signed measure $\eta$ (Fourier inversion, continuity and uniqueness of its Fourier transform). The maximum exists by compactness and continuity. Order-two diversity is reciprocal energy and, by [Leinster–Roff, Cor. 7.3](https://doi.org/10.1093/qmath/haab003), its maximizers maximize all orders simultaneously.

On the vertices $U$ has the constant value $E(\mu)$ by symmetry. For any probability $\nu$,

$$
E(\nu)-E(\mu)=E(\nu-\mu)+2\int [U(x)-E(\mu)]\,d\nu(x).
$$

Consequently $\mu$ is the unique minimizer if $U\ge E(\mu)$ everywhere; if this inequality fails at $x$, mixing $\mu$ with a sufficiently small positive mass at $x$ strictly decreases the energy. These are the classical equilibrium conditions; see [Dajani, §2, (4)–(5)](https://arxiv.org/pdf/2610.38031). In particular $\mu$ is always the unique minimizer *among vertex-supported probabilities*.

## 2. The minimum lies on an edge in the required range

Fix the relative interior of an $m$-face, $m\ge2$. At a point $x$ of the face, group corner vectors $v$ by the number $k$ of mismatches with its fixed coordinates. In each group the $m$ free bits are uniformly distributed. Let $L$ be the length of the component of $x-v$ in the free directions, $r=\sqrt{k+L^2}$, $W=e^{-sr}/r$. The face's relative interior contains no corner, so $r>0$. The trace of the radial Hessian over the free coordinates of $e^{-sr}$ is

$$
sW g(L),\qquad g(L)=sL^2/r+L^2/r^2-m.
$$

As $L$ increases, $W$ decreases and $g$ is nondecreasing. Thus $\operatorname{Cov}(W,g)\le0$: with an independent copy the covariance is half the expectation of the product of their two differences. Since $L^2/r\le L$ and $L^2/r^2\le1$,

$$
\mathbb E[Wg]\le \mathbb E[W](s\mathbb E[L]+1-m).
$$

For $m=2$, the function taking a point of the square to its mean distance from the four vertices is convex. At any point it is bounded by its maximum corner value $(2+\sqrt2)/4$. For $m\ge3$, each squared coordinate gap has mean $x_j^2-x_j+1/2\le1/2$, hence $\mathbb E[L]\le\sqrt{m/2}$. Since $(m-1)\sqrt{2/m}$ increases for $m\ge3$ and already exceeds $4/(2+\sqrt2)$ at $m=3$, the mean trace in **each** group is strictly negative whenever $s<4/(2+\sqrt2)$. The enclosures below put both $s_D$ below this bound.

At a relative-interior local minimum the trace on the face could not be negative. Every point belongs to one relative interior, so a global minimum is on an edge or a vertex.

## 3. Reduction along an edge in the base dimension

Let $t$ be the coordinate on the edge with all other coordinates zero. For $u\in[0,1]$, write $r_k(u)=\sqrt{k+u^2}$, $h_0(u)=e^{-su}$ and $h_k(u)=u e^{-sr_k(u)}/r_k(u)$ for $k\ge1$. Put

$$
H_{s,D}(u)=\sum_{k=0}^{D-1}\binom{D-1}{k}h_k(u),\qquad
F_{s,D}(t)=H_{s,D}(1-t)-H_{s,D}(t).
$$

Grouping pairs of vertices by Hamming weight in the other coordinates shows that the derivative of $2^DU$ along the edge is $sF_{s,D}(t)$; at $t=0$ this means the right derivative. $F_{s,D}(1/2)=0$ and $F_{s,D}(0)$ is the left side of (1), with $s$ replacing $s_D$, minus one.

To reduce to $s_D$, fix $0<t<1/2$. For $u>0$ one can write $H_{s,D}(u)=u\sum_k w_k(u)$, where $w_k(u)=\binom{D-1}{k}e^{-sr_k(u)}/r_k(u)$, including $k=0$ with $r_0(u)=u$. Normalize $w$ to a probability $p$. Then $\partial_s\log H_{s,D}(u)=-\mathbb E_{p(u)}[r_k(u)]$. This last expectation before the minus sign increases strictly with $u$. Indeed, when $j>i$ the ratio $w_j/w_i$ increases with $u$: both $r_i/r_j$ and $e^{-s(r_j-r_i)}$ increase, since $r_j-r_i=(j-i)/(r_j+r_i)$. For $v>u$ the ratio $p_k(v)/p_k(u)$ is therefore increasing in $k$. Its covariance under $p(u)$ with the increasing sequence $r_k(u)$ is nonnegative, giving $\mathbb E_{p(v)}[r_k(u)]\ge\mathbb E_{p(u)}[r_k(u)]$. Replacing $r_k(u)$ by $r_k(v)>r_k(u)$ makes this strict.

Hence $H_{s,D}(1-t)/H_{s,D}(t)$ strictly decreases with $s$. If $F_{s_D,D}(t)>0$ for $0<t<1/2$, the same holds for every $0<s<s_D$. This uses monotonicity of the **ratio**, not of the difference.

## 4. Exact interval lemma

The [first certificate](verify.py) brackets the roots by $0.83811<s_3<0.83812$ and $1.16444<s_4<1.16445$ using opposite strict signs of $F_{s,D}(0)$ at each pair of endpoints. It checks the following lower bounds, in integer units of $10^{-16}$, over each **whole closed parameter bracket**:

| $D$ | $F'$, $0\le t\le1/16$ | $F$, $1/16\le t\le3/8$ | $-F'$, $3/8\le t\le1/2$ |
|---|---:|---:|---:|
| 3 | 719021344444582 | 45475748617419 | 378295966583773 |
| 4 | 1264360770007316 | 85824553333822 | 683185510591429 |

Here primes differentiate in $t$. To reproduce the lemma, partition the half-edge into the 2048 closed cells $[i/4096,(i+1)/4096]$. Evaluate the indicated expression over each entire cell, using $F'=-H'(1-t)-H'(t)$ and $h'_k=e^{-sr_k}(k/r_k^3-su^2/r_k^2)$ for $k\ge1$. Interval arithmetic stores numerator endpoints on a fixed $10^{-16}$ lattice; every arithmetic operation rounds outwards. For a square root take floor/ceiling integer square roots at its endpoints. For $0\le z\le4$, use the alternating exponential partial sums of orders 25 and 26 for the lower and upper bounds on $e^{-z}$, respectively; the omitted terms decrease. Monotonicity of $e^{-z}$ permits evaluation at the interval endpoints in reverse order. The two endpoint identities $F_{s_D,D}(0)=F_{s_D,D}(1/2)=0$ now give strict positivity throughout the open half-edge, including the transition scale. A [second certificate](independent.py) proves the same sign from concavity and monotonicity on different intervals; see [REVIEW.md](REVIEW.md).

## 5. Transfer to every $d\ge D$ and sharpness

Increasing the dimension from $D$ to $d$ only adds nonnegative integer multiples of paired differences $h_k(1-t)-h_k(t)$ with $k\ge1$; the coefficient at $k=0$ remains one. For $a=t\in(0,1/2)$, $b=1-a$,

$$
\log\frac{b/r_k(b)}{a/r_k(a)}
=\int_a^b\frac{k}{u(k+u^2)}\,du
\ge \frac{2k}{k+1}(b-a).
$$

Indeed $k+u^2\le k+1$ and the average of $1/u$ is at least the reciprocal of its average argument $(a+b)/2=1/2$. Also $r_k(b)-r_k(a)=(b-a)/(r_k(b)+r_k(a))\le(b-a)/(2\sqrt k)$. Hence $h_k(b)>h_k(a)$ if $s<4k\sqrt k/(k+1)$, a bound at least 2 for $k\ge1$. At $a=0$ the positive-$k$ pairs help directly. Since $s_4<2$, this proves positivity of the half-edge derivative in all dimensions asserted. It does not require that every $h_k$ increase pointwise on the entire unit interval.

Symmetry now puts the minimum of each edge at its endpoints. Combined with §2 this proves the equilibrium inequality needed in §1. Conversely, in the base dimension $D$, (1) shows that for any $s>s_D$ the right derivative at a corner is negative, so arbitrarily close edge points violate this inequality. The only possible vertex-supported optimizer was $\mu$; it is now excluded. This proves the theorem.
