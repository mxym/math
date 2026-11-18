# Proof for at most two nonzero magnitudes

Write $K=|\operatorname{supp}S|$ and $\rho=\max_t\Pr(S=t)$, where $S$ is a sum of independently selected weights, each selected with probability $1/2$. Changing the sign of a weight only translates the law, by complementing its fair bit. Zero weights can be deleted. It suffices to consider positive weights.

### Three binomial estimates

For $j\ge1$, set $c_j=2^{-j}\binom{j}{\lfloor j/2\rfloor}$. We use
$$
(j+1)c_j^2\le 3/4,\qquad (j+1/2)c_j^2<2/3,\qquad (j+2)c_j^2\le1.
$$
For $j=2s$, $s\ge1$, the consecutive ratio of $(2s+1)c_{2s}^2$ is $(2s+3)(2s+1)/(2s+2)^2<1$, and the first term is $3/4$. In contrast $(2s+1/2)c_{2s}^2$ increases to $2/\pi<2/3$ by Stirling's formula: the difference between numerator $(4s+5)(2s+1)^2$ and denominator $(4s+1)(2s+2)^2$ of the consecutive ratio is 1. The preceding odd index has the same peak $c_{2s-1}=c_{2s}$ and smaller prefactors. The third bound follows from the second when $j\ge3$, and directly at $j=1,2$. The [review](REVIEW.md) also gives a purely inductive proof of all three estimates.

### Binomial sums on residue classes

Let $R_j(d)$ be the largest probability of any residue class of a $\mathrm{Bin}(j,1/2)$ variable modulo $d\ge1$. Convolution with an extra fair bit averages pairs of entries of the probability vector on $\mathbb Z/d\mathbb Z$, so $R_j(d)$ is nonincreasing in $j$. For $d\ge2$ and $j\ge d$,
$$
R_j(d)\le R_d(d)=c_d.
$$
At $j=d$ only the two endpoints merge, and their combined coefficient $2$ is at most the central binomial coefficient. For $j\ge2d$ we have
$$
R_j(d)\le R_{2d}(d)=c_{2d}+2/4^d,\qquad d R_{2d}(d)^2\le 1/2 .
$$
Indeed the sum of the $2d$ bits has the law of $d+B-B'$ for two independent $\mathrm{Bin}(d,1/2)$ variables, by complementing the second half. The cyclic autocorrelation of the distribution of $B\bmod d$ has its maximum at residue zero by Cauchy–Schwarz. There the original outcomes $0,d,2d$ contribute. At $d=2$ the last inequality is an equality. For $d\ge3$, the second binomial estimate gives $\sqrt d\,c_{2d}<1/\sqrt3<3/5$, and $2\sqrt{d}/4^d\le2\sqrt3/64<1/10$ by monotonicity. Their sum is less than $7/10<1/\sqrt 2$.

### Counting the fibers

For the empty or zero vector $K=\rho=1$. If a single magnitude occurs $j\ge1$ times, $K\rho^2=(j+1)c_j^2\le3/4$. Now let the two magnitudes have multiplicities $n,m\ge1$. When their ratio is irrational every pair of counts gives a distinct sum, so
$$
K\rho^2=(n+1)c_n^2(m+1)c_m^2\le9/16.
$$

For a rational ratio, rescale the magnitudes to coprime integers $a<b$ and write $S=aX+bY$, with independent $X\sim\mathrm{Bin}(n,1/2)$, $Y\sim\mathrm{Bin}(m,1/2)$. The integer displacements preserving the sum are the multiples of $(b,-a)$. Thus the representation on the count rectangle is injective if $n<b$ or $m<a$, and the preceding product bound applies.

Suppose $n\ge b$ and $m\ge a$. The points in a fiber form a consecutive string with step $(b,-a)$; count just its first point, one with no predecessor $(i-b,j+a)$ in the rectangle. This gives exactly
$$
K=(n+1)(m+1)-(n-b+1)(m-a+1)=a(n+1)+b(m+1)-ab.
$$
A fixed sum restricts $Y$ to one class modulo $a$ with at most one value of $X$ per $Y$. Exchanging their roles restricts $X$ modulo $b$. Therefore
$$
\rho\le c_n R_m(a),\qquad \rho\le c_m R_n(b).
$$

If $a\ge2$, these estimates give $a(n+1)\rho^2\le(n+1)c_n^2\, a c_a^2<(3/4)(2/3)=1/2$, and likewise $b(m+1)\rho^2<1/2$. Adding these two bounds proves $K\rho^2<1$.

If $a=1$, then $K=n+bm+1$. For $n\ge2b$, use $R_m(1)=1$ and the stronger residue bound to get
$$
(n+1/2)\rho^2<2/3,\qquad
(bm+1/2)\rho^2\le (m+1/2)c_m^2\, b R_n(b)^2<1/3.
$$
Adding proves the claim. For the remaining interval $b\le n<2b$, the integer bound $n+1\le2b$ yields $K\le b(m+2)$. Consequently
$$
K\rho^2\le(m+2)c_m^2\, b c_b^2<2/3 .
$$
This exhausts all nonzero vectors with at most two magnitudes. No optimal nontrivial numerical upper bound for $K\rho^2$ is asserted.
