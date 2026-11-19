# Fractional supply and the rare-stockout frontier for independent bounded demands

Yongxian Zhang (张永贤). AI-assisted research draft, November 19, 2026. Internally reviewed, not externally peer reviewed. See [prior-work boundaries](SOURCES.md).

For a finite family of independent (possibly nonidentically distributed) demands $X_i\in[0,1]$, let $S=\sum X_i$ and fix a **real** supply $K>0$. Stockout is $s=\Pr(S\ge K)$, availability is $1-s$, absolute throughput is $T=\mathbb E\min(S,K)$, and relative throughput is $T/K$. Set
$$
 F_K(s)=\inf\{\mathbb E\min(S,K): \Pr(S\ge K)=s\},
$$
over all finite such families, with no bound on their size. Stockout at least $s$ gives the same infimum: independently thin each original variable to zero with common retention probability $u$, chosen by continuity to give the exact desired stockout; this does not increase throughput.

**The question.** [Ganesh, Hartline, Sinha and vonAllmen (EC 2024)](https://arxiv.org/html/2402.19292v3), unnumbered Conjecture in the introduction, ask whether each feasible pair admits an ordinary Poisson total demand at the **same supply** with both availability and relative throughput no greater. The paper's general soup model (§2.1) allows real supply, unlike its integer examples. This is a question about the benchmark, not about the validity of their proved concentration bounds or the performance of a static pricing policy. A Poisson benchmark here has jumps of one; allowing arbitrary compound Poisson marks would change the question.

**Theorem A.** For every fixed noninteger $K>1$ and every $s\in(0,1)$, some finite iid demands in $[0,1]$ have stockout exactly $s$ and strictly smaller throughput than every ordinary Poisson demand with stockout at least $s$. A fully rational example needs three diners when $K=3/2$. This theorem does not refute the all-availability assertion for any positive integer supply.

**Theorem B (sharp sparse frontier).** For every fixed $1<K\le2$, set $c=K-1$ and
$$
 C_K=\max\left\{\frac4{K^2},\frac1{c(2-c)}\right\}.
$$
Then
$$
 F_K(s)\sim\sqrt{\frac{2s}{C_K}}\qquad(s\downarrow0).
$$
This infimum covers all finite independent families, including arbitrarily many heterogeneous variables, and can be approached to leading order by finite iid families. For $1<K<6/5$, two *distinct* nonzero jump sizes $K-1$ and $1$ improve on using just $K/2$; for $6/5<K\le2$ the latter homogeneous jump size suffices. At $6/5$ both constructions have the same leading constant. This is an asymptotic near full availability, not the entire finite-$s$ frontier. The underlying two-draw extremal and its transition are consequences of [L. E. Meester (2008), §3.3](https://arxiv.org/pdf/0808.1669), not new extremal probability formulae. We include an elementary derivation and the uniform reduction needed to apply them here.

## 1. Why a unit Poisson cannot dominate at fractional supply

Write $r=\lceil K\rceil\ge2$. The unique $\lambda>0$ with $\Pr(Z_\lambda\ge r)=s$, $Z_\lambda\sim{\rm Pois}(\lambda)$, minimizes Poisson throughput subject to stockout at least $s$: its tail increases strictly with $\lambda$ from 0 to 1, and throughput is increasing by independent increments. For every $n\ge r$, match this tail by $\Pr(B_n\ge r)=s$ with $B_n\sim{\rm Bin}(n,p_n)$. The root is unique by monotonicity. The $n$ iid individual demands take the value $K/r$ with probability $p_n$, and otherwise zero. Thus they have the prescribed stockout exactly, but their relative throughput tends to
$$
 \mathbb E\min(Z_\lambda/r,1)
 < \mathbb E\min(Z_\lambda/K,1).
$$
Indeed $np_n\to\lambda$ by bracketing $p_n$ between $a/n$ and $b/n$ for every $0<a<\lambda<b$ and all large $n$, using the binomial-to-Poisson limit at those fixed means. The bounded expectations converge, and the strict inequality holds already on $Z_\lambda=1$. Therefore a sufficiently large **finite** $n$ gives a strict witness. The class of allowed demands has upper bound one; it does not require attaining one. Even that optional extra normalization causes no problem: keep $n$ fixed after securing a strict gap, and on each nonzero occurrence independently upgrade the jump from $K/r$ to $1$ with a sufficiently small positive probability. The stockout event is unchanged because at most $r-1$ jumps sum to less than $K$, whereas any $r$ jumps still reach $K$. Throughput varies continuously and the strict gap persists.

For the promised rational example use $K=3/2$ and three independent demands equal to $3/4$ with probability $1/4$ and zero otherwise. The number of positive demands has masses $27,27,9,1$ divided by $64$. Thus availability is $27/32$ and relative throughput $47/128$. At $\lambda=\log2$ the corresponding Poisson availability and relative throughput are respectively $(1+\log2)/2>27/32$ and $1/2-(\log2)/6>47/128$. The bounds $11/16<\log2<3/4$ follow by summing $2\sum_{j\ge0}(1/3)^{2j+1}/(2j+1)$, retaining its first two terms for the lower bound and dropping denominators for the upper bound. Any smaller Poisson mean fails on availability, and any larger mean fails on throughput.

For completeness, if $0<K\le1$, then $T/K\ge s$ trivially; equality is reached with one Bernoulli demand of size $K$, and ordinary Poisson at matching stockout also has relative throughput $s$. Neither this observation nor the fractional example decides the interior of the integer-$K\ge2$ frontier.

## 2. The two-jump extremal

For $1<t\le2$, let $I_t(\nu)=\int\!\int\mathbf1_{x+y\ge t}\,\nu(dx)\nu(dy)$ for a finite positive measure on $[0,1]$. Then
$$
 I_t(\nu)\le C_t\left(\int x\,\nu(dx)\right)^2.                 \tag{1}
$$
This is sharp. By homogeneity normalize the first moment to one (zero moment is trivial); mass at zero is irrelevant. Write $h=t/2$ and $c=t-1$. If $t=2$, only $x=y=1$ can count, proving (1). Otherwise the low part $x<h$ has no internal pairs, whereas the high part $y\ge h$ counts all pairs within that part. With the high measure fixed the cross term is linear in the low measure. For fixed low first-moment budget, its contribution is bounded by the supremum obtained by placing the entire low budget at one point $x\in[c,h)$. This follows by averaging $\nu_{\rm high}([t-x,1])/x$ against $x\nu_{\rm low}(dx)$; points in $(0,c)$ have zero payoff. No assertion of attainment of that one-variable supremum is needed. Zero low budget gives at most $h^{-2}$; zero cross payoff gives the same bound.

For such a fixed $x$, move high atoms in $[h,t-x)$ to $h$, and those in $[t-x,1]$ to $b=t-x$, preserving their counts. Every paying pair remains paying, while the total first moment can only decrease. Normalize back to unit cost by scaling all masses, so the value can only increase. The resulting measure has counts $L,H,B$ at $x,h,b$, with $xL+hH+bB=1$, and payoff $(H+B)^2+2LB$. Fix $L$. As a function of $B$, $H+B=(1-xL)/h-(b/h-1)B$ is affine, so the payoff is convex. At an endpoint either $B=0$, giving at most $h^{-2}$, or $H=0$. In the latter case
$$
 B^2+2B(1-bB)/x\le 1/[x(2b-x)].
$$
The maximum occurs at $B=1/(2b-x)\in[0,1/b]$. The denominator $x(2t-3x)$ is concave in $x$, so its minimum on $[c,h]$ is attained at an endpoint. Their reciprocals are $1/[c(2-c)]$ and $4/t^2$. Both are attained: use just mass $1/h$ at $h$, or use masses $B=1/(2-c)$ at 1 and $L=(1-B)/c$ at $c$. At $t=2$ the single mass at one suffices. The sign of the difference between the two constants is decided by $(1+c)^2-4c(2-c)=(1-c)(1-5c)$.

For comparison to Meester's complete fixed-mean two-iid-draw theorem, substitute $Y=1-X$, his threshold $t'=2-t$ and his mean $m=1-u$, with $u$ small. His §3.3 table gives $u^2/(1-(t')^2)$ or $u^2/(1-t'/2)^2$ and a transition at $t'=4/5$. These are exactly the constants and supports in (1), after reversing the variables and scaling the positive masses. Conversely, a finite measure of unit first moment can be embedded in a probability law by scaling by sufficiently small $u$ and adding an atom at zero; the extra mass never contributes to a pair reaching $t>1$. Thus no priority is claimed for (1) or this crossover.

## 3. A uniform reduction for arbitrary independent demands

Let $\mu=\sum_i\mathbb EX_i$. Two uniform estimates used below are
$$
 1-e^{-\mu}\le T\le\mu,\qquad 0\le\mu-T\le\mu^2/2.           \tag{2}
$$
Indeed $\min(S,K)\ge\min(S,1)\ge1-\prod_i(1-X_i)$ for $K\ge1$, so independence gives the first inequality. For the second, pointwise $(S-K)_+\le(S-1)_+\le\sum_{i<j}X_iX_j$. To see the last bound, given numbers $x_i\in[0,1]$, introduce independent Bernoulli variables with these means and sum $N$. The pointwise inequality $\binom N2\ge N-1$ plus nonnegativity gives $\sum_{i<j}x_ix_j\ge(\sum_i x_i-1)_+$. Taking expectations proves (2). In particular small $T$ implies $\mu\to0$ and then $T/\mu\to1$. Small stockout alone need not imply small $\mu$.

For fixed $1<K\le2$ and any $0<\eta<K-1$, choose $0<d<\eta/3$. Split $X_i$ into its small value $Y_i=X_i\mathbf1_{X_i\le d}$ and a possible large jump. The $Y_i$ are independent across $i$. For $0<\mu<1$ use $u=d^{-1}\log(1/\mu)$. Convexity of the exponential on $[0,d]$ yields
$$
 \Pr(\textstyle\sum_iY_i>\eta)\le
 e^{-u\eta}\exp\{\mu(e^{ud}-1)/d\}\le e^{1/d}\mu^{\eta/d}=o(\mu^2).
$$
The number of large jumps has a Poisson-binomial law with sum of individual probabilities at most $\mu/d$; the third factorial-moment union bound gives probability of at least three at most $(\mu/d)^3/6$. These constants do not depend on $n$ or the marginal distributions. With neither exceptional event, stockout forces two jumps whose sum is at least $K-\eta>1$. Let $\nu$ be the sum of the marginal measures restricted to $(d,1]$. Independence and a union bound over distinct unordered pairs, followed by adding the nonnegative diagonal terms of the product measure, give
$$
 s\le \tfrac12 I_{K-\eta}(\nu)+o(\mu^2)
   \le\tfrac12 C_{K-\eta}\mu^2+o(\mu^2).
$$
First send $\mu\downarrow0$ at fixed $d,\eta$ and then $\eta\downarrow0$. The explicit $C_t$ is left-continuous through $t=2$. Hence for every sequence of independent finite demand families with $\mu\to0$,
$$
 \limsup s/\mu^2\le C_K/2.                                    \tag{3}
$$

## 4. Attaining the coefficient at every sufficiently small prescribed stockout

Let $\nu$ be an attaining finite measure from (1), of unit first moment and mass $M$, so $I_K(\nu)=C_K$. Fix an integer $N\ge2$. Give each of $N$ iid buyers a positive jump according to the measure $(a/N)\nu$, and put the remaining probability at zero, for $a\ge0$ sufficiently small. The total mean is $a$. Exactly two active buyers produce stockout with probability
$$
 \binom N2(a/N)^2(1-aM/N)^{N-2} C_K.
$$
The probability of three or more active buyers is $O_N(a^3)$, and one jump cannot reach $K$. Consequently $s_N(a)=\tfrac12(1-1/N)C_K a^2+O_N(a^3)$. Stockout probability is a continuous polynomial, nondecreasing under common retention of more jumps. Its positive quadratic leading term also makes it strictly increasing for all sufficiently small positive $a$. It therefore attains every sufficiently small prescribed $s$, with $a\sim\sqrt{2s/((1-1/N)C_K)}$. Throughput is at most $a$. Taking $\limsup_{s\downarrow0}$ and then sending $N\to\infty$ proves the upper bound in Theorem B; no uniform-in-$N$ expansion was assumed.

In particular $F_K(s)=O(\sqrt s)$. Given any sequence $s\downarrow0$, choose feasible instances of throughput at most $F_K(s)+s$. Their throughputs vanish, so by (2) their means vanish and $T\sim\mu$. Applying (3) gives $\liminf F_K(s)/\sqrt s\ge\sqrt{2/C_K}$. This proves Theorem B.

## Consequence: a choice of Poisson jump size does not always repair the benchmark

When $1<K<6/5$ and $s$ is sufficiently small, admissible finite iid inputs also have strictly lower absolute throughput than every **single-scale** Poisson total $hZ_\lambda$, $0<h\le1$, with stockout at least $s$. Here the jump size as well as the mean may be optimized anew for each $s$.

Indeed let $r=\lceil K/h\rceil\ge2$. Then $h\ge K/r$, and for the unique $\lambda_r$ matching the stockout target at count $r$, throughput is at least $K\,\mathbb E\min(Z_{\lambda_r}/r,1)$. For $r=2$, $s\sim\lambda_2^2/2$ and this lower bound is asymptotic to $K\sqrt{s/2}$. For $r\ge3$, the factorial-moment bound gives $s\le\lambda_r^r/r!$, and $r!\ge(r/e)^r$ by integrating $\log x$. Thus $\lambda_r/r\ge s^{1/3}/e$ uniformly. Since $\min(j/r,1)\ge1-(1-1/r)^j$, their absolute throughputs are bounded below by $K(1-\exp(-s^{1/3}/e))$, which is asymptotically much larger than $\sqrt s$. Theorem B has strictly smaller leading constant than $K/\sqrt2$ throughout $1<K<6/5$, and its upper construction uses finite iid demands. This separates even arbitrary single-scale rescalings of Poisson, not all compound Poisson laws with mixed jump sizes.
