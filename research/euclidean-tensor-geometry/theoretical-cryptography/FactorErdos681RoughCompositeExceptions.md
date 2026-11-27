# Rough composite witnesses with a near-power-saving exceptional set (Erdős #681)

Write $p_-(m)$ for the least prime factor of $m>1$. [Erdős problem #681](https://www.erdosproblems.com/681) asks whether, for every sufficiently large $n$, some shift $k\ge1$ gives a composite $n+k$ with $p_-(n+k)>k^2$. The assertion for almost all $n$ by itself is immediate from $k=1$. We prove a substantially smaller exceptional set for a stronger condition, using only unconditional sieve and concentration arguments.

**Theorem.** Let $H=\lfloor(\log X)^3\rfloor$. There are absolute constants $c,C>0$ such that all but at most
$$
C X\exp\!\left(-c\frac{\log X}{\log\log X}\right)
\tag{1}
$$
integers $n\in[X,2X]$ have at least $cH/\log H$ distinct shifts $1\le k\le H$ for which
$$
H^2 < p_-(n+k)\le H^3.
\tag{2}
$$
In particular $n+k$ is composite for large $X$, since $H^3<X$. Each such shift satisfies $p_-(n+k)>k^2$. The all-starting-point question is not resolved.

More generally the same assertion holds for $H=\lfloor(\log X)^B\rfloor$, any fixed $B>2$, and any fixed pair of thresholds $H^{\beta_1}<p_-(n+k)\le H^{\beta_2}$ with $1/B<\beta_1<\beta_2$. The positive constants can depend on $B,\beta_1,\beta_2$.

## 1. A conditional local-density statement

Put $L=\log X$, $z_0=\lfloor L/100\rfloor$ and $Q_0=\prod_{p\le z_0}p$. Write
$$
 I_a=\{n\in[X,2X]\cap\mathbb Z:n\equiv a\bmod Q_0\},\qquad
 S_a=\{1\le k\le H:\gcd(a+k,Q_0)=1\},\qquad m_a=|S_a|.
$$
For large $X$, the prime number theorem gives $Q_0\le X^{1/50}$, so $|I_a|\ge X^{0.97}$ uniformly in $a$. The lower linear sieve gives, uniformly,
$$
m_a\gg_B H/\log H.
\tag{3}
$$
For clarity, apply the dimension-one lower [Rosser–Iwaniec sieve](https://www.impan.pl/shop/publication/transaction/download/product/102606?download.pdf=) to an interval of $H$ consecutive integers representing $a+k$. The multiples of a squarefree $d$ have count $H/d+O(1)$. Choose a fixed $2/B<\rho<1$ and level $D=H^\rho$. Then $s=\log D/\log z_0\to B\rho>2$; choose $\rho$ small enough that $B\rho<3$. The lower sieve function $f(s)=2e^\gamma\log(s-1)/s>0$ in this range. The total remainder is $O(D)=o(H/\log H)$ because the lower sieve weights are bounded by one. Mertens' product formula gives (3).

For a fixed $\beta>1/B$, set $W=H^\beta$ and
$$
R_W(n)=|\{1\le k\le H:p_-(n+k)>W\}|,\qquad
\xi_W=\prod_{z_0<p\le W}(1-1/p).
$$
We will show that for each fixed $0<\varepsilon<1$,
$$
\mathbb P_{n\in I_a}\!\left(\left|R_W(n)/m_a-\xi_W\right|>\varepsilon\right)
\ll_{B,\beta,\varepsilon}\exp(-c_{B,\beta,\varepsilon}L/\log L)
\tag{4}
$$
uniformly over $a$. By Mertens, $\xi_W=(B\beta)^{-1}+o(1)$. Apply (4) to $\beta_1,\beta_2$ with fixed $\varepsilon$ smaller than one eighth of $(B\beta_1)^{-1}-(B\beta_2)^{-1}$. Outside the union of their exceptional sets, the difference of counts is at least a fixed positive multiple of $m_a$. Summing over classes and using (3) proves (1)–(2) and the generalization.

## 2. Concentration in the independent residue model

Fix the class $a$. Start with $S_a$ and, independently for each prime $z_0<p\le W$, remove all remaining sites in a uniformly chosen residue class modulo $p$. Let $R$ be the number left at the end. The expected value is $m_a\xi_W$. To see the required exponential tail without a fixed-dimensional moment theorem, reveal these primes successively. At the stage of prime $p$, let $N$ be the number of sites before that stage and $K$ the number it removes. Given the past, $\mathbf E K=N/p$. The difference of successive conditional expectations of the final count is
$$
D_p=w_p(N/p-K),\qquad w_p=\prod_{p<q\le W}(1-1/q),
$$
where $q$ runs over primes. Indeed, each remaining site survives the future choices with probability exactly $w_p$. Its conditional variance is bounded by $\mathbf E(K^2\mid\mathrm{past})\le \lceil H/p\rceil N/p$, since a single residue class meets the original interval in at most $\lceil H/p\rceil$ sites.

For all the increments, $|D_p|\le H/z_0+1=:b$. A deterministic upper bound for the sum of the conditional variances is
$$
 V\ll m_a\left(H\sum_{p>z_0}p^{-2}
           +\sum_{H<p\le W}p^{-1}\right)
 \ll_{B,\beta} m_a\left(\frac{H}{z_0\log z_0}+1\right).
\tag{5}
$$
In deriving the first bound, use $\lceil H/p\rceil\le 2H/p$ for $p\le H$ and $\lceil H/p\rceil=1$ for $p>H$. The prime-square reciprocal tail follows from the prime number theorem (a Chebyshev upper bound suffices), and the remaining reciprocal interval has a bounded sum by Mertens. If $W\le H$, the second sum is empty.

Here is the short moment generating function argument. Set $\lambda=1/(2b)$. For each conditionally mean-zero increment,
$$
\mathbf E(\exp(\pm\lambda D_p)\mid\mathrm{past})
\le \exp(C\lambda^2\mathbf E(D_p^2\mid\mathrm{past})).
$$
This follows by Taylor's formula on $|\lambda D_p|\le1/2$. In applying it successively one may use the deterministic individual variance bounds that sum to (5). For any fixed $s>0$, Markov's inequality gives an upper bound $2\exp(-\lambda s m_a+C\lambda^2 V)$ for a deviation of magnitude $s m_a$. Since $\lambda V/m_a=O(1/\log z_0+z_0/H)=o(1)$, (3) and $z_0\asymp L$ give
$$
\mathbb P\bigl(|R/m_a-\xi_W|>s\bigr)
\ll_{B,\beta,s}\exp(-c_{B,\beta,s}L/\log L).
\tag{6}
$$
In particular, this estimates the upper as well as the lower tail. It does not impose the incorrect assumption that individual candidate sites have independent survival events.

## 3. Transfer of moments of growing order

In this section fix $B,\beta,\varepsilon$. For any desired constant $K_0>0$, the following comparison holds. Let $r$ be the largest even integer not exceeding $\eta L/\log L$, with a sufficiently small fixed $\eta>0$. For each subset $S\subset S_a$ with $|S|\le r$, the probability that all its sites survive up to $W$ in the independent model and the probability that their actual translates $n+k$ are all $W$-rough for uniform $n\in I_a$ differ by at most
$$
e^{-K_0r}+X^{-1/2}.
\tag{7}
$$

To prove this, put $\nu_p=|\{k\bmod p:k\in S\}|$. In the independent model the simultaneous survival probability is $\prod_{z_0<p\le W}(1-\nu_p/p)$. In the class $I_a$, impose instead exclusions of the residues $n\equiv-k\bmod p$. For a finite set of primes $E\subset(z_0,W]$ the intersection of the corresponding **removal** events has normalized density
$$
\prod_{p\in E}\nu_p/p\ +\
O\!\left(\frac{\prod_{p\in E}\nu_p}{|I_a|}\right).
$$
This uses the Chinese remainder theorem on the consecutive integers parametrizing $n=a+Q_0t$; each inverse image modulo $\prod_{p\in E}p$ counts with error at most one. Apply the two consecutive Bonferroni truncations with orders an even $J$ and $J+1$, where $J=C_0r+O(1)$ and $C_0$ is fixed and large. Mertens gives $\sum_{z_0<p\le W}\nu_p/p\ll_{B,\beta} r$. Thus the absolute tail of the corresponding independent expansion is at most
$$
\sum_{j>J}\frac{(C_{B,\beta}r)^j}{j!}\le e^{-(K_0+2)r}
$$
if $C_0$ is large enough, by $j!\ge(j/e)^j$ and a geometric tail bound. The cumulative arithmetic rounding error on either truncation is at most
$$
\frac{(J+2)(rW)^{J+1}}{|I_a|}.
$$
Here $\log(rW)\ll_{B,\beta}\log L$. Because $|I_a|\ge X^{0.97}$, the last expression is at most $X^{-1/2}$ for a sufficiently small $\eta>0$. This proves (7) uniformly in the set of sites, the small-prime class, and $X$. The proof never equates the actual distribution of the residues modulo their entire (much larger) product with that of the independent model.

For each $0\le j\le r$, expand $(R_W(n)/m_a)^j$ as an average over ordered tuples of $j$ sites in $S_a$. Repeated sites can be dropped from each survival event. So (7) compares this moment with the analogous model moment to the same accuracy. The absolute coefficient sum of $(t-\xi_W)^r$ is $(1+\xi_W)^r\le2^r$, and $r$ is even. Consequently
$$
\mathbb E_{n\in I_a}|R_W(n)/m_a-\xi_W|^r
\le (\varepsilon/2)^r+C e^{-c_\varepsilon L/\log L}
    +2^r(e^{-K_0r}+X^{-1/2}),
$$
by splitting the model moment at deviation $\varepsilon/2$ and using (6). Choose $K_0>\log(2/\varepsilon)+2$ and then $\eta>0$ small enough that $\eta\log(1/\varepsilon)<c_\varepsilon/2$, as well as satisfying (7). After division by $\varepsilon^r$, all terms are $O(\exp(-c' L/\log L))$. This proves (4).

## 4. Scope and checks

- The original question is in [Erdős, *Some unconventional problems in number theory* (1979), Acta Math. Acad. Sci. Hungar. 33, 71–80, p. 74](https://www.renyi.hu/~p_erdos/1979-23.pdf), recorded as [#681](https://www.erdosproblems.com/681). The obstruction to a qualitative almost-all claim being meaningful is that $n+1$ is composite already outside the prime density. In contrast, (1) is smaller than $X/(\log X)^A$ for every fixed $A$, even without first restricting to $n+1$ prime, and (2) supplies many composite witnesses with large least factors.
- [Gafni–Tao, *Rough numbers between consecutive primes*](https://arxiv.org/abs/2508.06463) address #682 and use short-interval rough-number moments with a prime-gap requirement. We do not improve their #682 bound: we allow a longer polylogarithmic forward interval, ignore the ending prime gap, and use conditioning and a growing-order transfer to prove a different exceptional-set estimate for #681.
- The [fixed finite checker](verify_factor_erdos681_rough_moments.js) audits residue-class normalization, both Bonferroni signs and the mixed moments on 24 small toy wheels, with 18,320 exact assertions. It is separate from, and is not evidence for, the analytic asymptotic or its implicit constants. No general factorization or search claim is made.
