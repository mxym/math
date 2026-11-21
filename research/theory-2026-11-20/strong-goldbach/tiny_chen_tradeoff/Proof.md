# A pointwise tradeoff between the critical even-rank loss and actual odd composites

Use the central reflected prime slice of [the critical-rank tilt](https://github.com/mxym/math/commit/c8319147): $P$ is even, $p$ prime, $m=P-p\in[P/3,2P/3]$. Set $L=\log P$, $H=\log\log P$, $U=\mathfrak S(P)P/(3L^2)$ with the usual Goldbach singular series, $D=\exp(L/H^A)$ for fixed $A>0$, and $z=u/H$ for fixed real $u>0$. The sum $G(P)-J_P(u)$ has nonnegative charge $(k-2)z^{k-1}$ on each squarefree rank $k\ge3$, zero elsewhere. Let $E_+(P,u)$ denote **only its even ranks $k\ge4$**.

For odd squarefree $d\le D$ coprime to $P$ define
$$
 K_d=\#\{P=p+dq:q\text{ prime},\ dq\text{ central}\},\qquad
 V_d=\#\{P=p+drs:r<s\text{ primes},\ r>P^{.1},\ drs\text{ central}\}.
$$
Here and below $p$ is a genuine prime. Put $j=\omega(d)$ and
$$
 B_-(P,u)=\sum_{\substack{d\ \mathrm{admissible}\\ j=\omega(d)\ \mathrm{odd},\ j\ge3}}(j-1)z^j V_d,
$$
where the sum is over the indicated admissible $d$. Every physical row in $B_-$ has $\mu(m)=-1$ and rank at least five, and is counted once: $d$ contains all its factors below $P^{.1}$. **Its displayed weight is a boundary weight**, larger by order $1/z$ than its ordinary rank-tilt charge; it is not an estimate on the latter at the prime-pair scale.

**Theorem.** Uniformly in all sufficiently large even targets, for fixed $A,u$,
$$
 E_+(P,u)+B_-(P,u)\ \ge\ (.03-o(1)) U\,(u\cosh u-\sinh u).                 \tag{1}
$$
Two consequences frame the genuine arithmetic alternatives:

* If there are no odd-rank squarefree complements on this true prime slice, then $G(P)=0$, $B_-=0$, and $J_P(u)\le-c_u U$ for every fixed $u>0$. In particular the surviving subpower multipliers generate a negative charge **on the natural scale**, not only $1/H$ times that scale. A mere Goldbach exception need not satisfy this stronger premise.
* Conversely, if the entire near-unit range is absent ($K_d=0$ for every admissible $d\le D$), then for every fixed $j\ge0$ there are at least $(.03-o_j(1))UH^j/j!$ genuine squarefree reflected complements of rank $j+2$ with exactly two distinct primes above $P^{.1}$ and the other $j$ factors in $d\le D$. In particular both genuine Möbius signs occur. At ordinary tilt weights each such fixed-rank lower contributes at order $U/H$, not $U$.

No signed lower for a prime pair, unconditional absence of either branch, or uniform positive $J_P(u)$ is asserted.

## 1. A selective tiny-multiplier Chen bound

For every set of real multipliers $0\le b_d\le1$ on the admissible $d$ we have, for each fixed $M>0$,
$$
 \sum_{d\le D} b_d(K_d+V_d)\ \ge\ (.0335-o(1)) U\!
    \sum_{d\le D}\frac{b_d}{d}\prod_{w\mid d}\frac{w-1}{w-2}
     -O_{A,M}(P L^{-M}).                                                \tag{2}
$$
The same $b_d$ is used throughout the actual prime and switched bound. The $o(1)$ is uniform and multiplies the selected mass. The constant is deliberately not optimized.

Write $a=(P-p)/d$, and apply the [three-term Chen inequality and certified linear-sieve integrals](https://github.com/mxym/math/commit/5267e5b7) with lower rough cutoff $Z=P^{.1}$ and upper marking cutoff $y=P^{1/3}$. In the rough rows $a\le2P/(3d)<y^3$; a squarefree $a$ of rank at least three has either two or more factors in $(Z,y)$ or an exceptional triple $a=rst$, $Z<r<y\le s\le t$, with one such factor. These are removed by half of the singly marked sum and half of the exceptional triple count. A repeated prime above $Z$ costs $O(P^{1-.1+o(1)})$ globally even allowing all divisor choices: count $w^2\mid P-p$ by integers, $\sum_{Z<w\ll\sqrt P}(P/w^2+1)\ll P/Z+\sqrt P$, and use fixed divisor powers $P^{o(1)}$ for all multiplicities. In retained rough rows $a$ is coprime to $d$ automatically since eventually $D<Z$.

In the direct sieve $p\equiv P\bmod d$, with principal mass $P(1+o(1))/(3\varphi(d)L)$. For a squarefree sifting modulus $e$, the true modulus is the **product** $de$ even when $e,d$ overlap; if $w\mid d,e$ the prime progression therefore has $w^2$ in its modulus. Since the residue $P$ is a unit, the conditional local probabilities are $1/(w-1)$ outside $Pd$, $1/w$ for $w\mid d$, and zero for $w\mid P$. A target-prime divisor of $a$ is impossible outside the possible isolated $p=m=P/2$ row, which may be removed at cost $O(1)$. Use the same $P^\theta$, $P^\theta/r$ linear levels, $\theta=.479$. The physical moduli $de$ or $dre$ are $\le D P^\theta<P^{.49}$ eventually. Each accumulates $O(\tau(q)^2)$ occurrences from $d$ and a possible marked prime $r$. Prime BV with maximal prefixes, the trivial bound $O(P/\varphi(q))$ and Cauchy with reciprocal divisor moments give arbitrary log savings after this weight; square factors are ordinary allowable BV moduli. The singly marked $r>Z$ cannot divide $d$; $r\mid P$ is omitted, with reciprocal mass $O(L/Z)$.

In the direct Mertens product the adjustment for every $w\mid d$ is $(1-1/w)/(1-1/(w-1))=(w-1)^2/[w(w-2)]$. Consequently the *full direct main* has local multiplier
$$
 \frac1{\varphi(d)}\prod_{w\mid d}\frac{(w-1)^2}{w(w-2)}
   =\frac1d\prod_{w\mid d}\frac{w-1}{w-2}=:g(d).
$$
These exact factors matter since tiny tags may have small prime divisors. Mertens completion of target primes above $Z$ incurs uniform relative error $O(L/Z)$. The dimension-one sieve axiom is uniform since each local change only lowers a forbidden probability.

For the switched upper bound use the actual $n=d r s t$ with $P-n$ required prime. Its sifting level $P^{.499}$ and limit $P^{.249}$ are unchanged. On each full independent factor box keep the exact masked coefficient $b_d$. Group $d,r,s$ together and use the genuine prime $t$ as the independent Siegel–Walfisz factor. The grouped coefficient is divisor-bounded; in fact $d$ is the unique tiny part since $D<Z$, and the two larger grouped primes have at most two orders. Both grouped lengths are in $[P^{.2},P^{.8}]$. The [balanced convolution large-sieve proof with induced characters](https://github.com/mxym/math/commit/2f9bfe36) gives total absolute discrepancy $O_M(PL^{-M})$ to the needed level. Concretely use relative factor boxes of width $L^{-C}$ in each of $d,r,s,t$ (starting at $d=1$, so few or empty integer boxes are harmless). Keep boxes touching the central product and sorted marks. There are polylogarithmically many, and the nonnegative upper sieve allows enlargement. The mask $b_d$ is enforced on the individual integer throughout. This argument uses no Siegel–Walfisz assumption on $d$.

Reversing the reduced averages now gives for each selected $n$ a sieve product with local probabilities $1/(w-1)$ outside $nP$, zero otherwise. The deleted primes of $d$ contribute $\prod_{w\mid d}(w-1)/(w-2)$; deleting the three remaining polynomially large prime slots changes that by $1+o(1)$. Possible nonunit slots dividing $P$ do not increase this uniform upper. The source count at each $d$ is at most $(I_*+o(1))P/(3dL)$, where
$$
 I_*=\int_{.1}^{1/3}\frac{\log(2-3t)}{t(1-t)}\,dt .
$$
Indeed for fixed first two prime slots the last is in the enlarged central interval divided by $drs$; its prime count is bounded by the full interval length over its log, and $s\le(1+o(1))\sqrt{(2P/3)/(dr)}$. The prime PNT and Mertens give the same uniform compact exponent integral as in the tagged proof since $\log d=o(L)$ uniformly, all three logs are $\gg L$, and $1/d$ is retained in the length. This integrates over the smaller of the two final slots up to the square root; no unordered-factor multiplier is missing. The sieve constant is $2/.499$; taking the exceptional half-charge gives $I_*/.499$ against the exact same $U g(d)$ as the direct side.

Thus the net lower coefficient in (2) is at least the same certified integral as for the marked Chen theorem, $4196921349/125000000000>.0335$; it includes both linear-sieve corrections above the elementary branches. Upper/lower model errors are relative and uniform, while the BV errors have arbitrary negative log power. This proves (2) for arbitrarily selected tags; it is not a claim that the individual estimate holds with relative error for every $d\le D$.

## 2. Critical harmonic mass, true signs and the sharp boundary cost

Locally uniformly on the complex $v$-plane,
$$
 \sum_{d\le D\ {\rm admissible}} g(d)(v/H)^{\omega(d)}\ \longrightarrow e^v.       \tag{3}
$$
For $w>2$, $g(w)=1/w+O(1/w^2)$, and deleting $w\mid P$ costs $O(\log H+1)$ in the reciprocal sum: up to $L$ use Mertens, above $L$ there are $O(L/\log L)$ divisors each contributing $O(1/L)$. Also $\log\log D=H-A\log H$. Thus the product for all $2<w\le D$, $w\nmid P$, tends to $e^v$ uniformly. Cutting back to the integer bound $d\le D$ costs $O_R(1/H)$ in absolute value on $|v|\le R$, via $1_{d>D}\le\log d/\log D$ and $\sum_{w\le D}g(w)\log w\ll\log D$. This proves (3) and its derivative versions; individual rank $j$ harmonic mass is $(1+o_j(1))H^j/j!$.

Take $b_d=(j-1)z^j$ for odd $j\ge3$, zero otherwise. These weights are nonnegative and $\le1$ when $P$ is large for fixed $u$. The $K_d$ contribution is a subpopulation of $E_+$ with **exactly** its ordinary weight since its physical rank is $j+1$. The $V_d$ contribution is $B_-$. By (3) the limiting harmonic mass is $u\cosh u-\sinh u$. This proves (1). Selection of one fixed rank instead proves the asserted no-near-unit consequence, with distinct physical rows by uniqueness of the tiny part. This gives a genuine single-target alternative; no dyadic statement is used in its proof.

The amplified boundary is too large **in the true integers** to dismiss by absolute values. In fact, with $P$ restricted to even integers,
$$
 \frac{2\log^2 X}{X^2}\sum_{X<P\le2X} B_-(P,u)
      \longrightarrow (\log 9)(u\cosh u-\sinh u).
 \tag{4}
$$
Here is the calculation. In an independent count of $p,r,s$, fix odd squarefree $d$ in the common subpower range. Roles are $r<s$, with $r>P^{.1}$. For fixed $r$, the primes $p,s$ range over the same central polygon in $(p/X,drs/X)$ of area $1/2$ as in the critical tilt proof. For $\log r/\log X$ in a closed subinterval of $(.1,.5)$ the inequality $r<s$ is automatic for large $X$, and PNT gives the polygon main $(1+o(1))X^2/[2dr\log X\log(X/(dr))]$, uniformly by squeezing between fixed mesh boxes. The boundary strips of width $\delta$ in this exponent have upper size $O(\delta+o(1))X^2/(d\log^2 X)$ by the same PNT upper bound with order dropped and prime Mertens; no $r$ above $X^{.5+o(1)}$ is admissible. Let $\delta$ tend to zero. Removing $(d,P)>1$ is automatic since $p>d$; if a prime of $d$ divides $P=p+drs$, it would divide $p$. The integrated constant is $\int_{.1}^{.5}dt/[t(1-t)]=\log9$.

One may use the common lower/upper cutoffs $D_{\min}=\exp(\log X/(\log\log X)^{A+1})$, $D_{\max}=\exp(\log X/(\log\log X)^{A-1})$ for fixed $A>0$ (when $A\le1$, use exponents $A+1$ and $A/2$ instead). Both are subpower and enclose the target-dependent cutoff throughout the dyad in their respective cases. By the same Euler marking argument as (3), without the now-automatic target deletions and with $1/d$ in place of $g(d)$, both harmonic sums of the nonnegative weights have the same limit. Replacing $H$ by $\log\log X$ also follows by squeezing or the uniform Euler derivative bound. This proves (4). The dyadic mean of $U$ in the same normalization is $1$: expanding the usual singular series on even integers gives $\sum_{P\le x,\ 2\mid P}\mathfrak S(P)\sim x$ since $\prod_{w>2}(1-1/(w-1)^2)(1+1/[w(w-2)])=1$, and then use partial summation.

In particular a scheme that tries to retain the $.03$ lower benchmark in (1) and discard the entire $B_-$ by a uniformly smaller absolute upper bound cannot succeed. This identifies a concrete cost on true prime rows, not a synthetic parity model. A signed estimate tying it to $G$ or an independent same-scale positive source is still missing.
