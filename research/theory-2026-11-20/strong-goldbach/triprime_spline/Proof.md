# A reciprocal triprime spline removes the semi–triprime leakage at the critical cutoff

Let $P$ be even, $L=\log P$, $m=P-n$, $F=nm$, and keep the actual squarefree mask $\mu^2(F)$. Use a fixed nonnegative smooth $W(n/P)$ with support in $(1/3,2/3)$, $X=P\int W$ and the ordinary Goldbach singular series $\mathfrak S(P)$. All estimates below are uniform in the individual even target, as $P\to\infty$, with constants allowed to depend on the fixed weight. There is no conjectural input.

The literal quadratic detector is $K_0(F)=\sum_{d\mid F}\mu(d)(\log F-2\log d)_+^2$. Its [squarefree first moment](https://github.com/mxym/math/commit/5190f4df) is $8X\mathfrak S(P)+O_A(PL^{-A})$. The preceding [genuine semiprime transfer](https://github.com/mxym/math/commit/bae0d391) removed the spurious prime-leg signal but left a positive semi–triprime score on balanced triples. We remove that score in actual total variation by a signed, source-dependent progression calculation. It also eliminates a triprime against **every fixed even rank**, with the same detector.

## Construction and statement

Put $h=L^{-1/4}$. Choose smooth $0\le b_h,c_h\le1$ on the positive half-line, with $b_h=1$ up to $1/2-2h$ and $b_h=0$ from $1/2-h$ onwards, and $c_h=0$ up to $h$, $c_h=1$ from $2h$ onwards. Use fixed rescaled transition shapes, with derivatives of order $j$ bounded by $O_j(h^{-j})$. Set
$$
 \Phi(n)=\sum_{d\mid n}\mu(d)b_h(\log d/L),\qquad
 T_2(qs)=8\log q\log s\quad(q<s\ {\rm prime}),
$$
with $T_2=0$ elsewhere. For a triple of distinct primes with product $n$ write $x=(\log p_i/\log n)_{i=1}^3$, $s_I=\sum_{i\in I}x_i$ and $\epsilon_I=(-1)^{|I|}$. Define
$$
 M_j(x)=\sum_{s_I<1/2}\epsilon_I s_I^j,\qquad
 S_x(t)=\sum_I\epsilon_I(t-s_I)_+^2 .
$$
Here $s^0=1$, including $s=0$. Use $M_j$ with the identical definition for other squarefree leg profiles. No subset of the prime factors of a squarefree leg with normalized logarithms has sum exactly $1/2$: this would give a perfect square. A balanced triple has all $x_i<1/2$. Its $M_0$ is $-2$, and an unbalanced triple has $M_0=0$.

Define $J(n;m)=0$ unless $n$ is a genuine distinct-prime triple and $\min x_i>2h$. On such a source set
$$
 \begin{split}
 w_{x,h}(t)&=8\,b_h(t)c_h(t)\{S_x(t)+M_0(x)t(1-t)\},\\
 J(n;m)&=L^2 \sum_{d\mid m}\mu(d) w_{x,h}(\log d/L),\\
 D(n,m)&=K_0(F)-T_2(n)\Phi(m)-T_2(m)\Phi(n)-J(n;m)-J(m;n).
 \end{split}
$$
The final displayed definition of $D$ is used on all rows, whether or not $J$ vanishes. On the squarefree mask write $a=\omega(n)$, $b=\omega(m)$. All sums in the following statements include $W(n/P)\mu^2(F)$.

1. The full signed sum of $D$ equals $8X\mathfrak S(P)+O_A(PL^{-A})$ for every fixed $A$.
2. On a true prime pair the score is $4\log n\log m$. On **every** prime $p$ against a squarefree composite $u$ the exact score is $-(1+\mu(u))(\log(u/p)_+)^2\le0$. No cutoff on the composite rank is needed.
3. For every fixed $r$, the sum of $|D|$ on $a=3$, $b$ even, $b\le r$, is $o_r(X\mathfrak S(P))$; likewise upon reflection. The same total-variation conclusion holds for $a,b$ both even with $a+b\le r$.
4. On $a=b=3$ the sum of $|D+4L^2 M_0(x)M_0(y)|$ is $o(X\mathfrak S(P))$, $y$ the other leg's own-log profile. Thus the leading physical score is $-16L^2$ for balanced against balanced and zero otherwise. No frequency of such pairs at one $P$ is asserted.

The result makes **no** uniform-in-rank assertion, no total-variation assertion for the moving detector on unrestricted rank, and no sign claim on $2\times5$, $3\times5$, or the full remaining nonprime population.

## Signed first moment on the actual equation

We give details for the cutoff reaching $P^{1/2}\exp(-L^{3/4})$. The distribution input is [Motohashi, 1976, Theorem 2, pp. 273–274](https://www.jstage.jst.go.jp/article/pjab1945/52/6/52_6_273/_pdf/-char/en). For fixed $j\ge2$, the indicator of integers that can be written as $p_1\cdots p_j$ with each $n^{u_i}<p_i<n^{v_i}$ satisfies his property (C) **uniformly in the exponent windows**. Property (C) is the sum over $q\le P^{1/2}L^{-B(A)}$ of the maximum over reduced residue classes and prefixes of discrepancy from the actual reduced-class average, bounded by $O_A(PL^{-A})$. These are the source's own-log windows, exactly what we need. No distribution past the critical level or uniformity in $j$ is used.

Sort the own-exponents into bins of width at most $L^{-C}$, including boundaries $2h,1/2$ for the triple. For the lower bound $2h$ one may work throughout with inclusive/strict endpoints: a half-open interval on the finite inputs $n\le P$ is realized by an arbitrarily small endpoint perturbation and the uniform theorem, or subtract singleton boundary classes as limits. By using sorted bin **multisets** (bins may repeat) with the corresponding prime-product indicators one counts every source once. Factor order inside a repeated bin is immaterial. The value of $M_0$ on triprimes is constant within such a box by splitting at $1/2$. Freeze $x$ in $w_{x,h}$ at any representative of the box with the same $M_0$. The unrestricted error in this coefficient on $[0,1/2]$ is $O(L^{-C})$ by the uniform Lipschitz bound for the positive-part square and the eight terms; the cutoff multipliers depend on $t$ only. Thus the physical error, including $L^2$ and all its divisor labels, is $O_A(PL^{-A})$ by choosing $C$ first and the distribution accuracy afterwards. The number of boxes is polynomial in $L$. For the genuine semiprime use $8(\log n)^2 x_1x_2$, freezing the exponent product with the same precision and keeping $(\log n)^2W(n/P)$ by partial summation. There is no cutoff at the smaller semiprime factor.

**Squarefree and target masks.** We require $(n,P)=1$ on source rows. For the triple sources all prime factors exceed $\exp(cL^{3/4})$. Repeated primes there, or a source factor dividing $P$, affect $O(P\exp(-c' L^{3/4})+\sqrt P)$ inputs, by summing multiples of $p^2$, or over at most $O(L)$ primes dividing $P$. Their physical weights with divisor labels are negligible to every log order by Cauchy and fixed divisor moments. Their reduced-class main terms after summing reciprocal modulus weights are just as small. This argument may also be applied after opening the square mask below: the physical multiplicities are bounded by a fixed product of powers of divisor functions in $n,m$, and its required moments are polylogarithmic on average by Cauchy. For the semiprimes remove the $O(\sqrt P)$ squares in the same way, and remove target factors exceeding $L^{C'}$ at cost $O(PL^{1-C'}+\sqrt P)$ inputs before divisor-moment Cauchy, choosing $C'$ as large as required. On the remaining exception with a prime factor $\ell\mid P,\ \ell\le L^{C'}$, the source is $\ell p$. Apply ordinary maximal prime BV to $p\asymp P/\ell$; the congruence after opening the opposite side below is reduced and either impossible when $(\ell,q)>1$ or shifted by $\bar\ell\bmod q$. Here $q\le P^{1/2}\exp(-L^{3/4})L^{O(1)}<\sqrt{P/\ell}/(\log P)^{B'}$ for every fixed $B'$ and sufficiently large $P$. The own-log exponent windows on $\ell p$ give intervals in $p$ by monotonicity and can be handled by prefix differences, or do this subtraction for the whole log-weighted source instead of by bins. Two such small factors cannot make a central semiprime. Thus target-unit restriction creates no assumption on nonreduced BV.

On the surviving source $\mu^2(F)=\mu^2(m)$, $(m,P)=1$. Expand $\sum_{k^2\mid m}\mu(k)$, truncating at $k\le L^E$. The number of integers with any omitted square divisor is $O(PL^{-E}+\sqrt P)$, so the error from the original and truncated sums has arbitrary log accuracy by Cauchy/fixed divisor moments after choosing $E$. With $(k,P)=1$, split the squarefree divisor $d=e b$ in the test weight: $e\mid\operatorname{rad}(k)$ and $(b,kP)=1$. Its actual progression is $n\equiv P\bmod k^2b$, with $k^2b\le P^{1/2}\exp(-L^{3/4})L^{2E}$, reduced. BV for the indicated source gives its actual reduced-class average; the weight $\mu(e)\mu(b)f((\log b+\log e)/L)$ is bounded and now independent of $n$ for each box. The number of $k,e$ and source boxes is polylogarithmic, so choose the log accuracy of BV last. No estimates on the distribution of an unweighted remainder in a nonunit class are needed.

**Actual principal term.** Reverse the order in the reduced-class average. For each source $n$, the inner expression, times $\mu(e)/\varphi(k^2)$ when $(n,k)=1$, is
$$
 \sum_{(b,Pkn)=1}\frac{\mu(b)}{\varphi(b)} f\big((\log b+\log e)/L\big),
$$
where $f=b_h$ or a frozen $w_{x,h}$. The Mellin series is $\zeta(1+s)^{-1}\mathcal H_{Pkn}(s)$; compare the detailed Euler treatment in the [semiprime transfer](https://github.com/mxym/math/commit/bae0d391). For $H=Pkn\le P^3$, the correction factor is bounded by $(\log L)^{O(1)}$ in $\Re s\ge-c/\log L$ for a sufficiently small constant $c$: nondeleted normalized local factors converge absolutely there and the primes of $H$ above $L$ have reciprocal $p^{-1+c/\log L}$-sum $O(1)$ by $\log H=O(L)$, while the small ones cost a power of $\log L$. The $p=2$ factor is deleted since $P$ is even.

For precision, put $f_e(v)=f(v+\log e/L)$. Its derivative is zero at the origin. It has a bounded piecewise second derivative with $\int|f_e''|\ll L^{O(1)}$, no atoms from the quadratic spline knots (which are $C^1$), and its second derivative is supported in $v\ge h/2$ for large $P$. Express it as $\int_v^\infty (u-v) f_e''(u)\,du$. For the corresponding **unnormalized** linear log hinge at $Y=P^u$, Perron's kernel $Y^s/s^2$ and the classical zeta zero-free contour yield $\mathcal H_H(0)+O_A(L^{-A})$ uniformly in $h/2\le u\le1$ and $H\le P^3$. Indeed $\log Y\gg L^{3/4}$; truncate at $\exp(c'\sqrt{\log Y})$, shift to real part $-c''/\sqrt{\log Y}$ (inside the above Euler region), use the usual logarithmic reciprocal-zeta bound there, and note the original right-line absolute series at $\Re s=1/\log Y$ is polylogarithmic in $Y$. The shifted vertical error and truncated tails are $\exp(-c'''\sqrt{\log Y})L^{O(1)}$. The hinge normalized by $L$ has the same constant divided by $L$, which integrates to zero since $\int_0^\infty f_e''=-f_e'(0)=0$. All remaining losses are powers of $L$. This proves that every correction has signed mean $O_A(PL^{-A})$. The low collar is essential: without it the $M_0t(1-t)$ term would generally have a nonzero derivative at zero and a nonzero principal term.

## Reciprocal box-spline identity

Work temporarily in homogeneous profiles: each leg has total 1 instead of $(\log n)/L,(\log m)/L=1+O(1/L)$. For total rank bounded by $r$ this replacement in $K_0/L^2$ costs $O_r(1/L)$ by Lipschitz continuity of the quadratic hinge. Write $t_T=\sum_{i\in T}y_i$. The density of the sum of three independent uniforms on $[0,x_i]$ is $S_x(t)/(2x_1x_2x_3)$; in particular $S_x(t)=S_x(1-t)$, and $S_x(0)=S_x(1)=0$. Thus on a triprime against any even rank the ideal coupled sum is
$$
 4\sum_T\epsilon_T S_x(1-t_T)=8\sum_{t_T<1/2}\epsilon_T S_x(t_T).
$$
For even rank the complement has the same sign, so $M_0(y)=0$ and $\sum_{t_T<1/2}\epsilon_T\,8t_T(1-t_T)$ is half the full finite difference of the symmetric quadratic: $-8y_1y_2$ at rank 2, zero for even rank at least 4. The ideal unsmoothed correction
$$
 R_x(y)=8\sum_{t_T<1/2}\epsilon_T\{S_x(t_T)+M_0(x)t_T(1-t_T)\}
$$
therefore subtracts exactly the entire ideal $K_0$ minus the genuine-semiprime transfer on all such rows. On a prime partner it vanishes, both ideally and literally ($d=1$ has $w_{x,h}(0)=0$, the prime divisor is too large). Together with $\Phi(p)=1$ this preserves the exact prime-leg identities. On two even ranks the total rank is even and at least 4, so $K_0=0$ exactly: pair complementary divisors, and the full quadratic finite difference vanishes. Any remaining $T_2$ term vanishes in the ideal profile since $M_0$ of the even partner is zero.

For a triple $x$, pair complements in the full alternating first moment to get $2M_1(x)=M_0(x)$. In a contribution to $S_x(t_T)$ with $t_T<1/2$ only the lower subsets of $x$ occur. For two triples use $(v-u)_+^2+(u-v)_+^2=(u-v)^2$ on these two lower-subset lists. This gives
$$
 \begin{split}
 \sum_{t_T<1/2}\epsilon_T S_x(t_T)+\sum_{s_I<1/2}\epsilon_I S_y(s_I)
 &=M_0(x)M_2(y)+M_2(x)M_0(y)-2M_1(x)M_1(y),\\
 R_x(y)+R_y(x)&=4M_0(x)M_0(y).
 \end{split}
$$
Since $K_0$ vanishes at total rank 6, the residual is the stated nonpositive score. This reciprocity, not an estimate that treats the two genuine-source directions as independent, controls the sign newly introduced on triprime pairs.

## Cost of the collars on actual fixed-target rows

Write $s$ for a fixed cap on the **total** rank in each assertion. The number of $\mu^2(F)=1,\omega(F)\le s$ rows is $\ll_s P\mathfrak S(P)L^{-2}(1+\log L)^{2s}+O_s(P^{.7})$. If moreover either leg has a divisor in $[P^{1/2-Ch},P^{1/2+Ch}]$, for a fixed constant $C$, the same bound holds with an extra factor $h+L^{-1}$ multiplying its first term.

Here are details including nonrough inputs. For the latter estimate fix such a divisor $d$ on the first leg, with $\omega(d)\le s$ and $(d,P)=1$. Write $n=du$. Put $z=P^{1/[100(s+1)]}$ and expose the product $b$ of all remaining primes $\le z$ dividing $F$ but not $d$, so $b\le P^{.01}$, $\omega(b)\le s$, $(b,dP)=1$. Specify which of $u,P-du$ each prime of $b$ divides; this gives at most $2^{\omega(b)}$ classes modulo $b$. On each class sieve out all other primes $\le z$ not dividing $bd$ from these two forms. At $p\nmid Pbd$ there are two distinct roots, at $p\mid P$ only one. Omitting the at most $2s$ prime factors of $bd$ changes the local upper-product bound by a constant depending on $s$ (the prime 2 always divides $P$, never $bd$). The elementary dimension-two upper sieve at level $P^{.1}$ gives
$$
 \ll_s \frac{P\mathfrak S(P)}{db L^2}+O_s(P^{.1+o(1)})
$$
per class: the progression count at each squarefree sieve modulus $j$ has remainder bounded by $2^{\omega(j)}$; the sum to that level with the bounded upper-sieve weights is $P^{.1+o(1)}$. The level-to-sifting log ratio is $10(s+1)$; a fixed upper sieve bound suffices. Ignoring constraints at the omitted primes only enlarges the count. Summing errors over $d\le P^{.51}$ for sufficiently large $P$ and $b\le P^{.01}$ costs $O_s(P^{.7})$. The reciprocal $b$ sum, including class multiplicities, is $\ll_s(1+\log L)^s$. In each $d$ there is a prime $q\ge P^{.49/s}$; fix the remaining at most $s-1$ primes in $d/q$. The admissible $q$ lie in a multiplicative interval of ratio $\le P^{2Ch}$, still above $P^{.49/s}$. Partial summation of the classical prime number theorem, or Mertens with its standard $O(1/\log x)$ remainder, bounds their reciprocal sum by $O_s(h+L^{-1})$. Summing reciprocals of the other labels costs at most $(1+\log L)^s$. Reflection covers the other leg. The first, unrestricted rank count follows by the same sieve with $d=1$ and no $d$ sum.

Charge a crude $O_s(L^2)$ per row on all these exceptional divisors, covering both the actual and ideal expressions. The result is $o_s(X\mathfrak S(P))$. Elsewhere the upper collar $b_h$ agrees with the ideal strict half-indicator on every divisor of both legs, even after the $O(1/L)$ shift between the two central own-log normalizations and $L$. The missing low collar in $J$ costs at most $O_s(h)$ normalized, since $S_x(0)=0$, $S_x$ is uniformly Lipschitz and $t(1-t)=O(t)$. The smooth cutoffs need not be differentiated for this comparison. If a triple source has $\min x_i\le2h$, then either its two larger factors are within $O(h)$ of half (when balanced), already charged, or $M_0=0$. In the latter case pairing terms of $S_x$ that differ by the least factor gives $\sup_{0\le t\le1}|S_x(t)|\ll h$ by Lipschitz continuity of $v_+^2$ on $[-1,1]$. Omitting the entire source costs $O_s(h)$ also. All surviving normalized errors (including replacing $t=(\log d)/L$ in the polynomial/exact spline by its own-log value) are therefore $O_s(h+L^{-1})$. The unrestricted bounded-rank count proved above turns them into $o_s(X\mathfrak S(P))$. This proves the asserted total-variation statements without imposing a minimum prime power scale on the actual rows.

The independent exact-arithmetic check in the accompanying Python script uses odd integer log totals (no equality at half); it evaluates the raw coupled divisor sum and independently compares the reciprocal formulas, including the genuinely negative balanced–balanced triple control. It verifies the algebra and is not a substitute for the analytic fixed-target estimates.

## Comparison

[Arneth’s October paper on a signed Goldbach selector](https://zenodo.org/records/23215269) also distinguishes a central three-factor contribution from other factor patterns, but uses different weights and leaves its signed separation unproved. [Chan’s November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) uses signed terms in a prime-or-semiprime sieve. The result here is the actual same-target reciprocal correction for this coupled weight, not the full signed comparison or a priority claim.
