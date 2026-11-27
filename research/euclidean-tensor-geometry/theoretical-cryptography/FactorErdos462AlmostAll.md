# Unconditional concentration at the Erdős–Graham #462 scale

For real $x\ge2$ and $h>0$, let
$$
 W(x,h)=\sum_{\substack{x<n\le x+h\\n\ {\rm composite}}}
                   \frac{P^-(n)}{n},
 \qquad
 \mathcal M(x,h)=\int_x^{x+h}
       \frac{1}{t}\int_2^{\sqrt t}\frac{du}{\log u\log(t/u)}\,dt ,
$$
where $P^-(n)$ is the least prime factor of $n$. We only use $\mathcal M$ for large $x$. The exclusion of primes is essential.

**Theorem (simultaneous local concentration).** Let $X\to\infty$, $L=\log X$, $Z=\sqrt X$. For any fixed $A,B>0$, set $H_-=ZL^{-B}$, $H_+=ZL^B$. Unconditionally,
$$
 \frac1X\int_X^{2X}
 \sup_{H_-\le h\le H_+}
   \left|\frac{ZL^2}{h}\bigl(W(x,h)-\mathcal M(x,h)\bigr)\right|^2\,dx
 \ll_{A,B} L^{-A}.                                      \tag{1}
$$
The same estimate holds with the integral replaced by a sum over integer $X<m\le2X$. In particular, for any fixed $D>0$, for all but $O_{B,D}(XL^{-D})$ of these starting points the relative error $O_{B,D}(L^{-D})$ holds simultaneously for every length in the stated range. The center is comparable to $h/(ZL^2)$ there.

**At the Erdős scale.** For $C>0$ fixed, let $\mu_C(x)=W(x,C\sqrt{x}(\log x)^2)$. For any fixed nonnegative integer $r$, the center has the expansion
$$
 \mathcal M(x,C\sqrt{x}(\log x)^2)
 =4C\left(\sum_{j=0}^{r}\frac{4^j(2j)!}{(\log x)^{2j}}
                         +O_{r,C}((\log x)^{-2r-2})\right).       \tag{2}
$$
The mean square of the difference between $\mu_C$ and the exact integral center is $O_{A,C}(L^{-A})$ for every fixed $A$. In particular,
$$
 \frac1X\sum_{2\le m\le X}(\mu_C(m)-4C)^2
       \sim\frac{(32C)^2}{(\log X)^4}.                       \tag{3}
$$
Thus the leading squared discrepancy from $4C$ is a deterministic second-order bias, not a residual fluctuation of constant scale.

### Relation to the literature

The [original Erdős–Graham question, p. 92](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf#page=88), catalogued as [Erdős Problem 462](https://www.erdosproblems.com/462), asks for a positive lower bound at this scale for **every** sufficiently large starting point. Its literal wording and the preceding composite-only sum should be distinguished. [Xu Zhang, arXiv v2, Theorems 1.3–1.4](https://arxiv.org/abs/2608.24930v2) obtains mean $4C+O_C(1/\log X)$ and the $O_C(1)$ centered second-moment bound for the composite-only sum. Formula (3) replaces the latter upper bound by an asymptotic, and (1) treats many lengths simultaneously without RH. [Adam Henriksson, Theorems 1.1–1.2](https://hexagonmath.org/2611.00808v1) obtains a lower bound at every starting point under RH and a uniform unconditional upper bound; the all-starting-points lower bound and the concentration result are distinct. The unconditional all-starting-points question is not settled by (1).

## 1. Reducing to almost balanced semiprimes uniformly

For a sufficiently large fixed exponent $K$, put $P=ZL^{-K}$ and $U=4ZL^K$. For all $x\in[X,2X]$ and $0<h\ll ZL^B$, each composite with least prime $p\le P$ contributes at most $p/X$. There are at most $h/p+1$ multiples of $p$ in the interval. Hence all these terms together are at most
$$
 \frac{h}{X}\pi(P)+\frac1X\sum_{p\le P}p
 \ll L^{B-K-1}+L^{-2K-1}.                              \tag{4}
$$
If the least prime exceeds $P$, a number with at least three prime factors counted with multiplicity is impossible for large $X$, because $P^3>3X$. Every remaining composite is $pq$ with $P<p\le q\le U$; its weight is $1/q$. The upper bound follows from $pq\le 3X$. There is no need to assume pointwise information about primes in short intervals for (4).

The prime-density model for this sum is the integral of
$du\,dv/(v\log u\log v)$ over $2\le u\le v$, $x<uv\le x+h$. Substituting $t=uv$ gives $\mathcal M(x,h)$. Its portion with $u\le P$ is at most
$$
 O\left(\frac{h}{X\log X}\int_2^P\frac{du}{\log u}\right)
 \ll L^{B-K-2};                                        \tag{5}
$$
indeed $\log(t/u)\gg L$ there and the integral is $O(P/\log P)$. Also any $u>P$ has $v<U$ in the model. The estimates (4)–(5) are uniform in $x,h$.

## 2. Rectangle estimate from two prime factors

Fix $K,B$. Let $I,J\subset(P,U]$ be arbitrary real intervals and let $0\le\delta\le cL^B/Z$ for a fixed constant $c>0$. Denote by $V_{\delta,I,J}(x)$ the sum
$$
 \sum_{\substack{p\in I,\,q\in J\\x<pq\le(1+\delta)x}}q^{-1}
$$
over prime pairs, including equal primes if allowed by the intervals. Let $\widetilde V_{\delta,I,J}(x)$ be the analogous integral with $du\,dv/(v\log u\log v)$. We prove that for every $R>0$,
$$
 \int_0^\infty |V_{\delta,I,J}(x)-\widetilde V_{\delta,I,J}(x)|^2
                               \frac{dx}{x}
 \ll_{R,K,B,c} L^{-R}.                                 \tag{6}
$$

In the logarithm of $x$ the short window is translation by the interval $(0,\log(1+\delta)]$. Define
$$
 \begin{split}
 A_I(t)&=\sum_{p\in I}p^{-it},&
 a_I(t)&=\int_I u^{-it}\frac{du}{\log u},\\
 B_J(t)&=\sum_{q\in J}q^{-1-it},&
 b_J(t)&=\int_J v^{-1-it}\frac{dv}{\log v}.
 \end{split}
$$
Write $k_\delta$ for the indicator of that logarithmic interval. The left side of (6) is, by Plancherel,
$$
 \frac1{2\pi}\int_{\mathbb R} |\widehat k_\delta(t)|^2
           |A_I(t) B_J(t)-a_I(t)b_J(t)|^2\,dt,          \tag{7}
$$
because multiplication of the factors is addition in log coordinates. The sign of the window transform is immaterial in absolute value and
$|\widehat k_\delta(t)|\ll\min(\delta,1/|t|)$.
The transform identity is legitimate for finite measures convolved with the compactly supported $L^2$ window.

For any fixed $D,S>0$, the ordinary prime number theorem with a sufficiently large log saving, followed by partial summation, gives
$$
 |A_I(t)-a_I(t)|\ll_{D,S,K} U L^{-S},
 \qquad |B_J(t)-b_J(t)|\ll_{D,S,K} L^{-S}
 \quad (|t|\le L^D).                                   \tag{8}
$$
To see the uniformity in the endpoints, use $\pi(u)-\operatorname{Li}(u)=O_T(u(\log u)^{-T})$ on $[P,U]$. Partial summation incurs at most a power of $L$ depending on $D,K$ in each of the two weights. Trivially $|A_I|+|a_I|\ll U$ and $|B_J|+|b_J|\ll \log(2U/P)\ll_K L$. Thus (8), the bound $\delta^2U^2\ll L^{2B+2K}$, and a sufficiently large $S$ make the contribution from $|t|\le L^D$ arbitrarily small as a power of $L$.

For any desired $S>0$, the classical Vinogradov–Korobov prime-polynomial estimate gives
$$
           |B_J(t)|+|b_J(t)|\ll_{S,K} L^{-S}
                     \quad (L^D\le |t|\le X^3)          \tag{9}
$$
for sufficiently large $D=D(S)$. For example use the principal-character case of [Pliego–Sun–Wang, Lemma 3.1](https://arxiv.org/abs/2503.02962), with their large parameter $X^3$ and fixed $\theta\in(2/3,1)$. Its lower cutoff $\exp((3L)^\theta)$ is below $P$, upper cutoff $X^3$ is above $U$, and its right side is a sum of $O(L/(1+|t|))$ and a term smaller than any negative power of $L$. Endpoints may be rounded between consecutive integers; replacing a closed by an open endpoint costs at most $O(1/P)$. The same power saving can also be deduced from [Matomäki–Radziwiłł–Shao–Tao–Teräväinen, Lemma 3.2](https://doi.org/10.1007/s00222-026-01408-6) by removing prime powers and partial summation. For $b_J$ integration by parts in $\log v$ gives $O(1/(|t|L))$.

Only an elementary mean value for the other factor is needed. For every interval $\mathcal T$ of length $T\ge1$,
$$
        \int_{\mathcal T}|A_I(t)|^2\,dt
                \ll U(T+U\log(2U)).                    \tag{10}
$$
In fact the diagonal is at most $UT$, and for distinct integers $p,q\le U$, the integrated exponential is $O(1/|\log(p/q)|)=O(U/|p-q|)$. Sum the harmonic series over differences for each $p$. It follows by splitting at $1/\delta$ and dyadic summation beyond it that
$$
 \int_{\mathbb R}\min(\delta^2,t^{-2})|A_I(t)|^2\,dt
                     \ll \delta U+\delta^2 U^2\log(2U)
                     \ll L^{O_{B,K}(1)}.
$$
For $a_I$, Plancherel gives $\int |a_I(t)|^2dt\ll U^2$, since its density in log coordinates is $e^y/y$ on the interval $\log I$. The middle-frequency contribution in (7) is now $O(L^{-R})$ by (9) for $S$ large enough. Beyond $|t|=X^3$, use the trivial bound $B_J\ll_K L$ and (10) on dyadic intervals with the weight $t^{-2}$, giving $O_K(L^2(U/X^3+U^2\log(2U)/X^6))$. The continuous piece there is $O_K(L^2 U^2/X^6)$ by Plancherel. Both are smaller than any negative power of $L$. Combining the three ranges proves (6).

## 3. The ordered pair region and simultaneous lengths

Fix an auxiliary exponent $D_1>0$ and partition $(P,U]$ into intervals with endpoint ratios at most $1+\kappa$, $\kappa=L^{-D_1}$, using a geometric grid. There are $O_{K,D_1}(L^{D_1}\log L)$ intervals. For distinct bins the ordering $p<q$ is equivalent to the order of the bins. The sum over pairs in distinct ordered bins is controlled by (6) and the triangle inequality in $L^2$, since the polynomial number of rectangular errors can be absorbed by increasing $R$.

Pairs in the same bin are bounded above by the positive sum of full same-bin rectangles (including both orders and the diagonal). The continuous total for these rectangles is $O(\kappa L^{B-2})$ uniformly on $[X,2X]$: after setting $t=uv$, the first factor $u$ must lie between $\sqrt t/(1+\kappa)^{1/2}$ and $\sqrt t(1+\kappa)^{1/2}$, of width $O(\kappa Z)$; both logarithms are $\asymp L$. Once again (6) and the triangle inequality control the error of the sum of full same-bin rectangles. This bounds the $L^2$ norm of the omitted discrete part and the omitted continuous part. The argument treats a prime square as a single unordered pair in the discrete sum, without having to subtract it from the model separately.

Combining with (4) and (5), choosing $D_1,K$ sufficiently large, and using $dx/x\asymp dx/X$ on $[X,2X]$, proves for every $F>0$
$$
 \frac1X\int_X^{2X}
  |W(x,\delta x)-\mathcal M(x,\delta x)|^2\,dx
              \ll_{F,B,c} L^{-F}
      \qquad(0\le\delta\le cL^B/Z).                    \tag{11}
$$
The estimates in this deduction depend only on the displayed parameters, not the window.

Take a mesh of $\delta$ values of spacing $Z^{-1}L^{-D_2}$ from zero to just beyond $L^B/Z$, for $D_2>0$ large. It has $O(L^{B+D_2})$ values. The weight density defining the exact center is $O(1/(ZL^2))$ for $t\asymp X$, as follows either by splitting the $u$-integral at $t^{1/4}$, or by the expansion below. The centers therefore change by $O(L^{-D_2-2})$ between adjacent mesh values. Since the discrete weight is nonnegative and the intervals are nested as $\delta$ grows, the absolute error at any $\delta$ is bounded by the maximum of the absolute errors at the mesh values plus $O(L^{-D_2-2})$. The mean square of the maximum is bounded by the sum of the mesh mean squares. Finally $ZL^2/h\le L^{B+2}$ for $h\ge H_-$. Choosing $F,D_2$ sufficiently large proves (1).

For an integer $m$ and $x\in[m,m+1]$, shifting an interval of a fixed length $h$ changes at most a bounded number of integer endpoints. Each composite weight in this range is at most $1/\sqrt n\ll 1/Z$, and the integral changes by $O(1/(ZL^2))$. These bounds hold uniformly in $h$, so integrating over unit cells transfers (1) to the integer sum (discard or handle the one boundary cell, whose contribution is negligible even with the crude bound $W(x,h)\ll h/Z+1/Z$). If the left endpoint of the Erdős–Graham interval is taken closed, its extra composite weight is $O(1/Z)$, also immaterial. The exceptional-set consequence follows from Markov's inequality with $A\ge 3D$ and comparability of the center.

## 4. All-order arithmetic center and the second moment

With $L_t=\log t$ and $u=\sqrt t\,e^{-s}$, the center density is exactly
$$
 \frac1t\int_2^{\sqrt t}\frac{du}{\log u\log(t/u)}
 =\frac4{\sqrt t L_t^2}
     \int_0^{L_t/2-\log 2}\frac{e^{-s}}{1-4s^2/L_t^2}\,ds .       \tag{12}
$$
On $0\le s\le L_t/4$, expand $1/(1-4s^2/L_t^2)$ through degree $r$ in $4s^2/L_t^2$; integration of the remainder costs $O_r(L_t^{-2r-2})$. On the remaining interval the inverse denominator is $O(L_t)$, so its whole contribution is exponentially small in $L_t$. Extending each of the polynomial moments to $s=\infty$ is also negligible and gives $\int_0^\infty e^{-s}s^{2j}\,ds=(2j)!$. This proves comparability and the expansion of the center density. Over $t\in[x,x+C\sqrt x(\log x)^2]$, replacing $t$ by $x$ in each of the finitely many main terms costs a relative $O_{r,C}((\log x)^2/\sqrt x)$; this follows by differentiating the smooth terms. Multiplying by the interval length gives (2).

Choose $B>2$ in (1) and a large $A$, so the quadratic mean of the error from the center contributes $o(L^{-4})$. Equation (2) gives
$\mathcal M(x,C\sqrt x(\log x)^2)-4C=32C/(\log x)^2+O_C((\log x)^{-4})$.
Cauchy–Schwarz bounds its cross term with the distributional error. The dyadic average of $(\mu_C(m)-4C)^2$ is therefore asymptotic to $(32C)^2L^{-4}$. The same asymptotic holds up to $X$: sum dyadic blocks in $X/L^{10}<m\le X$, where all logarithms have ratio $1+o(1)$ to $L$, and use the crude pointwise $\mu_C(m)\ll_C(\log(2m))^2$ for the discarded part. Its contribution is $O_C(L^{-6})$. This proves (3).

The companion verifier checks the exact finite log-window overlap identity, the prime-factor truncation and rectangle/mesh bookkeeping, and the recurrence for the deterministic coefficients. It does not test the analytic estimates.
