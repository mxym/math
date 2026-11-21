# A supercritical double-divisor range in Pan's Goldbach remainder

**Fixed-target theorem (unconditional).** Write $L=\log N$, $Q=\sqrt N/L^{20}$, $R=N^{17/33-\epsilon_0}$, with $0<\epsilon_0<1/66$ fixed. For every sufficiently large even $N$ and every fixed $A>0$,
\[
 \sum_{1\le n<N}\ \sum_{\substack{b\mid n\\Q<b\le R}}\mu(b)\log b
 \sum_{\substack{d\mid N-n\\Q<d\le R,\ (d,N)=1}}\mu(d)\log d
 =O_{A,\epsilon_0}(N L^{-A}). \tag{1}
\]
There is no averaging in $N$. Both large-divisor cutoffs are imposed simultaneously. The sum is signed; the absolute values of its individual summands are **not** estimated by (1).

**Interpretation.** Removing both upper cutoffs in (1) gives literally $R_3(N)$ in [Huang–Li, introduction, (3)–(6)](https://arxiv.org/html/2005.03811v2#S1), their presentation of Pan's decomposition of the von Mangoldt convolution. Their unconditional formula is $\widetilde r(N)=N\mathfrak S(N)+R_3(N)+O(N/L)$ for even $N$. If $N$ has no two-prime representation, prime-power terms in $\widetilde r(N)$ are $O(\sqrt N L^3)$. Hence the **complement**, where at least one divisor exceeds $R$, would sum to $-N\mathfrak S(N)+O(N/L)$. Neither a sign bound for this complement nor binary Goldbach follows. We do not change $Q$ in the other parts of Pan's identity.

### 1. Preserve the sharp arithmetic cuts

Partition the $b,d$ ranges into dyadic intervals with possible truncated ends, $I_B\subset[B,2B)$, $I_D\subset[D,2D)$. Thus $B,D\gg Q$ and $BD/N\gg L^{-40}$. Replace the physical cutoff $1\le n<N$ by $W(n/N)$, with real $0\le W\le1$ supported compactly in $(0,1)$, equal to one on $[L^{-K},1-L^{-K}]$, and $\|W^{(j)}\|_\infty\ll_j L^{Kj}$. Smoothed and sharp sums, even with any of the restricted sets of divisor pairs here, differ by at most
\[
 L^2\sum_{\min(n,N-n)\le N/L^K}\tau(n)\tau(N-n)\ll N L^{5-K/2}.
\]
Here $1\le n<N$ in the error; Cauchy–Schwarz uses $\sum_{n\le x}\tau(n)^2\ll x\log^3(2x)$ once at $x=N/L^K$ and once at $x=N$. Choose $K>2(A+10)$. No short-interval theorem is required. In particular we do **not** replace $d>Q$ by a restriction on $(N-n)/d$ independent of $n$: the moving endpoint diagnosed by [Moya, August 2026](https://zenodo.org/records/21939906) is never discarded. The literal divisor ranges stay in each sum throughout.

Put $e(x)=\exp(2\pi i x)$ and $\widehat W(y)=\int W(t)e(-ty)\,dt$. Since $(d,N)=1$, simultaneous divisibility implies $(b,d)=1$; no assumption $(b,N)=1$ is needed. With $n=bm$ the remaining condition is $m\equiv N\bar b\pmod d$. Exact Poisson summation gives
\[
 \sum_{m\equiv N\bar b\bmod d} W(bm/N)
 =\frac{N}{bd}\sum_{h\in\mathbb Z}\widehat W(hN/(bd))\,e(hN\bar b/d). \tag{2}
\]
Both signs of $h$ occur.

### 2. Zero frequency

For each interval $I_B$, uniformly in $1\le d\le N$,
\[
 \sum_{b\in I_B,\,(b,d)=1}\frac{\mu(b)\log b}{b}\ll_J L^{-J}\qquad(B\gg Q), \tag{3}
\]
for arbitrary fixed $J$. Indeed use the Dirichlet convolution identity $\mu(\cdot)1_{(\cdot,d)=1}=\mu*1_{\{m:\,p\mid m\Rightarrow p\mid d\}}$. For $m\le\sqrt B$ each inner interval has endpoints of order $B/m\ge\sqrt B$; partial summation of the classical Mertens bound $\sum_{k\le t}\mu(k)\ll_C t(\log t)^{-C}$ saves any specified power of $L$ even with the logarithmic weight. Sum $1/m$ over these $m$ at cost at most $d/\phi(d)\ll\log\log(3N)$. For $m>\sqrt B$ use the trivial harmonic dyadic bound for $k\asymp B/m$ (empty if $m>2B$) and Rankin with $\eta=1/\log\log N$: the remaining harmonic mass is at most $B^{-\eta/2}\prod_{p\mid d}(1-p^{-1+\eta})^{-1}$. For $p\le L$, $p^\eta\le e$; for $p>L$ there are $\le L/\log L$ prime factors and $p^{-1+\eta}\le e/L$. The product is $O((\log L)^{O(1)})$. This proves (3). In (2) the $h=0$ contribution per box is consequently $O_J(N L^{1-J})$, summing $\log d/d$ in one dyadic interval. This is where arithmetic cancellation of the actual coefficients is used.

### 3. Both nonzero-frequency signs at the true target

Use [Bettin–Chandee, *Trilinear forms with Kloosterman fractions*, Theorem 1](https://arxiv.org/pdf/1502.00769). For lengths $B,D,F\ge1$, independent dyadic coefficient sequences $\alpha,\beta,\nu$, and nonzero integral $\theta$, the trilinear sum of $\alpha_b\beta_d\nu_h e(\theta h\bar b/d)$ over $(b,d)=1$ is bounded by
\[
 \ll_\xi \|\alpha\|_2\|\beta\|_2\|\nu\|_2
 (1+|\theta|F/(BD))^{1/2}
 \{(FBD)^{7/20+\xi}(B+D)^{1/4}+(FBD)^{3/8+\xi}[F(B+D)]^{1/8}\}. \tag{4}
\]
In our application $\theta=\pm N$; this is not a fixed-small-shift use of (4). Set $H=BD/N$, dyadize $|h|\asymp F$ and extract $N/(BD)$. The normalized factors $B/b,D/d$ and the cutoffs, logarithms, Möbius signs and $1_{(d,N)=1}$ are single-variable coefficients. The remaining $\widehat W(\pm Nh/(bd))$ separates by one ordinary Mellin inversion: set $z=(h/F)(B/b)(D/d)$ for positive $h=|h|$, insert a fixed bump supported in $(1/8,4)$ and equal to one on $[1/4,2]$, and Mellin-invert the bump times $\widehat W(\pm Fz/H)$. Its transform has $L^1(dt)$ norm $\ll_{j,K} L^{C(j,K)}(1+F/H)^{-j}$, by two integrations by parts in $\log z$ and the Fourier derivative bounds for the smooth $W$. The extra powers of $h,b,d$ have modulus one. Thus (4) applies under the integral with the norm product $\ll L^2\sqrt{BDF}$ and factor $(1+F/H)^{1/2}$.

Sum the dyadic $F$. For $F\le H$ the two terms increase with positive powers of $F$ and the sum is bounded by their values at $F=H$. For $F>H$ take $j$ larger than their degrees plus 2. If $H<1$, then $H\gg L^{-40}$ and replacing $H$ by 1 in growing factors costs at most fixed powers of $L$. Equivalently, for any fixed $\xi'>0$, by choosing the exponent in (4) sufficiently small and absorbing the logarithms, the entire signed nonzero-frequency contribution divided by $N$ is
\[
 \ll_{\xi',K} N^{\xi'}\big[
 H^{17/20}(BD)^{-3/20}(B+D)^{1/4}
 +H\min(B,D)^{-1/8}\big]. \tag{5}
\]
The displayed second term uses $(B+D)/(BD)\asymp1/\min(B,D)$.

Set $u=\log B/\log N$, $v=\log D/\log N$, $s=\max(u,v)$, $t=\min(u,v)$. The powers of $N$ in (5) before $\xi'$ are respectively
\[
 [14(u+v)+5s-17]/20,\qquad [8s+7t-8]/8.
\]
So any dyadic region a **fixed** positive distance below both boundaries $14(u+v)+5s=17$ and $8s+7t=8$ has a power saving in its smoothed nonzero modes. The boundary is one of this estimate, not an impossibility assertion. In the square $u,v\le17/33-\epsilon_0$, both margins are fixed and positive. Sum at most $O(L^2)$ boxes, apply (3) and restore the physical sharp cut. This proves (1). The same proof allows the larger asymmetric region under the two strict inequalities.

### Provenance and limits (checked November 2026)

This is a direct application of a published inverse-fraction estimate to a specified sector of an older decomposition. The Poisson mechanism, the spectral inequality, and the number $17/33$ in other moment/determinant settings are not claimed new. Bettin–Chandee themselves treat determinant equations and cite the corresponding range for twisted zeta moments. [Baier's dissertation, Chapters 1–2](https://webdoc.sub.gwdg.de/ebook/diss/2003/fu-berlin/2001/58/indexe.html) treats Kloosterman refinements of a Pan twin-prime formula and almost-all transfers to Goldbach. Contemporary [TamakoHe's smooth-route notes](https://github.com/TamakoHe/GoldbachResearch/blob/main/notes/smooth-route.md) likewise use signed Poisson blocks; [the twin-prime left-divisor analysis](https://github.com/solveathome/twin-primes/blob/main/research/left-divisor-signs.md) already explicitly prices Bettin–Chandee and Wright in a different signed block. [Wright I](https://arxiv.org/abs/2604.25177) and [Wright II](https://arxiv.org/abs/2608.27732) cover refined settings (a fixed divisor of the modulus or subdyadic supports); their hypotheses are not assumed for the complete cube. The stronger estimate of [Dong–Robles–Zeindler](https://arxiv.org/abs/2601.00292v2) was withdrawn and is not used. No absolute novelty or barrier on the true complementary sum is asserted.
