# A genuinely live fixed-target detector in one shrinking real zero-gap interval

**Conclusions.** Under Dirichlet GRH, a one-sided estimate for a single shrinking interval of genuine same-character zero gaps implies a centrally located prime pair for every sufficiently large even target. The detector compares from below with an actual fixed central prime-pair count, not merely with a positive pole term obtained at inactive arithmetic scales. Under a hypothetical exception its signed zero statistic is negative, but that is not the case for all targets: an elementary unconditional positive calibration gives infinitely many large targets with macroscopic arithmetic response. The required pointwise one-sided estimate is **not proved**. The window radius is of order $\log\log N/\sqrt{\log N}$, optimal up to constants for the specific causal, whole-real-complement, polynomial-leakage, nonvanishing-response requirements below. A signed conductor truncation for this super-polylogarithmic amplifier is in the last section.

We use the fixed-modulus parity projection of [Gou–Wang–Xu, (3.1)](https://arxiv.org/html/2611.18825v1#S3). Their conditional Hardy–Littlewood result assumes a separate primitive ratios conjecture. The estimate sought here is only a signed, single-window inequality. The [continuous shrinking-window calculation](ContinuousRealGapDetector.md) quantifies why simply normalizing a narrower Chebyshev window preserves the pole while losing **all** live arithmetic signal. The pole-null delayed correction below restores it.

## 1. Fixed-target scales

Let $L=\log N$, $\ell=\log L$, $\Phi=\varphi(N)$ for large even $N$. Fix a smooth real nonnegative $f$ supported in $(0.40,0.65)$ and at least 1 on $[0.49,0.58]$; put $b=0.65$, $h=\log(2b)$ and $m(s)=\int f(u)u^{s-1}du$, $m=m(1)$. With $P_\chi(Y)=\sum_{(n,N)=1}\Lambda(n)\chi(n) f(n/Y)$, define
$$T_N(Y)=(Y\Phi)^{-1}\sum_{\chi\bmod N}\chi(-1)|P_\chi(Y)|^2.$$
At all $Y=Ne^{-s}$, $s\ge0$, only $n+n'=N$ can contribute; at $s\ge h$ none can. For all such $Y$, $0\le T_N(Y)\ll_f L^2$, and if there is no prime pair at $N$ the stronger $T_N(Y)\ll_f N^{-1/2}L^2$ holds (at most $O(\sqrt{N})$ eligible proper prime powers can be one operand; the other is then fixed). In fact if no pair lies with **both** normalized arguments in $[1-b,b]$ the same stronger bound holds; any contributing $n,n'$ must be $<bN$. Nonunits are excluded as indicated.

Assume GRH for the primitive conductors dividing $N$, including zeta. For each $\chi$ list the ordinates $\gamma_i$ of its inducing primitive $L$-function with multiplicity. Write $M_i=m(1/2+i\gamma_i)$ and
$$ Z_N(K;I)=\Phi^{-1}\sum_{\chi\bmod N}\chi(-1)
 \sum_{\gamma_i-\gamma_j\in I} e^{iL(\gamma_i-\gamma_j)}M_i\overline{M_j}K(\gamma_i-\gamma_j).$$
The two ordinates in a pair belong to this **same** induced primitive $L$-function. For a finite complex delay measure supported in $[0,S]$, $S\le(1-\eta)L$ with fixed $\eta>0$, let $K(t)=\int e^{-its}d\lambda(s)$. The explicit formula gives
$$\int T_N(Ne^{-s})\,d\lambda(s)=(N/\Phi)m^2K(-i)+Z_N(K;\mathbb R)+O_f(\|\lambda\|_{TV}N^{-\eta/2}L^C).\tag{1}$$
Indeed $Y^{-1/2}P_\chi(Y)=1_{\chi_0}\sqrt{Y}m-\sum_iY^{i\gamma_i}M_i+O_f(Y^{-1/2}L^2)$ for $Y\ge N^\eta$ by Mellin inversion, the functional equation and the removal of primes dividing $N$; $\sum_i|M_i|\ll_f L$. The cross term involving the principal pole after averaging is $O_f(\sqrt NL/\Phi)$. The details and uniform imprimitive corrections are in the linked continuous-window calculation. No symmetry of zeros of one complex character about zero is assumed.

## 2. Constructing a real-gap window that retains prime pairs

Fix $t_0=1$ (in these log-frequency conventions), $c=1/4$, $a=cL$, and a fixed $\tau>h$, say $\tau=1$. Take $w=\sqrt{C}\ell/\sqrt a$ with a sufficiently large fixed $C$ chosen below; put $d=aw^2=C\ell^2$ and $I=[1-w,1+w]$. For $v>0$ let
$$ U_v(t)=e^{-iat}\cos(a\sqrt{(t-t_0)^2-v^2}).$$
This is entire (by the cosine series), is bounded by 1 off its real radius-$v$ window, and is the Fourier transform of $e^{it_0(s-a)}d\mu_v(s)$. Here $\mu_v$ is a positive measure on $[0,2a]$ with
$$ H_v(r)=\int e^{-rs}d\mu_v(s)=e^{-ar}\cosh(a\sqrt{r^2+v^2})\quad(r\ge0).\tag{2}$$
For example the inverse of $\cos(a\sqrt{z^2-v^2})$ is positive on $[-a,a]$ by the Volterra equation $C_a(z)=\cos(az)+v^2\int_0^a [\sin((a-x)z)/z] C_x(z)dx$: convolution preserves positivity, and the successive terms have masses $(av)^{2n}/(2n)!$. Translate by $a$ and modulate to obtain (2). In particular $\|\mu_v\|=\cosh(av)$.

Use a narrower harmless baseline $v_0=D\sqrt{\ell/L}<w$, where $D$ is fixed so that $|U_{v_0}(-i)|\ge L^6$ for all large $N$. This follows from $|\cos(x+iy)|\ge\sinh|y|$ and $|\Im\sqrt{(-i-t_0)^2-v_0^2}|=1+v_0^2/[2(1+t_0^2)]+O(v_0^4)$. Define
$$ K(t)=\frac{U_{v_0}(t)}{U_{v_0}(-i)} + L^{-6} e^{iat_0}U_w(t)(1-e^\tau e^{-i\tau t}).\tag{3}$$
Then $K(-i)=1$. Its inverse measure $\lambda$ is supported in $[0,2a+\tau]\subset[0,0.6L]$ for large $N$, with total variation at most $\exp(O(\sqrt L\,\ell))=N^{o(1)}$. Over **all real** $t\notin I$, $|K(t)|\ll L^{-6}$, so deleting these zero pairs costs $O_f(L^{-4})$ by absolute summation. Equal ordinates, whether from one or distinct repeated indices, are among the discarded gaps for large $N$. The full arithmetic and complementary explicit-formula errors therefore vanish.

The baseline arithmetic output is $o(1)$ for every target, by (2): on $0\le s\le h$ its inverse norm is $\le L^{-6}\exp(rh+av_0^2/(2r))\le L^{-6+o(1)}$, taking $r=\sqrt{av_0^2/(2h)}$; all other scales are inactive. The negative translate in the second term of (3) is also completely inactive, by $\tau>h$. Its unshifted part has real arithmetic response
$$ L^{-6}\int_0^h T_N(Ne^{-s})\cos(t_0s)\,d\mu_w(s)\ge0.\tag{4}$$
Here we used the displayed rotation $e^{iat_0}$ and $\cos(t_0 h)>0$.

**Quantitative comparison at live scales.** Let $J=[0.495,0.505]$, $s_1=0.02$, $s_*=0.04$, $s_2=0.06<h$. For $p/N,q/N\in J$ and $s_1\le s\le s_2$, both $p/Y,q/Y$ fall in $[0.49,0.58]$. Define
$$R_J(N)=N^{-1}\sum_{p+q=N,\;p/N,q/N\in J,\;p\ne q}\log p\log q,$$
with ordered prime pairs. Distinct primes here are units modulo $N$, and $T_N(Ne^{-s})\ge R_J(N)$ throughout this delay interval.

To show these scales have nontrivial mass, tilt $\mu_w$ by $e^{-rs}/H_w(r)$ at $r=\sqrt{d/(2s_*)}$. Its mean equals $-(\log H_w)'=a[1-r\tanh(a\sqrt{r^2+w^2})/\sqrt{r^2+w^2}]=s_*+o(1)$. Its variance is $(\log H_w)''=a w^2(r^2+w^2)^{-3/2}\tanh(a\sqrt{r^2+w^2})+[ar/\sqrt{r^2+w^2}]^2\operatorname{sech}^2(a\sqrt{r^2+w^2})=O(1/\sqrt d)=o(1)$. Consequently the tilted probability of $[s_1,s_2]$ tends to one. As $H_w(r)\ge1/2$ for $r\ge0$, untilting gives $\mu_w([s_1,s_2])\ge (1/3)e^{r s_1}$ for large $N$. Fix $C$ so large that $s_1\sqrt{C/(2s_*)}>8$. Equations (1)–(4) imply, uniformly at large even targets,
$$ \mathcal D_N:=(N/\Phi)m^2+\Re Z_N(K;I)\ \ge L\,R_J(N)-o(1).\tag{5}$$
If $N$ is unrepresented, its uniform proper-power bound, multiplied by $N^{o(1)}$, shows $\mathcal D_N=o(1)$. Equally, if $\mathcal D_N\gg1$ then an actual prime pair in $[1-b,b]N$ exists, not necessarily in $JN$ (the comparison in (5) only goes in one direction).

This last criterion is not vacuous. By the ordinary PNT there are $\gg X/\log X$ primes in $[X,(1.001)X]$. Every ordered pair of distinct such primes yields $N\in[2X,2.002X]$ even with both ratios in $J$ and contributes $\gg (\log X)^2/X$ to $R_J(N)$. Thus some $N$ in each large such block has $R_J(N)\gg1$, so (5) gives $\mathcal D_N\gg\log N$ there. This is a calibration, not an inference about all even targets. The missing one-sided inequality is, for example, $\mathcal D_N\ge\delta$ uniformly for one fixed $\delta>0$. We prove only $\mathcal D_N\ge-o(1)$ for every target. The on-window multiplier may be super-polylogarithmically large; absolute one-character estimates are not a substitute for the missing sign.

## 3. Why a live uniform-complement filter cannot use a thinner scale

For any $K(t)=\int_0^{2a} e^{-ist}\,d\lambda(s)$ with $|K(t)|\le\epsilon$ on the real complement of a radius-$w$ interval, the slit-plane bound yields, for $r>0$,
$$ \sup_x |K(x-ir)|\le\epsilon\,\exp\{a(\sqrt{r^2+w^2}-r)\}\le\epsilon e^{aw^2/(2r)}.\tag{6}$$
In detail, $B(z)=e^{iaz}K(z)$ has centered type $a$ and $|B(z)|\le\|\lambda\|e^{a|\Im z|}$. On the plane slit along the real complement of $I$ write $M(z)=\Re\sqrt{w^2-(z-t_0)^2}$ with positive-real-part branch. For $z=x-ir$, $r\le M(z)\le\sqrt{r^2+w^2}$: $M^2$ is the larger root of $X^2+((x-t_0)^2-r^2-w^2)X-(x-t_0)^2r^2=0$, whose values at $r^2$ and $r^2+w^2$ bracket zero. The bounded holomorphic function $B(z)\exp[-a\sqrt{w^2-(z-t_0)^2}]$ has boundary modulus $\le\epsilon$; the map $z=t_0+w\sin\zeta$ and the strip maximum principle then prove (6).

Extend the smooth scale count on $s\ge0$ to $g_N\in C_c^\infty(\mathbb R)$ supported in $[-1,h]$: multiply the explicit sum for $n+n'=N$ by a fixed smooth cutoff that equals one on $[0,h]$ and vanishes near $-1$ and farther left. The formula itself vanishes at and beyond $h$. Uniformly $|g_N^{(j)}|\ll_f L^2$ for $j=0,1,2$ since there are at most $N$ terms, each weighted by $O_f(L^2/N)$ after differentiating a bounded compactly supported function of $s$. Fourier inversion applied to $e^{rs}g_N(s)$ and the transform of $e^{-rs}\lambda(ds)$, followed by (6), gives
$$\left|\int T_N(Ne^{-s})d\lambda(s)\right|\ll_f L^2(1+r)^2\epsilon \exp(rh+aw^2/(2r)).\tag{7}$$
Here the Fourier $L^1$ norm of the smooth function is bounded by a constant times the sum of the $L^1$ norms of the function and its second derivative. The extension outside $s\ge0$ is used solely to apply Fourier inversion, not to claim unknown negative-delay scale moments. Taking $r=\max(1,\sqrt{aw^2/(2h)})$ shows that when $2a=O(L)$, $\epsilon\ll L^{-A}$ for a fixed $A>2$, and $w=o(\ell/\sqrt L)$, every such detector has $o(1)$ arithmetic output **for all targets**. This conclusion does not require GRH, a bound on $\|\lambda\|$, or any pole normalization. It does require a uniform complementary multiplier bound on the whole real line. The live construction (3) attains this width order.

## 4. Near-full conductors despite super-polylogarithmic amplification

At the level of an individual character the raw bound $O_f(L^2\sup|K|)$ is super-polylogarithmic; consequently a fixed log-power conductor-counting tail alone cannot justify deleting its amplified contribution. Regroup into complete character families before taking absolute values. This section concerns only the nonprincipal part; the explicitly normalized pole is not discarded.

For $m'\mid N$, set $D=N/m'$, $R=\log D$. Let $E_{m'}(s)$ denote the real signed prime-energy sum for all nonprincipal characters modulo $N$ factoring through $m'$, with the same normalization $1/(Y\Phi)$ and same restricted coefficients $(n,N)=1$ as in §1. Then, uniformly on $[0,2a+\tau]$,
$$ |E_{m'}(s)|\ll_f L^{C_1}e^{-\max(s,R)}.\tag{8}$$
For $s\le R+h$, the individual nonprincipal GRH estimate $|P_\chi(Y)|/\sqrt Y\ll_f L$, and $\varphi(m')/\Phi\le e^{-R}N/\Phi$, prove (8), with the harmless factor $e^h$ if $R<s$. For $s>R+h$ the two operands sum to less than $m'$, so the *whole* character family (including its sole principal term) sums to zero exactly by orthogonality on $m'$. The residual nonprincipal contribution is precisely minus $|P_{\chi_0}(Y)|^2/(Y\Phi)$, bounded by $O_f(L^2Y/\Phi)\ll_f L^3 e^{-s}$. The character weights and prime coefficients are identical across all full subfamilies: the $N$-coprimality condition must not be dropped.

For $R\ge d$ use, for $0<r\le1$, $\max(s,R)\ge(1-r)R+rs$. The absolute inverse measure in (3) is bounded by constant multiples of $\mu_w$, $\mu_{v_0}$ and a fixed positive translate of $\mu_w$. Their Laplace transforms are at most $O(1)\exp(d/(2r))$ by (2). Choosing $r=\sqrt{d/(2R)}$ gives
$$\left|\int E_{m'}(s)d\lambda(s)\right|\ll_f L^{C_1}\exp(-R+\sqrt{2dR}).\tag{9}$$
For prime conductors or composite conductors alike no individual zero-gap spacing is assumed.

Möbius inversion writes the aggregate **nonprincipal** energy at a fixed primitive conductor $q\mid N$ as $\sum_{m'\mid q}\mu(q/m')E_{m'}$. Upon summing over $N/q\ge e^{R_0}$, each $D=N/m'$ has $\log D\ge R_0$ and total unsigned multiplicity at most $2^{\omega(D)}$: possible $q/m'$ with nonzero Möbius value are squarefree divisors of $D$. Put $u=(\log\ell)/(4\ell)$ and $R_0=B\ell^4/(\log\ell)^2$. For $B$ sufficiently large in terms of fixed $C$ above, $\sqrt{2dR}\le uR/2$ for all $R\ge R_0$. Therefore the sum of (9) is
$$\ll_f L^{C_1}e^{-uR_0/2}\sum_{D\mid N}2^{\omega(D)} D^{-1+u}=o(L^{-A})\qquad\text{for every fixed }A.\tag{10}$$
Indeed the log of the divisor sum is $\ll\sum_{p\mid N}p^{-1+u}$ by the geometric local factors. For $p\le L^2$, $p^u\le\sqrt\ell$ and the sum of prime reciprocals up to $L^2$ is $O(\log\ell)$; for $p>L^2$ there are at most $L/(2\ell)$ such prime factors, with each factor $O(\sqrt\ell/L^2)$. Hence the log of the sum is $O(\sqrt\ell\log\ell)$, whereas $uR_0\gg\ell^3/\log\ell$. The constants do not require factoring small-prime primitive conductors incorrectly.

Finally transfer (10) to the **actual restricted zero-pair sum**. On the low-conductor nonprincipal subset apply the same uniform explicit formula as in (1), with per-character normalized error $O_f(N^{-0.19}L^{C_1})$ throughout the measure support, and integrate using $\|\lambda\|=N^{o(1)}$. Deleting the real complement of $I$ from this subset costs $O_f(L^{-4})$ by the crude zero count times the uniform multiplier bound, even after restricting the characters. The conductor-one zeta **zero pair**, separate from the pole, costs $O_f(\sup|K|/\Phi)=o(1)$ by (3). Consequently (5) and its missing strictly positive lower bound may use just primitive conductors
$$ q\mid N,\qquad q> N\exp\!\left(-B\frac{(\log\log N)^4}{(\log\log\log N)^2}\right),$$
with absolute $o(1)$ loss and the principal pole still explicit. There is no deduction here of the sharper $(\log\log N)^2/\log\log\log N$ cutoff available for bounded-polylogarithmic, fixed-phase amplifiers by direct conductor counting. The advance here uses exact inactivity of **complete signed subfamilies** to avoid their huge global multiplier norm. This does not control the remaining high-conductor one-sided statistic.

For comparison, [Bhowmik–Grimmelt, v2](https://arxiv.org/html/2607.27282v2) and [Althöfer–Chen–Perelli–Pintz, v1](https://arxiv.org/html/2611.09386v1) study exceptional-set estimates. Bounds for those sets do not imply the pointwise positivity required here. This note does not claim priority for the classical slit-plane argument or the use of parity in fixed-target counts.
