# An actual finite rough rank window for the bounded-rank detector

Use the notation of the [arbitrary-fixed-rank gate](../all_fixed_ranks/Proof.md), with its smooth coupled base $K_\nu$ (a fixed, nonzero-width smoothing) and its same fixed $\psi,a,C_r$ for the prescribed integer $r\geq3$. Let $0<\eta<1/4$ be fixed and keep only prime tags $P^\eta\leq\ell\leq\sqrt P$ in $M$. Write $D_{r,\eta}=K_\nu-C_r M_\eta$. The squarefree first moment is still $8X\mathfrak S(P)+O_{A,r,\eta,W}(P/\log^A P)$ since the null first-moment result was uniform for bounded tag multipliers. All limits below are for even prescribed targets.

**Theorem.** For each fixed $r$ and $\varepsilon>0$, one can successively choose fixed $\eta>0$, a finite integer $B>r$, and $\sigma>0$ so that
$$
4G+\!\!\!\sum_{\substack{n:\,\mu^2(F)=1,\; r<\omega(F)\leq B\\P^-(F)>P^\sigma}}
           W(n/P)\,(D_{r,\eta}(F))_+
   \ \geq\ (8-\varepsilon-o(1))X\mathfrak S(P).
$$
In particular, the compensating leakage on an unrepresented target would have an actual positive natural-scale contribution in a *fixed finite rank interval* on polynomially rough squarefree inputs. The same detector has total absolute mass $O_{r,\eta,\nu,W}(X\mathfrak S(P))$. No common $B,\sigma$ or implied constant is asserted for the sequence of ranks $r$. This does not estimate the sign in the remaining finite window or prove Goldbach.

**Bounded-rank losses.** Let $t=L^{-1}\log P^-(F)$ and consider squarefree $F$ of rank at most $r$. When the least tag is kept the preceding pointwise domination proof is unchanged. If $t<\eta$, its least-bit absolute bounds, which do not require this tag to be retained, give $|D_{r,\eta}|\ll_r L^2 t^a$. We need an estimate in dyadic $t$ rather than the global $(\log L)^r$ loss. For $0<\tau\leq\eta$ and $\tau/2<t\leq\tau$ fix $z=P^{1/[100(r+1)]}$. We may take $\eta<1/[100(r+1)]$. As before let $b$ denote the full product of primes $\leq z$ dividing $F$, so $\omega(b)\leq r$, $b<P^{.01}$. All its primes are now between $\max(2,P^{\tau/2})$ and $z$. Their reciprocal sum is $\ll_r 1+|\log\tau|$ uniformly, by Mertens when $P^{\tau/2}\geq2$ and by $\log L\ll1+|\log\tau|$ otherwise. On every allowed root class for $b$ use the same one-progression upper sieve, which gives the uniform count
$$
\ll_r \mathfrak S(P)\frac P{L^2}(1+|\log\tau|)^r+O(P^{.35}).
$$
The number of nonempty dyadic bands is $O(\log L)$ since $P^-(F)\geq2$. Taking $\tau=\eta 2^{-j}$ and summing $\tau^a(1+|\log\tau|)^r$ yields
$$
\sum_{\substack{n:\mu^2(F)=1,\ \omega(F)\le r\\ P^-(F)<P^\eta}}
 W(n/P)|D_{r,\eta}(F)|\ll_{r,W}\mathfrak S(P)P\,\eta^a(1+|\log\eta|)^r+o(P).
$$
All constants at this stage are independent of $\eta$: the shape, exponent, correction coefficient and rank count were set first. This tends to zero relative to the reference as $\eta\downarrow0$.

**Actual absolute tail at fixed $\eta$.** Put $L=\log P$ and $u(t,p)=\min(2,|t|\log p/L)$. Fourier inversion for a smooth compactly supported function $f$ gives the exact multiplier $\prod_{p\mid F}(1-e^{it\log p/L})$ for $\sum_{d\mid F}\mu(d)f(\log d/L)$. Extend all one-sided kernels smoothly to compact support on the full real line, matching them on the relevant nonnegative range. For $P^\eta\leq\ell\leq\sqrt P$ the shapes $f(s)=\psi(sL/\log\ell)$ are in a single bounded Schwartz family (constants can depend arbitrarily on $\eta,r$). A row has at most $2/\eta$ such prime tags. For $K_\nu/L^2$ use $f(s)=\int((1+v)\log(F)/L-2s)_+^2\nu(v)\,dv$. The physical variable $\log F/L$ lies in a fixed compact positive interval; smoothness of the fixed density $\nu$ again gives uniform Schwartz extensions, though not for the *sharp* hinge. Taking uniform transform envelopes, for every fixed $N>0$ we obtain
$$
|D_{r,\eta}(F)|\leq C_{N,r,\eta,\nu} L^2
    \int_{\mathbb R}(1+|t|)^{-N}\prod_{p\mid F}u(t,p)\,dt .
$$
There is no independence assumption about the tag count and the other prime factors: in this *upper* bound each allowed shape obeys the very same envelope for that actual $F$.

On the retained squarefree rows $n$ and $P-n$ are coprime, so the prime product above splits exactly into the two legs. We use the [audited primary-source-based two-form estimate, Section 2](https://github.com/mxym/math/commit/9f35592a), specifically the corrected [Henriot Theorem 5](https://doi.org/10.1017/S0305004114000280) with its [basic formulation](https://arxiv.org/abs/1102.1643). For fixed $b\geq1$ and $\theta\in(0,1]$, set $h(p^j)=b2^{1-\theta}u(t,p)^\theta$ for $j\geq1$, extending multiplicatively on coprime factors and setting $h(1)=1$. The result used is
$$
\sum_{n\in[P/3,2P/3]} h(n)h(P-n)
 \ll_{\theta,b}\frac{\mathfrak S(P)P}{L^2}(2+|t|)^{C_{\theta,b}}.
$$
It follows from the corrected raw local sum for the two primitive forms $n,P-n$: root sieve product $\ll\mathfrak S(P)L^{-2}$; nonnegative local-series factor bounded by $1+O_{\theta,b}((u^\theta+u^{2\theta})/p)$ even for primes dividing $P$ (joint prime-power density $\leq p^{-\max(i,j)}$). Chebyshev below $P^{1/(2+|t|)}$ and Mertens above it give $\sum_{p\leq P}u(t,p)^\theta/p\ll_\theta1+\log(2+|t|)$. No extra target-prime factor is inserted. The squarefree/copime restriction can now be discarded on the positive majorant.

With $\theta=1$ the product on squarefree rows of rank $>B$ costs at most $b^{-B}h(n)h(P-n)$ for $b>1$. On a row with a factor $\leq P^\sigma$, take $\theta=1/2,\ b=1$ and extract $(|t|\sigma/2)^{1/2}$ at a smallest prime; other ratios are at most 1. Integrate with $N$ sufficiently large for these two fixed exponents (and for the unrestricted $\theta=b=1$ bound). For example at $b=2$ this proves
$$
\sum_{\substack{n:\ \mu^2(F)=1\\\omega(F)>B\ {\rm or}\ P^-(F)\leq P^\sigma}}
 W(n/P)|D_{r,\eta}(F)|
 \ll_{r,\eta,\nu,W} X\mathfrak S(P)(2^{-B}+\sqrt{\sigma}).
$$
The unrestricted absolute bound follows in the same way. Choose $\eta$ to make the bounded-rank loss $<\varepsilon/3$ of the reference, then $B$ sufficiently large and $\sigma$ sufficiently small to spend another $2\varepsilon/3$. In the positive-mean identity all omitted nonprime terms of rank $\leq r$ are nonpositive apart from the explicitly priced exception. This yields the stated inequality.

**Scope of the narrowing.** The bounds use a single fixed detector after $\eta$ is selected, and their constants need not remain small when $\eta$ decreases. One cannot choose $r=B$ after estimating this tail: the shape and tail constant were set for the original $r$. Consequently the existence of a finite natural-scale leakage gate does not close that gate. This use of the smooth base and a fixed polynomial lower tag scale is important; the same total-variation statement has not been proved here for a literal sharp hinge or the original subpower tag cutoff.

[Chan’s November preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also uses rough-rank windows and small-prime tail estimates, for its prime-or-semiprime sieve. The estimate above is for the absolute tail of the particular signed coupled detector; it does not improve Chan’s representation theorem or supply the pointwise sign that this detector lacks. See [Henriot’s erratum](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B0BD208D979495FE06B8192209E710EA/S0305004114000280a.pdf/nairtenenbaum_uniform_with_respect_to_the_discriminant-erratum.pdf) for the precise local-density correction.
