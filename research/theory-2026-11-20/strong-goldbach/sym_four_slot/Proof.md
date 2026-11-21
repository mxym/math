# A symmetric four-rough-variable correlation with a near-unit fixed-target reserve

Let $P$ be a prescribed even integer tending to infinity, $I=[P/3,2P/3]$, $X_P=|I|\mathfrak S(P)$ with the usual two-prime singular series, $D=P^{3/10}$, $W=P^{1/50}$. Set $G=\sum_{p\in I,\,p,\,P-p\;\mathrm{prime}}(\log p)\log(P-p)$ and
$$
 T(P)=\sum_{\substack{mn+tb=P,\ mn\in I,\ (mn,P)=1\\
                 m,t>D,\ n,b>W,\ P^-(mntb)>W}}
             \mu(m)\mu(t)(\log n)(\log b).
$$
Then, unconditionally at every sufficiently large even $P$,
$$             |G-T(P)-X_P|<.001X_P.                                  \tag{1} $$
In particular a lower bound $T(P)\ge-.999X_P$ would imply a prime pair at that target. **No such lower bound is proved.** All four slots have polynomial size and are polynomially rough. Both products $mn$ and $tb$ are composite, with at most 49 prime factors each, counted with multiplicity, since they are $<P$. No prime pair appears explicitly in $T$. The only signs are the actual Möbius signs of its two long factors; the other weights are symmetric and nonnegative. Equivalently $T$ is a reflection correlation of $K(x)=\mathbf1_{P^-(x)>W}\sum_{mn=x,\,m>D}\mu(m)\log n$ on target units, **not** a sum of squares.

This is a *new calibration at a different physical roughness*, not a strengthening for the unchanged bulk with cutoff $P^{.001}$. It is literally the sector of the [four-slot determinant](https://github.com/mxym/math/commit/19b9b6ee7b1602538b24364ee544007d0d93a1aa) on which both products are $W$-rough: there $J_{P^{.003}}(n)=\log n$ because every prime dividing $n$ already exceeds $P^{.003}$. The improvement in the allowed debit comes from recalibrating the true primes, not from treating the omitted sectors as pointwise nonnegative.

## 1. Recalibrate the actual prime source

For $x\in I$ define $F(x)=\mathbf1_{P^-(x)>W}\sum_{d|x,\,d\le D}\mu(d)\log(x/d)$. Then $F(x)+K(x)=\mathbf1_{P^-(x)>W}\Lambda(x)$. A cofactor $1$ never contributes to $K$. With a star restricting $x$ and $P-x$ to target units, replacing true primes by von Mangoldt where appropriate costs $P^{1/2+o(1)}$. We may write
$$
 G=S_0+H_W+o(X_P),\quad
 S_0=\sum^*_{p\in I\text{ prime}}(\log p)F(P-p),\quad
 H_W=\sum^*_{p\in I\text{ prime}}(\log p)K(P-p).
$$
Target primes excluded here cost negligibly. Put $V_P(W)=\prod_{r\le W,r\nmid P}(1-1/(r-1))$ over primes. Uniformly in the even target, $V_P(W)\log W/\mathfrak S(P)\to e^{-\gamma_E}$. Define
$$ c=e^{-\gamma_E}\left[35\rho(15)+\int_0^{15}\rho(u)\,du\right],\qquad
 \delta_*=2e^{\gamma_E}\rho(8.9)/9.9 ,                               \tag{2}$$
where $\rho$ is Dickman's function. Then
$$       \limsup|S_0/X_P-c|\le 750\delta_*.                         \tag{3} $$

Indeed open the signed $W$-rough divisor $d\le D$ and the roughness condition on $P-p$, using the two positive dimension-one linear sieves at level $E=P^{.198}$. The sieve uses primes $r\le W$, $r\nmid P$ coprime to $d$, and has $s=\log E/\log W=9.9$. Its relative upper/lower gap is $F_{\rm lin}(s)-f_{\rm lin}(s)=\delta_*$; omitting target primes improves the upper dimension bound. See the [linear-sieve gap derivation](https://github.com/mxym/math/commit/ca6fa82f). One chooses bounds by the sign of $\mu(d)$. Actual progression moduli are $de\le P^{.498}$, with fixed divisor-power multiplicity. Maximal Bombieri–Vinogradov and Cauchy absorb that multiplicity and fixed logarithms with arbitrary log savings before normalization. The complementary absolute progression bound for true prime weights follows already by summing over all integers of that class. Source proper powers can be subtracted in these sums because there is a fixed gap below $P^{1/2}$. Keep the bounded variation part of $\log((P-p)/d)$ by partial summation, or use the positive upper sieve to pay its $O(1)$ variation.

The signed low principal is $V_P(W)|I|$ times the $W$-rough target-unit $\mu(d)/\phi(d)$ sum of $\log P-\log d+O(1)$. In the variable $u=\log d/\log W$ the limiting harmonic measure on $[0,15]$ is $\delta_0+\rho'(u)du$ by the finite distinct-prime expansion and Mertens, as in [the earlier rough inversion](https://github.com/mxym/math/commit/6f877f72). Omitting extra primes $>W$ dividing any integer $\le P^2$ or switching between denominators $d$ and $\phi(d)$ costs $o(1)$ uniformly; for the first assertion there are at most 100 such omitted primes, and the rest of each harmonic product is bounded by a constant. The original target primes $\le W$ are already in $V_P$. Hence the normalized main is $c$. The normalized absolute sieve error is at most $(750+o(1))(\delta_*+o(1))$, since $V_P(W)\log P/\mathfrak S(P)\le 50$ eventually and $\sum_{d\le D}\mu^2(d)\mathbf1_{P^-(d)>W}/\phi(d)\le15+o(1)$ by its Euler upper product. This proves (3).

## 2. Exact source split, with no short-prime subtraction

On $W$-rough source integers $y\in I$ the exact split $\Lambda(y)=F(y)+K(y)$ contains no separate subtractive short-prime term. Equivalently, in the unequal-cut Vaughan formulation take the second cutoff to be $W$ itself: the small $\Lambda$ convolution and the isolated term vanish and $\sum_{k|n,\,k>W}\Lambda(k)=\log n$ on all remaining $W$-rough $n$. Applying the split to $H_W$ gives
$$ H_W=T+M_1+o(X_P),\qquad M_1=\sum^*_{x\in I} K(x)F(P-x). $$
The contribution of non-prime powers in replacing the prime-source definition is zero; proper powers cost $P^{1/2+o(1)}$. All slot and original endpoint constraints in this displayed formula are literal.

For the ordinary Buchstab function $\omega$, put
$$ J=\int_{15}^{49}\rho'(u)(50-u)\omega(50-u)\,du. $$
Then
$$ \limsup |M_1/X_P-cJ|\le 459000\delta_*.                          \tag{4} $$
To check this carefully, open $x=tb$ with $t>D,b>W$, both $W$-rough. The ordinary signed $t,b$ mean weighted by $\mu(t)\log b$ and divided by $|I|$ tends to $J$. The absolute mean has limsup $\le \int_{15}^{49}(50-u)du=612$. For the latter formula, rough positive harmonic $t$ on $u=\log t/\log W\in[15,49]$ has density $\omega(u)du\le du$, via ordinary Buchstab and partial summation. The signed harmonic density there is $\rho'(u)du$. The sum on $b\in I/t$ when its whole interval exceeds $W$ has mean $v\omega(v)+o(1)$ with $v=50-u$, uniformly if $v\ge1+\epsilon$ for fixed $\epsilon>0$. Near $v=1$ the corresponding positive mean is $O(1)$ even if the interval is clipped, by the ordinary upper bound for primes (there are no rough pairs below $W^2$). The affected $t$ harmonics have mass $O(\epsilon)+o(1)$; take $P\to\infty$ then $\epsilon\downarrow0$. Additional unit constraints on $tb$ remove $o(P)$ after these bounded rough divisor weights. These are ordinary integer-factor laws, **not** assumptions about reflected primes.

Open the short $d|P-tb$ in $F(P-x)$ and the free source roughness by the same two positive weights up to $E$, now separating the signs of both $\mu(t)$ and $\mu(d)$. The exact tested progression is $tb\equiv P\pmod{de}$ with $(de,P)=1$, $e$ coprime both to $d$ and $tb$. The two independent slots have lengths $\gg P^{.3}$ and $\gg P^{.02}$. For their true signed-split or unsigned rough coefficients one may invoke the elementary convolution distribution proof [four-slot evaluation §1](https://github.com/mxym/math/commit/19b9b6ee7b1602538b24364ee544007d0d93a1aa), with $Q=P^{.498}$: in its large-conductor bound the term $Q\sqrt P\le P^{.998}$ still has a fixed power saving. The $P/\sqrt T,P/\sqrt B$ terms also do, and the small-nonprincipal-conductor sums are Siegel–Walfisz by fixing all but one prime of an integer with at most 50 factors above $P^{.02}$. The auxiliary unit masks are uniform, removing at most $O(\log P)$ primes for each remaining product. The maximum unit-residue estimate has arbitrary log accuracy after the fixed modulus multiplicities, including for separated subintervals and the true coupled log via the endpoint argument there.

Thus the exact principal retains $(d,Ptb)=1$ and has $1/\phi(e)$ separately. The linear sieve replacement by $V_P(W)$ has relative error at most $\delta_*+o(1)$ against the *absolute* model. The remaining $d$ multiplier, including $\log(P-tb)-\log d$, tends after normalization by $\mathfrak S(P)$ to the same $c$ in (2), uniformly in $tb$ (only primes $>W$ are added to the deletion mask). The error budget from the rough sieve is at most $612\cdot15\cdot50\,\delta_*=459000\delta_*$ in units of $X_P$, using the absolute mean, divisor harmonic mass, and normalized $V_P(W)\log P$ above. No logarithm remains to multiply a fixed error bound. This proves (4).

## 3. Strict explicit margin

Equations (3)–(4) center $(G-T)/X_P$ at $c(1+J)$ with total normalized limsup error $\le459750\delta_*$. Since $\int_0^\infty\rho=e^{\gamma_E}$ and $\rho(j)\le1/j!$, $|c-1|\le37/15!$ and $|c|<2$. By $\rho'\le0$ and $0\le\omega\le1$ one has $|J|\le35\rho(15)\le35/15!$. For an elementary *upper* bound on $\rho(8.9)$ use the integral identity $x\rho(x)=\int_{x-1}^{x}\rho(v)dv$. On mesh $1/32$, set $a_j=1$ for $0\le j\le32$ and $a_j=j^{-1}\sum_{k=j-32}^{j-1}a_k$ subsequently. Monotonicity gives $\rho(j/32)\le a_j$ by induction, hence $\rho(8.9)\le a_{\lfloor32\cdot8.9\rfloor}$. The exact rational checker uses $e^{\gamma_E}<2$ and proves
$$
       459750\delta_*+107/15!<.0005.
$$
This yields (1) with room for the vanishing errors. A large signed determinant may still cancel the entire calibration at a particular target; neither reflection symmetry nor the positivity of the two logarithms forbids that.
