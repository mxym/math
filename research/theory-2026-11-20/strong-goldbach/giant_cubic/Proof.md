# A bank-free giant-cofactor comparison and a bilateral cubic rank tail

There is a whole-opponent lower bound **inside the unmarked cell** of the cubic Goldbach comparison, not just a subcollection known pointwise to have the right sign. On the distinguished side take a composite with a prime factor larger than its square root. No factor condition or sign is imposed on the other side beyond the common roughness and bank exclusion. There is also an exponentially small upper bound on the *absolute* weight involving sufficiently tall ranks, uniform for each prescribed target in the indicated limits. Neither result controls the complementary finite-rank competition well enough to establish Goldbach.

Let $P$ be an even integer, $I=[P/3,2P/3]$, $L=\log P$, $X=|I|\mathfrak S(P)$, with
$$
\mathfrak S(P)=2\prod_{p>2}(1-(p-1)^{-2})\prod_{2<p\mid P}(p-1)/(p-2).
$$
All sums are ordered over $x+y=P$, $x\in I$, $(x,P)=1$. Let $J=J_{3,\theta}$ be the [native cubic composite score](https://github.com/mxym/math/commit/74d3b0e858f37c871ca0ba6d7b732d0bebaf06b9). It vanishes off squarefree $P^{\theta^2}$-rough composites. On true ranks at most three it is exactly $-\log n\sum_{d\mid n}\mu(d)(1-2\log d/\log n)_+^3$. On higher ranks replace the divisor weight by $1-\log d/\log n$ on $d\le P^\theta$ and by zero above $P^{1/2-\theta}$. Fix constants $2<a<b$. Set $s=2\delta$ and let $\mathcal H$ consist of numbers with every prime factor $>P^s$ and none in $(P^{a\delta},P^{b\delta}]$. A *giant composite* has at least two prime factors with multiplicity and $P^+(x)>\sqrt x$.

**Theorem.** In order of limits $P\to\infty$ through even integers, then $\theta\downarrow0$, then $\delta\downarrow0$,
$$
\liminf_{\delta\downarrow0}\liminf_{\theta\downarrow0}\liminf_{P\to\infty}
\frac1X\sum_{\substack{x,y\in\mathcal H\\ x\ {\rm giant\ composite}}}J(x)J(y)
\ \ge\ (6-200/53)\,6\log2=\frac{708}{53}\log2>9.25.                  \tag{1}
$$
This is a *single orientation*. The giant–giant overlap has not been subtracted to obtain a two-orientation result. In the same order, for every $1<c<3/2$ and integer $R\ge1$,
$$
\limsup_{\delta\downarrow0}\limsup_{\theta\downarrow0}\limsup_{P\to\infty}
  \frac1X \sum_{\substack{x,y\in\mathcal H\\ \max(\Omega(x),\Omega(y))>R}}
                 |J(x)J(y)|\ \ll_c\ c^{-R}.                              \tag{2}
$$
The implicit constant in (2) is not a numerical tail certificate for a specified small $R$. For (1), classical sub-root source distribution by itself gives $12\log2$ in place of the displayed constant.

### 1. A genuine bounded-rank source, without a rank approximation

Write $g(v)=(1-2v)_+^3$ for $v\ge0$. On squarefree $x$ put $A(x)=\sum_{d\mid x}\mu(d)g(\log d/\log x)$. If $x=q r_1\cdots r_j$ has a giant prime $q$, set $u_i=\log r_i/\log x$ and $t=\sum_i u_i<1/2$. No subset using $q$ contributes. All remaining subsets lie on a single polynomial segment. Taking its successive finite differences gives
$$
 A(x)=
 \begin{cases}
  6u-12u^2+8u^3,&j=1,\\
  24uv(1-u-v),&j=2,\\
  48uvw,&j=3,\\
  0,&j>3 .
 \end{cases}                                                             \tag{3}
$$
All three nonzero expressions are nonnegative. Define $Q(x)=L A(x)$ on genuine squarefree giant composites in $\mathcal H$, zero elsewhere. Take $\Pi(n)=L1_{n\ \rm prime}$ and $F_0(n)=L1_{\mathcal H}(n)\sum_{d\mid n}\mu(d)g(\log d/L)$. Every sufficiently large central prime lies in $\mathcal H$. In ordered limits the sum on the left of (1) equals
$$
 \langle Q,F_0\rangle-\langle Q,\Pi\rangle+o_*(X).                     \tag{4}
$$
At each fixed $\delta$, when $\theta<s$ the only divisor in the lower patch is $1$. Omitted upper terms have weight $O((\theta+L^{-1})^3)$, the switch from $\log n$ to $L$ costs $O_\delta(1)$ in the unnormalized score, and there are at most $2^{1/s}$ divisors on each squarefree high leg. A dimension-two upper sieve counts $O_\delta(X/L^2)$ doubly rough pairs. Rough nonsquarefree inputs cost $O(P^{1-s}+\sqrt P)$ rows via the square-divisor bound; factors of $P$ above $P^s$ cost $O(P^{1-s}L)$ rows. These estimates allow absolute score replacement on subevents for each fixed $\delta$ before shrinking it. In particular (3) does not assert exact vanishing of the physically cut-off higher-rank score at finite $\theta$.

Let $m_Q=|I|^{-1}\sum_{x\in I,(x,P)=1} Q(x)$. Prime-factor PNT gives, after $P\to\infty$ then $\delta\downarrow0$,
$$
 m_Q\longrightarrow \sum_{j=1}^3\frac1{j!}\int_{u_i>0,\ t<1/2}
                       \frac{A_j(u)\,du}{(1-t)\prod_i u_i}=6\log2.        \tag{5}
$$
Here the giant choice is unique, only the $j$ other distinct primes are unordered. First apply PNT with the fixed positive lower cutoff in each slot and the indicated bank omitted (use Mertens for the $j$ smaller slots, then PNT for $q$); all cut-boundaries have zero limiting measure. Removal of the two shrinking angular holes is dominated convergence, since (3) cancels every denominator $u_i$. The three integrals in order equal $1+2\log2$, $3/2$, $4\log2-5/2$. For the first integrate $-8u+4+2/(1-u)$; the second is $12$ times a triangle of area $1/8$; the third is $4\int_0^{1/2}t^2/(1-t)\,dt$.

### 2. The actual mixed term, including the critical divisors

We prove $\langle Q,F_0\rangle/X=m_Q M_0+o_*(1)$, where $M_0=6+O_{a,b}(\delta)$ is the no-mark cubic multiplier of [the cubic bank calculation, (2)–(4)](https://github.com/mxym/math/commit/88cb4c61). This is a statement about an actual source of genuine prime products, not a factorization postulate for their pair counts.

For clarity, the model is $M_0=E T_s(g(\,\cdot+W))$, where $T_s(f)=e^{-\gamma}s^{-1}\int f(su)(\delta_0(du)+\rho'(u)du)$, $\rho$ is Dickman's function, and $W$ is the nonnegative compound-Poisson shift with intensity $dt/t$ on $[a\delta,b\delta]$. The signed rough-divisor harmonic measure supplies the Dickman factor; quotient bank avoidance supplies $\exp(-\log(b/a))$ and omission of bank primes from the divisor supplies the inverse Euler convolution. Integrating by parts the untruncated cubic gives $T_s(g(\cdot+w))=6(1-2w)^2-24s(1-2w)+36s^2$ up to a factorial-tail error after averaging over $W$: the event of large $W$ or large $s u$ has superpolynomially small cost, as proved there. $E W=(b-a)\delta$.

Put $H=\log(1/s)$ and shorten the opened rough, bank-free divisor $e$ on $y$ to $e\le P^{1/2-Hs}$. Apply a dimension-one upper/lower sieve on $y/e$ to exclude the small primes up to $P^s$ and the bank, omitting target primes. The label $j$ is disjoint from $e$, $j\le P^{Hs/4}$. Test the sign of each $\mu(e)g(\log e/L)$ by opposite endpoints when necessary. The physical progression for the source is $x\equiv P\bmod ej$, with $ej\le P^{1/2-3Hs/4}$, a fixed gap at this $\delta$. The source has maximal reduced-residue Bombieri–Vinogradov with any logarithmic saving on this range. One direct justification: in each of its three exact rank pieces (3), partition the prime slots into independent relative $1+L^{-B}$ boxes and keep the central product interval by endpoint differences or a further fine mesh. The terminal prime is $\ge P^{1/2+o(1)}$ and its complementary product has size at least $P^s$ and at most $P^{1/2+o(1)}$; both are polynomial, with exponents fixed away from 0 and 1 for fixed $s$. The terminal prime slot is Siegel–Walfisz with auxiliary unit masks. For rectangular weights the small-conductor/large-sieve proof is [the tagged Chen comparison, §3](https://github.com/mxym/math/commit/2f9bfe36): at primitive $r\asymp R'$ induced to $kr$, the large-conductor block is
$$ \ll L^{O(1)}k^{-1}\big(P/R'+P^{1-c_s}+\sqrt P\,R'\big). $$
Small conductors use prime Siegel–Walfisz. Arbitrary log savings absorb the number of boxes and fixed divisor weights, by Cauchy and fixed divisor moments. Hard factor or product boundaries can be bracketed by the touching fine rectangles for the **nonnegative source** before each signed sieve sum. Their excess ordinary mass is $O_{s,B}(L^{-B+O(1)})$ after normalization (prime PNT with arbitrary log precision on log-fine multiplicative intervals, then harmonic sums; for the near-tie giant/cofactor use the same endpoint estimate in the giant slot). For smooth weights use upper/lower step envelopes with error $O(L^{-B})$ per profile; $B$ is taken arbitrarily large before the requested BV saving. Coincident prime slots or target prime factors cost a power even with divisor multiplicity, as in §1. These arguments justify the stated estimates also with this particular source rather than requiring distribution of an arbitrary rough sequence.

In the reduced principal conditioned on a true original source $x$ the initial factor is $1_{(e,x)=1}/\varphi(e)$, with local sieve density $1/(p-1)$ at $p\nmid Px$ and zero otherwise. All prime factors of $x$ are $>P^s$, and their number on the source is at most four. Omitting them from the bank and initial harmonic variable changes the normalized absolute model by $o_{P;\delta}(1)$, as does deleting the large target factors; the absence of small target factors is exactly what supplies $\mathfrak S(P)$ in the one-form Mertens product. This is not a model coprimality assumption. The unsigned fundamental-lemma error after summing $e$ is $O_{a,b}(m_Q s^{-2}v^{-v/2})$, $v=Hs/(4b\delta)$, as in the cited model, using $\sum_{e\le\sqrt P,\ P^-(e)>P^s}1/e\ll1/s$. This tends to zero and $m_Q$ stays bounded.

On $P^{1/2-Hs}<e\le\sqrt P$, the cubic costs $O((Hs)^3)$. Write $y=e m$. In the physical absolute error, $Q(x)/L$ is bounded by an absolute constant by (3); but keep the true $P^s$-roughness of $x=P-em$ as well as that of $m$. Uniformly in target-unit rough $e$, the number of these $m$ is
$$ \ll \frac{\mathfrak S(P)P}{e\,s^2L^2}+O(P^{.1+o(1)}). $$
For instance use a dimension-two upper beta sieve with level $P^{.1}$ on these two primitive forms: primes $p\le P^s$ forbid two roots except when they coincide at $p\mid P$; no such prime divides $e$. The dimension bound is uniform for sufficiently small $s$, and the sum of root-count floor errors is $\le P^{.1+o(1)}$. The positive rough harmonic sum $1/e$ over this shoulder is $O(H)$ in limsup as $P\to\infty$ at fixed $s$, from the ordinary rough Buchstab harmonic density at argument $\log e/(sL)$, bounded by 1. Thus the full absolute shoulder costs $O(H^4s)X$; restoration in the positive model costs at most $O(m_Q H^4s^2)X$. No beyond-root prime distribution or assumed asymptotic for semiprime pairs enters.

Finally [angular prime domination, (1)](https://github.com/mxym/math/commit/2fdd6ea0) bounds $\langle Q,\Pi\rangle/X\le(200/53)m_Q+o_{P;\delta}(1)$. It applies **before** shrinking $\delta$, separately at each of three fixed ranks, with minimum exponent $s+o(1)$ and finitely many linear/angular bank and giant cut boundaries; use a slightly smaller compact exponent and smooth upper envelopes exactly as in that proof. The own-log normalization and the macroscopic interval shift cuts by $O(1/L)$ only, on null boundaries. Alternatively a single upper linear sieve at level $P^{1/2-\varepsilon}$ using only the preceding factored-source BV gives $(2/(1/2-\varepsilon))m_Q$, by sieving the reflected number on ordinary primes excluding those dividing $Px$ at $z=P^{.18}$; take $\varepsilon\downarrow0$ after $P\to\infty$. This is an upper on true primality and not an asymptotic. Equations (4)–(5) now give (1).

### 3. Direct control of all tall ranks, at a fixed target

At fixed $\delta$ the absolute score replacement of §1 allows us on both eligible composite legs to use $-L\sum_{d\mid n}\mu(d)g(\log d/L)$. At a prime the score is zero; for an **upper** bound on absolute contributions we can drop this restriction. The bank can also be discarded after this replacement. This step does not send $\delta$ to zero inside a finite-$\theta$ patch.

Extend $g$ from the positive half-line to a compactly supported $C^2$ function on the real line, smooth except for the cubic endpoint, with third derivative of bounded variation (multiply the polynomial extension to negative arguments by a smooth cutoff equal to one near zero). Its Fourier transform for the convention $g(u)=\int \widehat g(t)e^{itu}dt$ satisfies $|\widehat g(t)|\ll(1+|t|)^{-4}$. For squarefree $n$ the divisor transform inside this integral is exactly $\prod_{p\mid n}(1-e^{it\log p/L})$. Fix $c$ as in (2), and weight the first side by $c^{\omega(x)}$. For $v\in\{1,c\}$ let $f_{v,t}$ be multiplicative on squarefree numbers, with
$$
 f_{v,t}(p)=v\,|1-e^{it\log p/L}|\,1_{p\nmid P},\qquad
 f_{v,t}(p^j)=0\quad(j\ge2).
$$
By [Henriot, Theorem 3](https://arxiv.org/pdf/1102.1643) with its [official erratum](https://doi.org/10.1017/S0305004114000280), for the two primitive linear forms $n,P-n$ on $I$,
$$
 \sum_{n\in I} f_{c,t}(n) f_{1,w}(P-n)
 \ll_c \frac{X}{L^2}\exp\!\left(\sum_{p\le P}
                    \frac{f_{c,t}(p)+f_{1,w}(p)}p\right).
$$
Indeed $D=P^2$ is the discriminant of the product and every nontrivial local coefficient at $p\mid D$ vanishes identically due to the target-unit masks. The remaining root product has two roots at $p\nmid P$ and one otherwise; its ratio to $\prod(1-1/p)^2$ is $\ll\mathfrak S(P)$. In the Euler sum away from $D$, each primitive linear form has one root; enlarging to the unrestricted product gives the displayed exponential. Polynomial coefficient norm is $O(P)$ against an interval of length $\asymp P$, so any fixed sufficiently small coefficient-size exponent works. The multiplicative-function class constants are independent of $P,t,w$: the prime values are bounded by $2c$, all higher prime-power values vanish, and the usual $n^\epsilon$ growth bound on squarefree $n$ is uniform at fixed $\epsilon,c$. For the two-variable condition one uses the product of the two multiplicative functions.

For all real $t$, including $|t|>L$, the last prime sum on one leg is $\le 2v\log(2+|t|)+O_v(1)$. Split at $P^{1/(2+|t|)}$; below it use $|t|\log p/L$ and $\sum_{p\le u}\log p/p\ll\log u$, above it use $2$ and Mertens. If the split is below 2, the trivial full prime harmonic sum is already bounded by $\log(2+|t|)+O(1)$ before multiplying by $2v$. Consequently both Fourier absolute integrals converge uniformly, since $2c<3$. Tonelli applied to the nonnegative envelopes proves $L^2\sum c^{\omega(x)}|\sum_{d\mid x}\mu(d)g(\log d/L)\sum_{e\mid y}\mu(e)g(\log e/L)|\ll_c X$ on genuine unit squarefree pairs. Divide by $c^R$ and reverse sides for the other tail. This proves (2), including absolute rather than merely signed error.

At the unmarked high–high scale the full cubic cell still contains the unknown prime-pair term; its formal calibrated main is $G(P)+(24+o(1))X$, by the two separately proved prime and CRT tests in the cubic bank note. The oriented lower (1) cannot be added to that identity. (2) localizes the remaining question to bounded ranks to any fixed accuracy but does not determine their true joint sign. The related earlier quadratic whole-high response in Angular Prime Domination already uses the one-sided true-prime upper sieve; the new content here is the no-mark cubic giant-cofactor comparison, its exact source mass, and the genuinely bilateral absolute rank truncation. No stronger concurrent numerical majorant is used.
