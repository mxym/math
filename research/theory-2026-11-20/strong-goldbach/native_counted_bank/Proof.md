# Counting actual medium prime factors inside a signed Goldbach remainder

For each prescribed sufficiently large even integer, a genuine five-prime source sees a Poisson-shaped signed mass on the opposite composite in the **original quadratic divisor score**. This is not a Poisson law for Goldbach representations. On the full marked population the leading term is positive; in the sector where the other integer has no small prime factor, the leading term vanishes and a strictly negative next-order term is carried by **exactly one** medium prime factor. Both assertions include direct estimates of the whole bulk, not the summation of asymptotics for fixed occupancies.

Let $L=\log P$, $I=[P/3,2P/3]$, $X=|I|\mathfrak S(P)$ with the usual ordered Goldbach singular series $2\prod_{p>2}(1-1/(p-1)^2)\prod_{2<p\mid P}(p-1)/(p-2)$. Put $\langle C,D\rangle=\sum_{x\in I,(x,P)=1}C(x)D(P-x)$. Use the [native quadratic score $J=J_2$](https://github.com/mxym/math/commit/74d3b0e858f37c871ca0ba6d7b732d0bebaf06b9). It is zero on primes, nonsquarefree inputs and integers not rough to $P^{\theta^2}$. On rough squarefree composites use $-(\log y)\sum_{d\mid y}\mu(d)$ times the following weight inside the sum: $1-\log d/\log y$ for $d\le P^\theta$, $g(\log d/\log y)$ for $P^\theta<d\le P^{1/2-\theta}$, and zero beyond, where $g(v)=(1-2v)_+^2$. On genuine rank two replace the patched/truncated weight everywhere by $g$. Write $H=\{P^-(y)>P^{2\theta}\}$, $J_H=J1_H$, and $J_L=J-J_H$ (the subscript here means low least factor).

Let $C(x)=J(x)$ if $x$ is a product of five distinct genuine primes, one with log exponent $\log p/L$ in each of the intervals of half-width $10^{-5}$ centered at
$$
 (.050,.197,.229,.248,.276),
$$
and zero otherwise. This is a nonnegative physical restriction of $J$, not an auxiliary majorant (see below). Put $m_C=|I|^{-1}\sum_{x\in I,(x,P)=1} C(x)$; it tends to a fixed $m>0$. Fix $2<a<b$ and let $N(y)$ be the number of **distinct** prime factors of $y$ in $P^{a\theta}<r\le P^{b\theta}$. Write
$$ h=\log(b/a),\qquad p_k=e^{-h}h^k/k!,\qquad \lambda=(b-a)\theta.$$
An error $O_*(\theta^A)$ means its $\limsup_{P\to\infty,\ P\ {\rm even}}$ in absolute value is $\le c_{A,a,b,k}\theta^A$ for all sufficiently small $\theta>0$, with $k$ absent in whole-bulk assertions. This is an ordered estimate; there is no growing-rank or growing-bank-ratio uniformity.

**Theorem.** For every fixed $A>0$ and integer $k\ge1$,
$$
\begin{aligned}
 \langle C,J_L1_{N=k}\rangle/X
   &=(3-8\theta^2)m_C p_k+O_*(\theta^A),\\
 \langle C,J_H1_{N=k}\rangle/X
   &=-8\lambda m_C1_{k=1}+O_*(\theta^A).
\end{aligned}                                                        \tag{1}
$$
For the whole $N\ge1$ replace $p_k$ in the first line by $1-e^{-h}$ and $1_{k=1}$ in the second by $1$. For the whole $N\ge2$ replace them by $1-e^{-h}(1+h)$ and $0$. These formulas hold separately on the actual signed correlations. In particular the negative $H$ signal has error $o_*(\theta)$, not merely $o_*(1)$. Both orientations need not be added.

For context, the complete no-mark sector at leading precision is
$$
 \langle C,J1_{N=0}\rangle/X=\langle C,\Pi\rangle/X-(4-3e^{-h})m_C+o_*(1),
 \qquad \Pi(y)=L1_{y\ {\rm prime}}.                                    \tag{2}
$$
Here we also use the previously proved bounded-rank whole-source evaluation and genuine prime upper bound (see the final paragraph). For instance at $(a,b)=(3,60)$, (2) is strictly negative for every sufficiently small fixed $\theta$ and all sufficiently large prescribed $P$, whereas the full positive-occupancy sector is strictly positive. The leading mass in (1) belongs to the already known low least-factor channel; it is **not** a new net contribution that can be added to that channel. The occupancy-resolved law and the subleading high-only signal are additional information.

## 1. Genuine source and modulus level

At the central vector $t$ above the ideal alternating quadratic coefficient $\sum_S(-1)^{|S|}g(\sum_{i\in S}t_i)$ is $-19171/125000$. Every subset sum has distance at least $.005$ from $1/2$. On the full box the coefficient moves by at most $32\cdot4\cdot5\cdot10^{-5}$ using Lipschitz continuity on $[0,\infty)$; changing all five denominators from $L$ to $\log x$ adds $O(1/L)$. For sufficiently small fixed $\theta$, only $d=1$ sees the patch and the change at the upper cutoff is identically zero on this source. Thus $C(x)>.14L$ on its support. The five labels are disjoint. Standard iterated prime PNT (four reciprocal-prime sums, then the last prime in the central interval) gives $m_C\to m>0$: the angular integral has density $dt_1\cdots dt_4/\prod_{i=1}^5t_i$, $t_5=1-\sum_{i=1}^4t_i$, on the labelled simplex box, times minus the coefficient. There is no factorial. Its interior has positive four-volume. Dropping $p\mid P$ on the physical source costs $P^{1-.049+o(1)}$, by divisibility and bounded multiplicity.

The required over-root theorem is [Fouvry, *Autour du théorème de Bombieri–Vinogradov II*, Corollaire 1, pp. 617–619](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf). In the convolution $\alpha*\beta$ take the short factor $\ell$ to be the actual prime at exponent $.05+O(10^{-5})$ and the long factor to be the remaining four-prime product. The theorem permits arbitrary order-$K$ long and modulus coefficients, while the short coefficient satisfies (1.3), including the auxiliary unit constraint. For the actual prime on a subinterval this follows from classical prime Siegel–Walfisz for logarithmic moduli using interval differences; at larger moduli use $O(N_0/q+1)$ and $1/\varphi(q)\ll (\log\log(3q))/q$ in the range $q\le N_0$, or the elementary $1/\varphi(q)\ll1/\sqrt q$ beyond that range. Removing prime divisors of the auxiliary mask costs at most its divisor count. Here $N_0$ and $M_0$ are the short and long box bases, $x_0=4M_0N_0$; the theorem is uniform for the **common actual residue** $|P|\le x_0$ and all reduced moduli to $Q$ with $Qx_0^\delta<\min(x_0^{1/2}N_0^{1/2},x_0^{4/7}N_0^{-6/7})$, $N_0\ge x_0^\delta$. Both exponent rails exceed $.5249$ throughout the box, so $Q=P^{.516}$ is admissible with fixed slack. The centered principal is $1_{(x,q)=1}/\varphi(q)$ on the original genuine source, not on uniform integers.

For clarity, use independent relative boxes $1+L^{-B}$ for $\ell$ and its cofactor, with their own lower endpoints $N_0,M_0$. Boxes meeting $I$ satisfy $4M_0N_0\ge(4/3-o(1))P$. The four-prime decomposition of the cofactor is unique on these labelled ranges; all of its fixed-prime interval restrictions stay in the long coefficient. Freezing $\ell$ in the smooth native score leaves an independent divisor-bounded long coefficient after taking out a factor $O(L)$. Ignore the two product boundary boxes' *total endpoint strips* of width $O(P/L^B)$; bounded normalized score variation is $O(L^{-B})$ across the short box. These two physical losses, after all divisor labels, save arbitrary fixed logarithms by Cauchy–Schwarz and fixed divisor moments on $x$ and $P-x$. Model losses have only an additional fixed logarithmic power by the harmonic sum of divisor powers. Choose $B$ first for those losses and then Fouvry's saving for all polylogarithmically many boxes. No over-root distribution of the true prime by itself is assumed.

On physical rough inputs replace own-log normalization by $L$, keeping both physical divisor cuts in place. This costs $O_\theta(1)$ per normalized-log-weighted integer (i.e. the unnormalized $J$ changes by $O_\theta(1)$), as the divisor count there is bounded at fixed $\theta$ for squarefree support. There are $O_\theta(X/L^2)$ relevant pairs by the standard upper dimension-two sieve on $x(P-x)$ using the smaller roughness threshold; the coincident root at primes of $P$ gives the singular factor. This is $o_{P;\theta}(X)$ after a remaining $O(L)$ source weight. Nonsquarefree rough rows cost $P^{1-s+o(1)}+P^{1/2+o(1)}$ at roughness $P^s$, by summing $P/p^2+1$ over $P^s<p\le\sqrt P$; fixed divisor moments per exceptional row may be bounded by $P^{o(1)}$. These errors vanish for every fixed $\theta$, including at the precision in (1).

## 2. Direct transfer of an exclusive occupancy, including zero

Put $w=\theta^2$, $z=2\theta$, and let $\phi(t)=1-t$ on $[0,\theta]$, $g(t)$ on $(\theta,1/2-\theta]$, and $0$ beyond. For $s=w,z$ define
$$ F_s(y)=L1_{P^-(y)>P^s}\sum_{d\mid y}\mu(d)\phi(\log d/L).$$
On $N\ge1$ the opposite integer cannot be prime. If it is a semiprime on our squarefree support it is $rp$ with $r$ in our bank and its other prime above $\sqrt y$ for all sufficiently small $\theta$. Thus neither nontrivial divisor sees a correction: $r$ is strictly beyond the short patch and far below $P^{1/2-\theta}$, and the other proper prime has zero weight both ways. Consequently on all *marked* events the actual $J_H,J_L$ are respectively $-F_z,F_z-F_w$ to the normalization and square errors already paid. This assertion is applied to the difference of events before any model evaluation. In particular we do not use an $O(\theta)$ bound on a no-mark semiprime correction at a putative $o(\theta)$ precision.

Here is the model for $\langle C,F_s1_{N=k}\rangle/X$, valid also for $k=0$. Let $\mathcal B=[a\theta,b\theta]$, $\tau_t f(v)=f(v+t)$, $D_{\bf t}=\prod_{i=1}^k(1-\tau_{t_i})$, and
$$ T_s(f)={e^{-\gamma}\over s}\int_{[0,\infty)} f(sv)\,d\nu(v),
 \qquad d\nu=\delta_0+\rho'(v)\,dv,$$
where $\rho$ is Dickman's function, extended by zero on the negative line. For prime exponents use $d\lambda_0(t)=dt/t$ (distinct from the scalar $\lambda$). Then, to $O_*(\theta^A)$ for every fixed $A$, the model is
$$
 m_C\,{1\over k!}\int_{\mathcal B^k}
   e^{-h}\sum_{j\ge0}{1\over j!}
    \int_{\mathcal B^j}T_s(\tau_{u_1+\cdots+u_j}D_{\bf t}\phi)
                 \prod_{l=1}^j d\lambda_0(u_l)\prod_{i=1}^k d\lambda_0(t_i).
                                                                    \tag{3}
$$
Without any condition on $N$ the model is simply $m_CT_s(\phi)$ to the same precision.

To see this, select an unordered set of $k$ actual distinct bank primes with product $R$ dividing $y$. For $k=0$ select the empty set. The remaining quotient has none of the bank primes. On squarefree rows opening the original divisor sum first over subsets of the selected marks leaves the weight $D_{\bf t}\phi$ on an $e\mid y/R$, where every prime of $e$ is $>P^s$ and outside the bank. Sieve $y/(Re)$ at the primes $\le P^s$ and those in the whole bank, except for the selected primes. A square at a selected prime may be omitted at physical cost $P^{1-a\theta+o(1)}+P^{1/2+o(1)}$, even summing expanded divisors by the pointwise divisor bound. Thus this is an **exclusive** count of the real event, not its factorial moment. Sources are target units; unit-incompatible arithmetic labels can be omitted. For fixed $\theta$ each of the remaining relevant prime squares in the rough physical sum has the negligible cost proved above.

Use ordinary dimension-one upper/lower combinatorial sieve sums for this set at level $P^{.01}$, choosing the direction separately according to the sign of $\mu(e)D_{\bf t}\phi(\log e/L)$; the physical trap uses $C\ge0$. Sieve labels $j'$ are coprime to $Re$ by construction. The true modulus is $Rej'\le P^{kb\theta+.5-\theta+.01}<P^{.516}$ at each fixed $k$ for sufficiently small $\theta$. This estimate includes the **entire** upper shoulder. Regrouping the labels at a modulus gives at most a fixed divisor power multiplicity, for arbitrary signs and all the cutoffs, so the Fouvry estimate in §1 applies also after the sign split. Both enclosures then have the same centered-model main up to a relative dimension-one fundamental-lemma error $O(v_0^{-v_0/2})$ times the unsigned principal, $v_0=.01/(b\theta)$ sufficiently large. The local densities are $1/(p-1)$ except when $p\mid PxRe$, when the label is unavailable; the inverse-product sieve dimension inequality is uniform by deletion, with $2\mid P$. This is just the [usual fundamental lemma, e.g. Theorem 2.2](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/superscars-for-arithmetic-point-scatters-ii/3CCB969E058792C1803466AE0EF29136).

Uniformly in the original source integer $x$, prime Mertens gives the sifted product
$$ (1+o_{P;\theta,k}(1)){e^{-\gamma}\mathfrak S(P)\over sL}\,e^{-h}.$$
Indeed source primes exceed $P^{.049}$, absent target primes above a fixed positive power have reciprocal total $O(L/P^{\min(s,.049)})$, bank exclusions have inverse product tending to $e^h$, and selected-prime local omissions contribute $1+o(1)$. The source-unit restriction on $Re$, and replacing $1/\varphi(Re)$ by $1/(Re)$, cost $o_{P;\theta,k}(1)$ after normalization by marking any omitted prime in the harmonic sums; all such true labels are polynomially rough, and $\sum_{p\mid xP,\ p>P^s}1/p=o(1)$. The unsigned rough harmonic sum for $e$ is $O(1/s)$ and the mark sum $O_k((1+h)^k)$. Including $|D_{\bf t}\phi|\le2^k$ gives a normalized sieve error $O_{k,h}(s^{-2}v_0^{-v_0/2})$ times bounded source mass. It is smaller than any fixed power of $\theta$. All initial finite-target errors are taken at fixed $\theta,k$.

For the full signed rough-divisor harmonic measure the limiting cumulative, in units $sL$, is $\rho(v)$. Indeed expansion by distinct prime factors and Mertens gives the simplex alternating exponential of $dt/t$ on $[1,\infty)$, with the atom of the empty tuple; its cumulative is $1$ on $[0,1]$ and satisfies $v\rho'(v)=-\rho(v-1)$. Removing the bank from this measure cancels its negative convolution-exponential, hence convolves it with the **positive** exponential of $dt/t$ on $\mathcal B$ in unscaled coordinates. This is equivalently the reciprocal Euler factor for every deleted bank prime; repeated labels in the inverse cost a vanishing reciprocal-square tail. On any compact log support these operations can also be checked by multiplying the finite simplex series, since each mark shifts by $\ge a\theta$. The selected-mark unordered integral is $1/k!$ times the ordered one. This gives (3). The retained atom at zero is essential. The unrestricted calculation has no bank sieve or inverse factor.

## 3. Why the high sector selects a single mark

Let $q(v)=(1-2v)^2$ here be the **untruncated polynomial on the whole half-line**. With $d\nu$ as above its constant integral is zero. Integration by parts gives
$$
 T_s(\tau_u q)=4-8u-8s,\quad
 T_s(\tau_u(1-\tau_t)q)=8t,\quad
 T_s(\tau_uD_{\bf t}q)=0\quad(k\ge2).                                  \tag{4}
$$
We used $\int_0^\infty\rho(v)\,dv=e^\gamma$ and $\int_0^\infty v\rho(v)\,dv=e^\gamma$; for the latter integrate $v\rho(v)=\int_{v-1}^v\rho(z)\,dz$. A second finite difference of $q$ is a **constant**, whose signed integral vanishes.

In (3), every nonempty positive shift (either a selected-mark subset shift in $D_{\bf t}$ or an inverse bank mark) is $>\theta$. Replacing $\phi$ there by $q$ in $T_s$ costs less than every power of $\theta$ after all summations. Indeed truncate the number $j$ of inverse marks at $\theta^{-1/2}$: the exponential-series tail, even multiplied by $2^k s^{-1}(1+j^2)$, is superpolynomially small. For retained $j$ the total shift is $\le b\theta(j+k)=O_{b,k}(\sqrt\theta)$. The far discrepancy between the two profiles is supported on $v\gg1/s$ and is $O(1+(sv)^2)$ in the integral; the tail of Dickman's function and of $|d\nu|$ has arbitrarily fast power decay. For instance monotonicity and $v\rho(v)\le\rho(v-1)$ for $v\ge1$ give factorial decay, and $-\rho'(v)=\rho(v-1)/v$ for $v>1$. This pays the explicit $1/s$ prefactor and any fixed powers.

The zero-shift exception contributes
$$
 T_s(\phi-q)=\eta_s+O_A(\theta^A),\qquad
 \eta_w=-3+8w,\qquad \eta_z=0.                                          \tag{5}
$$
For $s=w$ the profile is $1-sv$ up to $v=1/\theta$ so $T_w(\phi)=1$ to this precision. For $s=z$ the patch discrepancy is supported on $0\le v\le1/2$, where the signed measure has only its atom at zero and the two values there coincide. The far tails have just been paid. In (3) this exception is seen **only if $j=0$ and the empty selected-mark subset is used**, with sign $+1$.

The normalized positive shift law $e^{-h}\sum_j (d\lambda_0)^{*j}/j!$ has total mass $1$ and first moment $\int_{\mathcal B}u\,du/u=\lambda$. These are identities of integrals. From (3)–(5), for $k\ge1$ the multiplier of $m_C$ for $F_s1_{N=k}$ is
$$ 8\lambda 1_{k=1}+\eta_s p_k .                                       \tag{6}$$
For $k=0$ the multiplier is $4-8s-8\lambda+e^{-h}\eta_s$, compared with $4-8s+\eta_s$ for unrestricted $F_s$. In particular we evaluated **the no-mark population by sieving out the entire bank**. Subtract from the unrestricted model to obtain $8\lambda+(1-e^{-h})\eta_s$ for all $N\ge1$. Subtract (6) with $k=1$ to obtain the whole $N\ge2$ case. Taking $-F_z$ and $F_z-F_w$ on these same real marked sets proves every assertion of (1), without a uniform-in-$k$ sieve or an interchange with an unknown signed tail.

For (2) the complete source response is $\langle C,J\rangle/X=\langle C,\Pi\rangle/X-m_C+o_*(1)$, from formulas (2)–(3) of *Strict one-sided response to genuine bounded-rank prime-factor profiles* in the same repository (the present source is in its labelled Jordan-integrable class, with an immaterial $O(1)$ own-log normalization on a fixed rough profile). Subtract the *bulk* already evaluated. Applying its (1) gives an upper bound $(-12/53+3e^{-h})m_C+o_*(1)$ in (2). Neither this prime upper bound nor the whole-source rank correction is used for the finer marked-sector formulas (1). For $b/a=20$ the strict gap is $81/1060$ in units of $m_C$. All absolute constants in the numerical data are checked by the accompanying rational script.

**Comparison and limit.** The earlier least-factor law resolves a different observable. Its positive low mass is redistributed here across all positive occupancies. At high least factor, even the leading occupancy law would give zero for every nonempty class; the negative $-8(b-a)\theta$ singleton and the superpolynomial cancellation on the *aggregate* multi-mark sector cannot be read from that leading rectangle law. Classical prime Mertens, the dimension-one sieve, and the Dickman calculus describe the model **after** Fouvry transfers the actual centered progressions. The result is not an assertion that prime factors of reflected prime pairs are independently distributed and does not price the rest of the Goldbach identity from below.
