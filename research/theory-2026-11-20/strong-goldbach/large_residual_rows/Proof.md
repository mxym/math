# Conditional fixed-rank-multiplier prime counts in one prescribed class for almost every near-linear modulus

Write $L=\log P$ for one prescribed sufficiently large even integer $P$. Assume a fixed $\Theta<1$ bounds the real parts of the nontrivial zeros of all primitive nonprincipal Dirichlet $L$-functions. We use the [conditional, polylogarithmic-label, full-target bilinear second moment, §§1–3](https://github.com/mxym/math/blob/1b426a35/research/theory-2026-11-20/strong-goldbach/polylog_prime_multiplier/Proof.md), not just the count in §4 of that paper. These are the same external zero assumption and in-repository projected-comparison dependencies as there. [OpenAI, September 30, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) states a zero-free half-plane $\Re s>7/8$ for the full Dirichlet family, which would supply the explicit-formula hypothesis. This paper does not independently verify that external proof.

**Theorem.** Fix $A>0$, $0<\epsilon<1/2$, and a smooth $0\le\eta\le1$ supported in $[1,1.1]$ and positive on some open subinterval. There exist a fixed $K$ and fixed exponents $b_1<\cdots<b_K$ such that the following holds. Let $\mathcal A$ consist of products of one genuine prime $\ell_i\equiv1\bmod4$, $\ell_i\nmid P$, from each $[L^{b_i},L^{2b_i}]$, and put
$$
 Y=L^{3b_K/2+2\sum_{i<K}b_i},\quad H=P/Y,\quad J=[.50H,.54H],
 \qquad M=\sum_{a\in\mathcal A}\eta(a/Y)\asymp_{\mathbf b,\eta} Y/\log Y.
$$
For all but $O_{A,\epsilon,\eta,\Theta}(H L^{-A})$ integers $h\in J$ coprime to $P$, the following genuine weighted prime count has relative error at most $\epsilon$:
$$
 \left|\frac{\displaystyle\sum_{a\in\mathcal A}\eta(a/Y)
                      {\bf1}_{P-ah\ {\rm prime}}}
                   {\displaystyle \mathfrak S(P) h_P(h) M/L}-1\right|
       \le \epsilon,\qquad
 h_P(h)=\prod_{r\mid h}\frac{r-1}{r-2}.                                      \tag{1}
$$
Here $\mathfrak S(P)=2\prod_{r>2}(1-(r-1)^{-2})\prod_{r\mid P,\,r>2}(r-1)/(r-2)$; letters $r$ in Euler products denote primes. All constants, including bank exponents, may depend on the fixed parameters. We do **not** assert arbitrary precision for a single fixed bank. The resulting unweighted set has at least $c\mathfrak S(P)h_P(h)Y/(L\log Y)$ distinct primes in $[.406P,.50P]$ all in the single reduced class $P\bmod h$; $h\asymp P/(\log P)^{O_{A,\epsilon}(1)}$. The rank of every multiplier is exactly $K$.

Two concrete consequences, taking $A>2$: (i) all but $O(H L^{-A})$ of the $\asymp H/L$ prime moduli in $J$ work; (ii) $\gg\mathfrak S(P) H/L^2$ distinct unit $h\in J$ work **with $P-h$ itself prime and $\Omega(h)\le4$** ($\Omega$ counts prime factors with multiplicity). Thus these individual $h$ simultaneously have a genuine prime at the unit multiplier and many *other* distinct genuine primes at the specified $K$-factor multipliers. These are different sets of $h$; no modulus in their intersection is asserted. An aggregate count over pairs $(a,h)$ does not give these simultaneous conclusions. There is no averaging in $P$.

## 1. A squared transfer before testing the residual integer

Put $z=\exp(L^{.24})$, $V(v)=\prod_{r\le v}(1-1/r)$, $R_v(n)={\bf1}_{P^-(n)>v}$ and $n_a=P-ah$. Let $\Lambda_1(n)=(\log n){\bf1}_{n\ {\rm prime}}$. We shall prove, for any preassigned finite $E$, at a suitable bank,
$$
 \sum_{\substack{h\in J\\(h,P)=1}}
 \left|\sum_a\eta(a/Y)
   [\Lambda_1(n_a)-R_w(n_a)/V(w)]\right|^2\ll PY L^{-E},
 \qquad w=L^j.                                                           \tag{2}
$$
Choose $E>A+5$, and $j>E+20$. In the cited polylogarithmic second moment take block precision $E+20$ and cover coefficient exponent $C=2$ and bilinear lengths $\ge P^{.19}$. First fix that precision, then $K$, then the bank exponents as in (2) of the cited proof; enlarge them as necessary so $b_1\gg j+E+100$ and $b_K/j$ exceeds the fixed sieve ratio required by $\epsilon$ in §3 below. Increasing the upper exponents in the stated hierarchical order is allowed; the exponents $E,j$ do not absorb a factor $Y$. Implicit constants may depend on all these fixed choices. In particular $1.1Y<z$ for all sufficiently large $P$.

For a target-unit $h$, $(n_a,P)=1$. Start with $\Lambda(n_a)R_z(n_a)$ and apply Vaughan's identity at $D=P^{1/5}$. The omitted difference from $\Lambda_1$ is supported on proper powers in $[.406P,.50P]$. There are $P^{1/2+o(1)}$ such values per $a$ as a crude bound, and $\#\{a:\eta(a/Y)\ne0\}\ll Y$. By Cauchy its squared row contribution is at most $Y^2P^{1/2+o(1)}=P^{1/2+o(1)}$. The isolated $\Lambda_{\le D}$ vanishes. In the Type II term $\mu_{>D}*(\Lambda_{>D}*1)$ use independent rough and target-unit restrictions on both factors; its second coefficient is bounded by $L$. Partition both positive factor axes into complete intervals of ratio $1.05$, cutting at the original separate Vaughan thresholds as needed. Only boxes meeting $[.406P,.50P]$ in their product matter: each such box has product $\asymp P$ and strictly below $P$ *everywhere*, even off $J$. There is no sharp product cutoff inside a box. Apply the cited second moment on each whole box for this one smooth shell, restrict the squared output to the unit $h$ in $J$, and use the triangle inequality for the $\ell^2$ norm across $O(L^2)$ boxes. The normalization there is the reciprocal bank product $\mathcal V^{-1}=O_K(1)$, with $\mathcal V\asymp_K1$. This proves $O(PY L^{-E-1})$ for the squared Type II contribution. This is the only conditional step.

On the remaining terms write
$$
 T(n)=R_z(n)\sum_{\substack{d\le D^2,\ P^-(d)>z\\(d,P)=1}}
          c_d(n){\bf1}_{d\mid n},\quad
 c_d(n)={\bf1}_{d\le D}\mu(d)\log(n/d)
          -\sum_{\substack{uv=d\\u,v\le D}}\mu(u)\Lambda(v).
$$
On the physical target units this formula is exact. Amend $c_1$ by subtracting $1/V(z)$, writing $\widetilde c$ for the result; all coefficients are $O(L)$ with variation $O(L)$ on the central range, also for products (variation $O(L^2)$). The ordinary *integer-variable* principal is
$$
  \sum_{d\le D^2,\,P^-(d)>z,\,(d,P)=1}\widetilde c_d(n)/d
       =O_B(L^{-B})                                                       \tag{3}
$$
for every fixed $B$, uniformly there. This is the truncated rough Möbius value and derivative at 1 calculated in [the fixed-multiplier proof, §2](https://github.com/mxym/math/blob/b262263b/research/theory-2026-11-20/strong-goldbach/near_full_cofactor/Proof.md): the full series has value zero and negative log moment $1/V(z)$, and truncation at $D$ has arbitrary log savings by the smooth-convolution split for $\mu R_z$. The negative convolution is rectangular in $u,v$; its harmonic sum factors and its $\mu R_z$ sum is negligible. Removing rough primes dividing $P$ costs $O(L^{O(1)}/z)$ by absolute harmonic summation.

Here and below the rough indicators in products may be opened to $k=\lfloor L^{.1}\rfloor$ degrees of squarefree inclusion–exclusion. The aggregate truncation error is smaller than any log saving at the per-pair scale $H$. Details: the remainder is bounded by $\binom{\omega_{\le z}(n_a)}{k+1}$, which vanishes unless $\omega_{\le z}(n_a)\ge k+1$ and is bounded by $\tau(n_a)$. For a fixed $a$ and $h\in J$ one has
$$
 \#\{h:\omega_{\le z}(n_a)\ge k+1\}
 \ll H (C\log L)^{k+1}/(k+1)!+z^{k+1}.
$$
A prime dividing $a$ cannot divide $n_a$, since $(a,P)=1$. Any other squarefree product of $k+1$ small primes specifies at most one class of $h$. Also, for each fixed integer $s$, $\sum_{h\in J}\tau(n_a)^s\ll H L^{O_s(1)}$ uniformly in the bank: majorize $\tau^s$ by $\tau_{2^s}$, choose a largest factor in the convolution, and sum the product $d$ of other factors up to $P^{1-1/2^s}$. For $d\mid n_a$ it is necessary that $(d,a)=1$, and its count is $O(H/d+1)$; the total rounding term $P^{1-1/2^s}L^{O_s(1)}=o(H)$. Hölder handles all products of truncated indicators and short-divisor coefficients (bounded by a fixed divisor power times $L^{O(1)}$) using these two estimates. This argument also applies to all lower cutoffs $w$ used below. In the continuous CRT probability model the same truncated expansions have negligible weighted tails: each small-prime divisor count for one form has Bernoulli probabilities $\le1/r$ after excluding $r\mid P$; its harmonic factorial tails and fixed moments of $2^{\omega_{\le z}}$ suffice, the latter $\ll(\log z)^{O(1)}$ by the Euler product.

Expand the square for $\sum_a\eta(a/Y)[T(n_a)-R_z(n_a)/V(z)]$. For $a=c$ use the divisor moment above: all diagonals sum to $O(P L^{O(1)})$, with an absolute log exponent smaller than $b_1-E$ after enlargement if necessary. For $a\ne c$ keep the full joint small-prime field. On unit $h$, primes dividing $P$ never divide either form. In the two small-prime terms $e_1\mid n_a,\ e_2\mid n_c$ omit those primes; delete also primes of $a$ in $e_1$ and of $c$ in $e_2$. The two congruences are compatible precisely when their prescribed residues agree modulo $(e_1,e_2)$; if compatible the density is $1/[e_1,e_2]$. In particular common roots at primes dividing $a-c$ are included, not treated as independent.

For rough $d_1,d_2$, a common prime $r$ would divide $P(a-c)$; this is impossible since $r>z>1.1Y$, $a\ne c$, and $r\nmid P$. Each $d_i$ is coprime to $a,c$ and to both $e_i$. When $(d_1,d_2)=1$ the two additional congruences therefore have independent density $1/(d_1d_2)$. Enforce $(h,P)=1$ by $\sum_{t\mid(h,P)}\mu(t)$; all four moduli are coprime to $t$. Consequently the principal gets the factor $\phi(P)/P$; each compatible joint congruence, including $t\mid h$, has a floor error $O(1)$, regardless of the size of $t$. Partial summation for the product of log coefficients costs $O(L^2)$ in that error. Summed over $O(Y^2)$ banks pairs, $d_1,d_2\le P^{.4}$, $e_1,e_2\le z^{k+1}$ and $t\mid P$, all floors total $P^{.8+o(1)}$. This treatment does not suppress a large divisor of $P$ by an unproved uniformity.

One can now remove the rough $d$-coprimality constraint **from the model** at negligible cost: its absolute missing harmonic cost is $\ll L^4\sum_{r>z}r^{-2}$, since each multiple of $r$ contributes $O(L/r)$ in an unweighted $d$-harmonic sum and each coefficient is $O(L)$. The absolute double small-modulus factor is at most $\prod_{r\le z}(1+3/r)\ll(\log z)^{O(1)}$, even at common roots. Thus per pair the principal factors inside the integral in $h$ as the true joint small-prime density times the two one-leg expressions (3), with negligible errors. This proves (2) with $z$ instead of $w$. In particular the degree-two use of Vaughan is only for *both short Type I lengths*, never both bilinear terms without the separate conditional estimate.

## 2. Descend to a polylogarithmic presieve without losing the target

We show the squared comparison of $\sum_a\eta(a/Y)R_z(n_a)/V(z)$ and $\sum_a\eta(a/Y)R_w(n_a)/V(w)$ is $\ll PY L^{-E}$. The same joint small-prime inclusion–exclusion with $e_i\le z^{k+1}$ and $t\mid P$ now involves no $d_i$. Restore full local probabilities with the truncation error established above. The two normalized indicators may cost $O(L^2)$ harmlessly. The $a=c$ diagonals cost $O(PL^2)$. For $a\ne c$ compare all four pairs of cutoffs $(v_1,v_2)\in\{w,z\}^2$. In each the contribution of primes $\le w$ (with their true common or distinct roots), the target-unit density, and $V(w)^{-2}$ are **identical**. For $w<r\le z$ divide the probability of avoiding the applicable one or both roots by $(1-1/r)^m$, where $m$ is the number of cutoffs equal to $z$. If $r\nmid P ac(a-c)$ this ratio is 1 for $m=0,1$ and $1+O(r^{-2})$ for $m=2$. At every exceptional prime it is $1+O(1/r)$, including $r\mid P$ where no root constraint remains on target units. Since $\log (P ac|a-c|)=O(L)$, the deviations sum to $O(L/w)$ uniformly. No estimate whatsoever on a pair correlation at the primes $\le w$ was made. The four normalized joint probabilities therefore differ from their common lower-cutoff value by $O(V(w)^{-2}L/w)$ each. In the squared difference that common value cancels. Summing with $O(HY^2)=O(PY)$ and $V(w)^{-2}\ll_j(\log L)^2$ gives the claimed saving. This proves (2).

## 3. Evaluate the short presieve for each individual unit modulus

For $b=\prod_{i<K}\ell_i$ in the earlier banks, put $x=Y/b$. Uniformly $L^{1.5b_K}\le x\le L^{1.5b_K+\sum_{i<K}b_i}$, so the entire fixed-ratio window $[x,1.1x]$ belongs to the last bank for large $P$. PNT in the class 1 modulo 4, with the at most $O(L)$ target prime exclusions, gives
$$
 M=(1+o(1))\sum_b\frac12\int_x^{1.1x}\frac{\eta(u/x)}{\log u}\,du
       \asymp Y/\log Y .
$$
Indeed $\sum_b1/b\to(\log 2/2)^{K-1}$ and $\log x\asymp\log Y$. All these labels exceed $w$.

For fixed $b$ and unit $h\in J$, sift $P-bh\ell$ at $w$ over actual primes $\ell\equiv1\bmod4$ in this same window with the given weight. The even prime and every $r\mid Ph$ impose no exclusion (the labels are units modulo $P$); for odd $r\le w$, $r\nmid Ph$, the prime $\ell$ avoids the one reduced class $P\overline{bh}\bmod r$ among $r-1$. Thus the dimension-one model is
$$
 V_*(P,h;w)=\prod_{\substack{3\le r\le w\\ r\nmid Ph}}\!\!(1-1/(r-1)).
$$
Removing primes $\ell\mid P$ from the initial list can instead be done after sieving with cost $O(L)$ per $b$; no such prime $\ell$ is $\le w$. On the full list before that removal the same small-prime conditions hold. At level $d\le x^{1/4}$, CRT with the class modulo 4 gives one reduced class modulo $4d$ for the forbidden-residue intersection at squarefree $d$ of admissible odd primes. The sum of absolute remainder terms is $O_C(x/(\log x)^C)$ for any fixed $C$ by ordinary maximal-prefix prime Bombieri–Vinogradov at $1.1x$, partial summation for the fixed smooth weight, and $4x^{1/4}<x^{1/2}(\log x)^{-B(C)}$. This is uniform in $b,h,P$; the residue itself may depend on all three. No prime theorem off the ordinary level at the small scale is used. True primes rather than $\Lambda$ are used by partial summation and the usual prime-powers error, which also saves a power at this level.

Apply the dimension-one fundamental lemma, upper and lower, to that actual sequence. Its dimension constant is absolute: the inverse products in any prime interval are bounded by the usual full product for $1/(r-1)$, omitting any primes of $Ph$ only improves that bound. The sieve parameter $\log(x^{1/4})/\log w\ge3b_K/(8j)$ can be chosen sufficiently large so that both relative errors are $<\epsilon/10$ for large $P$, uniformly in $b,h$. Bounded absolute sieve coefficients allow the just-proved BV bound; $x/(\log x)^C+O(L)=o(xV_*/\log x)$. Term by term,
$$
 V_*(P,h;w)/V(w)=(1+O(L/w))\mathfrak S(P)h_P(h).
$$
This includes the factor 2 and the primes of $Ph$ exceeding $w$, whose reciprocal sum is $O(L/w)$. Summing the independent last-prime estimates shows that
$$
 U_w(h):=V(w)^{-1}\sum_a\eta(a/Y) R_w(n_a)
     =(1+O_*(\epsilon/5))\mathfrak S(P)h_P(h)M
$$
for **each** unit $h\in J$, where $O_*(v)$ denotes a quantity of absolute value at most $v$ (enlarge $P$ if needed). No independence of primality in different rows was assumed. The reference $\mathfrak S(P)h_P(h)$ has a positive absolute lower bound. Applying Chebyshev to (2) at threshold $\epsilon\mathfrak S(P)h_P(h)M/3$ gives $O_{\epsilon,\mathbf b,\eta}(H L^{-E}(\log Y)^2)\ll H L^{-A}$ exceptions. On the others we can remove $\log n_a=L+O(1)$ uniformly, since $n_a\in[.406P,.50P]$ and prime contributions are nonnegative. This proves (1).

## 4. A prime at the unit multiplier, on the same moduli

The usual PNT on $J$ gives the first consequence; the at most $O(L)$ primes dividing $P$ are harmless. For the second use the true primes $p_0=P-h$ for $h\in J$ as the initial list. Every such $h$ is automatically a unit since $p_0>P/2$ cannot divide the composite integer $P$. Sift $h$ at $z_0=P^{.24}$, omitting primes $r\mid P$. The density for each other prime $r$ is $1/(r-1)$; on squarefree $d$ made of these primes the progression is $p_0\equiv P\bmod d$. At level $D_0=P^{.49}$ ordinary maximal-prefix BV gives total discrepancy $O_C(P L^{-C})$ in log weights; partial summation supplies ordinary prime counts on the interval $P-J$. Choose $C$ *after* the constant $B=\log Y/\log L$ has been fixed, so this is $o(H/L^2)$ even on the short physical interval. Its initial integral is $(1+o(1))|J|/L$. The dimension-one linear lower sieve has strictly positive coefficient $f(.49/.24)$ since $.49/.24>2$, and
$$
 \prod_{\substack{r\le z_0\\r\nmid P}}(1-1/(r-1))
        \asymp \mathfrak S(P)/L
$$
uniformly by Mertens and the same target-prime tail estimate. Hence $\gg\mathfrak S(P)H/L^2$ such $h$ have no prime factor at most $z_0$. They obey $\Omega(h)\le4$ because $z_0^5=P^{1.20}>h$; repeated factors cause no problem. Removing at most $O(H L^{-A})$ exceptional $h$ proves (ii). Both primes counts are physical; the unit-multiplier partner is near $P$, and the other prime partners are central. This does not imply that $h$ and $P-h$ are both prime.

The classical near-linear Barban–Davenport–Halberstam comparison averages over residue classes as well as moduli (see the primary overview in [Klurman–Mangerel–Teräväinen, §3.1.3](https://doi.org/10.1112/plms.12546)); here the single class is tied to the prescribed macroscopic target. [Maynard’s fixed-residue large-modulus work](https://arxiv.org/abs/2006.06572) obtains unconditional distribution past the square-root in specified modulus ranges, while [his dense-cluster theorem](https://arxiv.org/abs/1405.2593) concerns clusters under distribution hypotheses in a different setting. [Pham Van Khanh, October 30, Theorem 1.1](https://www.preprints.org/manuscript/202610.3061/v1) gives, outside a common exceptional set of targets, a lower bound for actual binary representations with both prime residues prescribed at small fixed-power moduli. Its Appendix A separately treats a mixed prime–rough row average strictly below the square-root scale. Our exceptional integers are moduli, not targets; we test only the selected fixed-rank multipliers in one near-linear reduced class, not two-prime representations for all residue prescriptions. None of these results is used as near-linear distribution at our target; the conditional in-repository input is essential. We make no priority claim. The conclusion is not uniform in *all* residues at any one modulus and is not a proof of binary Goldbach.
