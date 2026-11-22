# True-prime parity with a subpower-rough reflected partner at a prescribed small-radical target

Fix $B>0$, $0<\gamma\le 3/20$, and a compact interval $J$ of positive length inside $(0,1)$. Let $N$ run through individual even integers with $\operatorname{rad}(N)\le (\log N)^B$. Write $L=\log N$, $w=\exp(L^\gamma)$, and
\[
 E_w(N)=\prod_{\substack{r\le w\ \mathrm{prime},\ r\nmid N}}
                    \left(1-\frac{1}{r-1}\right).
\]
There is $\kappa>0$ such that for $f=\lambda$ or $f=\mu$,
\[
 \sum_{\substack{p\in NJ\ p\ \mathrm{prime},\ P^-(N-p)>w}}
      (\log p)f(N-p)
 \ll_{B,\gamma,J} |J|N E_w(N)L^{-\kappa}.
 \tag{1}
\]
For each $\sigma\in\{-1,1\}$ the corresponding count of true primes with $f(N-p)=\sigma$ is
\[
 \frac{|J|N E_w(N)}{2L}
     \left(1+O_{B,\gamma,J}(L^{-\kappa})\right).
 \tag{2}
\]
Here $\kappa$ may be very small; no zero-free half-plane hypothesis is used, and the threshold may be ineffective. The same asymptotic (without the claimed logarithmic rate) holds in $1\le p<N$ with $|J|=1$. These are statements on the relative scale of the actual rough sample, not the scale of all primes.

In this range the local normalization is
\[
 E_w(N)=(1+o(1))\frac{e^{-\gamma_E}\mathfrak S(N)}{\log w}
       \gg L^{-\gamma},
 \tag{3}
\]
where $\mathfrak S$ is the ordinary binary singular series, with its factor at $2$, and $\gamma_E$ is Euler's constant. Indeed
$E_w(N)/\prod_{r\le w}(1-1/r)$ is exactly its truncated Euler product: the local factor is $(1-1/(r-1))/(1-1/r)$ at $r\nmid N$, and $(1-1/r)^{-1}$ at $r\mid N$. All target primes lie below $w$ for large $N$, and the remaining normalized tail is $1+O(1/w)$.

## 1. Banks, exact coverage, and true-prime density

Use the [full-target reflected comparison](../target_slope_switch/Proof.md) and its [unconditional small-radical major bound](../small_radical_projection/Proof.md), with $z=\exp(L^{.24})$ on the source. For each sufficiently large **fixed** $K$ choose $s=\lfloor \log L/(100K\log 4)\rfloor$ families of $K$ disjoint prime bands. One possible choice of exponents is
\[
 \vartheta_{j\nu}=\frac3{20}+\frac{2\nu-1}{40K}
                        +\frac{j\log4}{\log L}
   \qquad(1\le j\le s,\ 1\le\nu\le K).
\]
The band $\mathcal B_{j\nu}$ consists of primes $r\equiv1\bmod4$ in
$[\exp(L^{\vartheta_{j\nu}}),\exp(2L^{\vartheta_{j\nu}})]$. The logarithmic lower endpoints of successive bands within a color differ by a factor $4$, while the upper endpoint is only twice the lower one on that scale. Different colors have a fixed positive exponent gap even across all families. Within each family the exponent gap is $1/(20K)$ and all exponents are strictly between $.1$ and $.2$. The prime number theorem modulo $4$ gives each reciprocal mass $V_{j\nu}=\sum_{r\in\mathcal B_{j\nu}}1/r$ in $[1/4,1/2]$ for large $N$. Every bank prime exceeds $w$ and is coprime to $N$.

Write $\omega_{j\nu}(y)$ for the number of **distinct** prime factors of $y$ in that band. Put
\[
 U_j(y)=\prod_{\nu=1}^K 1_{\omega_{j\nu}(y)>0},\qquad
 C(y)=1-\prod_{j=1}^s(1-U_j(y)).
 \tag{4}
\]
Thus $C(y)$ is the indicator of at least one eligible family on the actual row, not a weighted divisor count.

For an arbitrary union $\mathcal D$ of selected bands and primes $r\le w$ not dividing $N$, ordinary true-prime Bombieri–Vinogradov gives
\[
 \sum_{\substack{p\in NJ\ p\ \mathrm{prime}}}
    (\log p)1_{r\nmid N-p\ (r\in\mathcal D)}
 = |J|N\prod_{r\in\mathcal D}\left(1-\frac1{r-1}\right)
       +O_A(NL^{-A}).
 \tag{5}
\]
This estimate is uniform in the selected subset. Indeed each omitted prime imposes the one reduced class $p\equiv N\bmod r$. Use upper and lower Bonferroni at successive orders near $b_0=\lfloor L^{.1}\rfloor$. All moduli are squarefree products of at most $b_0+1$ primes bounded by $\exp(2L^{.2})$, hence $\le\exp(O(L^{.3}))=N^{o(1)}$, and each product appears only once in a given truncation. The first omitted reciprocal sum in $1/\varphi(q)$ is at most $(C\log L)^{b_0}/b_0!$, since the sum of reciprocals $1/(r-1)$ is $O(\log L)$. Thus both model brackets approximate the product to arbitrary logarithmic accuracy and the summed prime discrepancy is in the range of ordinary BV. The two endpoints of $NJ$ are common to all moduli. With a von Mangoldt formulation, proper powers summed over these subpower moduli cost $N^{1/2+o(1)}$. Primes $r\le w$ dividing $N$ impose no restriction on the central actual primes, so are not included in $\mathcal D$.

The exact expansion
\[
 1-U_j(y)=\sum_{\emptyset\ne S\subseteq\{1,\ldots,K\}}
           (-1)^{|S|+1}1_{\omega_{j\nu}(y)=0\ (\nu\in S)}
 \tag{6}
\]
gives at most $2^{Ks}=L^{O_K(1)}$ terms when multiplying the failures. Apply (5) termwise with the true rough gate. The main factors exactly because the families and the roughness primes are disjoint. If $M=|J|N E_w(N)$, the total prime log mass of the rough sample is $M+O_A(NL^{-A})$, and its uncovered part is
\[
 M\prod_{j=1}^s
      \left[1-\prod_{\nu=1}^K\left(
          1-\prod_{r\in\mathcal B_{j\nu}}
                        \left(1-\frac1{r-1}\right)\right)\right]
     +O_A(NL^{-A}).
 \tag{7}
\]
The error budget in (5) is enlarged before summing (6). The probability of coverage by one family in the product in (7) is at least
$c_K=(1-e^{-1/4})^K>0$, since $\sum_{r\in\mathcal B_{j\nu}}1/(r-1)\ge 1/4$. Hence the uncovered mass is $O(M L^{-\kappa_0})+O_A(NL^{-A})$ for any fixed $\kappa_0<c_K/(100K\log4)$. This bound is relative to $M$, as required, despite the shrinking density.

## 2. Type II on the exact covered weight

Set $y=N-n$, and start with the actual signed, covered prime sum. Replace the prime weight by $\Lambda(n)1_{P^-(n)>z}$ for $n\in NJ$; this costs $O(N^{1/2+o(1)})$ by the proper powers and $|\lambda(y)C(y)|\le1$. The rough source is a unit at $R=\operatorname{rad}(N)$, and the residual roughness gate implies the same unit condition. Use Vaughan's identity with both short cutoffs $D=N^{1/5}$, in the form
\[
 \Lambda=\mu_{\le D}*\log-\mu_{\le D}*\Lambda_{\le D}*1
        +\Lambda_{\le D}+\mu_{>D}*(\Lambda_{>D}*1).
 \tag{8}
\]
The third term vanishes on $NJ$. In the last term both actual source slots are $z$-rough, are target units, and have polynomial length; the Mobius slot has its true coefficient and the other inner convolution is bounded by $L$. This is exactly the source admissible in the cited small-radical projected estimates.

For this term write the same covered indicator as
$C(y)=\sum_j U_j(y)\prod_{i<j}(1-U_i(y))$. Let $\mathcal A_j$ denote products of one prime from each $\mathcal B_{j\nu}$. On rows squarefree at all bank primes, the factor $U_j(y)$ is exactly
\[
 \sum_{\substack{u\in\mathcal A_j,\u\mid y\\h=y/u}}
       \prod_{\nu=1}^K\frac{1}{1+\omega_{j\nu}(h)} .
 \tag{9}
\]
Indeed every summand has denominator $\prod_\nu\omega_{j\nu}(y)$, and the number of choices is that product. On rows with a repeated bank prime the replacement in (9) is still between zero and one, because each $1+\omega_{j\nu}(h)\ge\omega_{j\nu}(y)$. Moreover the earlier-family switches are unchanged by removing $u$ in either case. Only the first active family can contribute, so the entire replacement is bounded by one. Exceptional rows with $r^2\mid y$ for some bank prime number $\ll N\exp(-cL^{.15})$; by $\sum_{n\ll N}\tau(n)^2\ll NL^3$ and Cauchy, their effect even after the Type II divisor expansion and the log coefficient is smaller than every fixed inverse log power times $N$.

Since all primes of $u$ exceed $w$, removal of $u$ preserves the actual rough mask and changes $\lambda(y)$ to $(-1)^K\lambda(h)$. The earlier-family factors in (9) become exactly the same functions of $h$, as the banks are pairwise disjoint. Thus after extraction, for each family the equation is $N-mn'=uh$, with two genuine bilinear slots and a separate residual
\[
 H_j(h)=\lambda(h)1_{P^-(h)>w}
       \prod_{i<j}(1-U_i(h))\prod_{\nu=1}^K
                        (1+\omega_{j\nu}(h))^{-1}.
\]
Its absolute value is at most one. The small-radical Type II bound is uniform over such residuals. Indeed in a packet with $u\asymp Y$ its normalized square is $O_A(NY L^{-A})$ for arbitrary desired fixed $A$ after choosing $K$ sufficiently large; Cauchy on $h\ll N/Y$ and the reciprocal normalization $\prod_\nu V_{j\nu}\asymp_K1$ give the desired bilinear saving. Sum smooth fixed-ratio tag shells, the $O(\log L)$ families and log-fine source rectangles. For the last subdivision, rows in products crossing the two fixed interval edges number $O(NL^{-F}+1)$ for box width $L^{-F}$; $\tau^2$ and the uniform bound one on the total extracted weight give negligible error for $F$ large, independently of $K$. This is the same sharp product-endpoint treatment as in [the near-full cofactor application](../near_full_cofactor/Proof.md). We obtain $O(NL^{-3})$ for the Type II contribution, by choosing its accuracy and then $K$.

## 3. Type I on the same covered weight, without a nonmultiplicative residual

We first record the ordinary maximal-prefix consequence needed here:
\[
 \sum_{q\le X^{.42}}\max_{(b,q)=1}\max_{t\le X}
 \left|\sum_{v\le t,\ v\equiv b\bmod q}\lambda(v)\right|
      \ll_A X(\log X)^{-A}.
 \tag{10}
\]
Use $\lambda(v)=\sum_{j^2\mid v}\mu(v/j^2)$. For $j\le X^{1/25}$, apply the classical maximal-prefix Möbius BV (Siebert–Wolke, Corollary 1, as stated in [Murty–Vatwani, Proposition 3, p. 115](https://mrammurty-ai.github.io/chowla.pdf#page=5); see also [the classical estimate restated as (3.1)](https://arxiv.org/html/2610.20242v1#S3)) at $X/j^2\ge X^{.92}$, since $.42<.92/2$. The class is reduced and $j$ must be a unit; sum the errors by $\sum_j j^{-2}$. For larger $j$ the total is bounded by summing $X/(q j^2)+1$ over $q\le X^{.42}$ and $X^{1/25}<j\le\sqrt X$, which is $O(X^{.96}\log X+X^{.92})$. No shifted-prime cancellation theorem is an input to (10).

For each of the first two terms in (8), use (6) to expand the **exact same** $C(y)$. Do not attempt to distribute the residual in (9) in arithmetic progressions. Every resulting term is a signed avoidance of a specified set of primes $\mathcal P_y$ on $y$, including all primes $\le w$ from the original rough gate. There are at most $1+2^{Ks}$ such terms with coefficients of absolute value one, counted with multiplicity. Each set lies below $\exp(2L^{.2})$. In the source write $n=d k$ with $d\le N^{.4}$ and $P^-(d)>z$. At fixed $d$, the grouped coefficient has size $O(L)$ by $\sum_{b\mid d}\Lambda(b)=\log d$, and the first term has the smooth extra $\log k=\log((N-y)/d)$. Its supremum and total variation on the fixed central $y$ interval are $O_J(L)$.

Retain the exact mask $(y,R)=1$, with $R=\operatorname{rad}(N)\le L^B$, separately. It enforces the exclusions at primes of $R$ on both $y$ and $k$, since $(d,R)=1$. Open the remaining source roughness on $k$ by truncating inclusion–exclusion at $b_0$ primes $\le z$ coprime to $R$, using squarefree divisors $e$. Then open the remaining residual avoidance on $y$ using squarefree divisors $g$ with at most $b_0$ primes of $\mathcal P_y\setminus\{r:r\mid R\}$. For either opening the pointwise absolute error is bounded by the positive sum with $b_0+1$ factors. For the first opening drop the bounded $y$ weights and count by $N/(de)+O(1)$. For the second, for each retained $d,e$ the actual conditions $de\mid n$ and $g\mid y$ force $(de,g)=1$ since $(de,N)=1$, and give $N/(de g)+O(1)$ by CRT. The retained $e$ reciprocal mass is $L^{O(1)}$, since $\sum_{r\le z}1/r=O(\log L)$. In either error the reciprocal tail is at most $(C\log L)^{b_0+1}/(b_0+1)!$, multiplied by $N L^{O(1)}$. The number of floor errors is at most $N^{.4+o(1)}$, since $e\le\exp(O(L^{.34}))$ and $g\le\exp(O(L^{.3}))$ and each choice occurs at most once per set and cutoff. These give $O_A(NL^{-A})$ for each opened avoidance pattern and any fixed $A$.

In the retained sum put $y=g v$. On $(g,deR)=1$ the exact conditions are
\[
 \lambda(y)=\lambda(g)\lambda(v),\qquad
 v\equiv N\bar g\pmod {de},\qquad (v,R)=1 .
\]
The congruence modulo $de$ is reduced, and $de$ is coprime to $R$. Splitting the unit mask into at most $R$ classes, apply (10) at $X=N/g=N^{1-o(1)}$ and $q=deR\le N^{.4+o(1)}<X^{.42}$. At fixed $g$ the modulus recovers first $de=q/R$ and then $d,e$ uniquely from their opposite prime ranges. The variable $v$ is in the real interval imposed by $n\in NJ$, with the maximal prefix in (10) allowing its endpoints and partial summation for $\log k$. Thus the total at fixed $g$ is $O_A((N/g)L^{-A})$ after increasing the accuracy for $R$ and the log coefficients. Summing $1/g$ over the retained exclusions costs $L^{O(1)}$. Finally charge the $L^{O_K(1)}$ pattern multiplicity from (6) by choosing greater accuracy in (10) and the absolute sieve estimates. This proves $O(NL^{-3})$ for Type I on the exact covered weight. This calculation does not assume a progression theorem for arbitrary first-active functions.

## 4. Unmasking, count, and scope

Combining the same two pieces of Vaughan's identity gives an $O(NL^{-3})$ bound for the true covered prime sum. The actual omitted signed sum is bounded by the **positive** uncovered mass in (7). Choose $0<\kappa<\min(\kappa_0,1/4)$. Since $M\gg_J N L^{-\gamma}$, this proves (1) for $\lambda$. All parameters are fixed in order: required packet log accuracy, $K$, and then $\kappa$ and the auxiliary progression/Bonferroni accuracies, before $N$ grows. On a rough complement, a square factor is $r^2$ with $r>w$ and there are $O(N/w)$ such integer rows. Their true prime log weight is $O(NL/w)$, so replacing $\lambda$ by $\mu$, or asking for squarefree complements in the Liouville conclusion, does not change (1) or (2).

The signed and unsigned weighted statements split the two signs, and $\log p=L+O_J(1)$ on $NJ$ gives (2). To obtain the full interval, trim $p<N^{{1}/{2}}$ first at negligible cost, and then use the unsigned form of (5) on the two endpoint intervals of fixed relative length $\eta$. Its upper bound there is $2\eta N E_w(N)+O_A(NL^{-A})$ in prime log weight; the only new exceptions are primes $p=r$ at a sieving prime dividing $N$, already in the negligible small range. For $p\ge N^{1/2}$ pass to ordinary counts using $\log p\ge L/2$. Let $N$ grow with $\eta$ fixed, then let $\eta\downarrow0$.

The closest comparison is Guo's October 23 v2 *The Möbius function at $N-p$*, whose primary [repository description](https://github.com/aster2024/openai-math-followups) reports rough versions up to $\exp((\log x)^a)$ for fixed $a<1/2$, with assumptions on the fixed-shift argument of Lü–Wang–Wu and on a Dirichlet half-plane or specified target-radical/real-zero conditions. The exact v2 PDF was unavailable in this check, so no comparison of its exact rough-relative error or priority is asserted. The result here has the narrower radical and roughness ranges, uses the separately stated Jiang–Lau–Lü projected minor and unconditional small-radical major inputs, and does not assume the fixed-shift proof of [Lü–Wang–Wu](https://arxiv.org/html/2610.20242v2). The [unrough companion](../small_radical_projection/Parity.md) already treats unmasked true prime--Möbius/Liouville. The [bilateral rough companion](../small_radical_reflected_chowla/BilateralRough.md) has two actual rough integer slots rather than the present true-prime sampling. Neither gives (1) by restricting or rescaling its error. The new argument computes the exact complement of the tag coverage in the true rough prime sample and uses complementary expansions of the same physical coverage for Types I and II.

The result makes no assertion about a fixed-power rough cutoff, a bounded number of factors, or a prime reflected partner. All proved negative rows could still have at least three prime factors. In particular (1) does not control the signed prime-versus-giant-semiprime defect at a fixed positive-power cutoff, or imply binary Goldbach.
