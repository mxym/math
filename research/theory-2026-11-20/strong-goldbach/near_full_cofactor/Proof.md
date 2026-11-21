# A prime and a subpower multiple of a second prime at a prescribed target

Let $P$ be a sufficiently large **prescribed even integer**. Write $L=\log P$, $H=\log L$, $S=\exp(L^{1/4})$, $I=[P/3,2P/3]$. Put $\lambda(s)=(-1)^{\Omega(s)}$. For each choice of sign count triples of positive integers
$$
 P=p+s q,\qquad p\in I,\quad p,q\text{ prime},\quad q>P/S,\quad\lambda(s)=\pm1 .
$$
The two counts are each
$$ (1+o(1))\,\frac{|I|\log S}{2L^2}.                                      \tag{1}$$
In particular the second genuine prime is $P^{1-o(1)}$. The error is relative to the displayed, *shrinking* density. No claim is made that $s=1$ occurs; its two-prime sieve upper bound is $O(PH/L^2)$ and is negligible on this scale. Nor is there any fixed bound for $\Omega(s)$. There is at most one eligible $q$ for each $p$.

**Precise dependencies.** We use the [full-target projected minor comparison](https://github.com/mxym/math/tree/f22749a7/research/theory-2026-11-20/strong-goldbach), which uses deterministic estimates of [Jiang–Lau–Lü, sections 5–6, v2](https://arxiv.org/html/2611.12467v2), and ordinary Bombieri–Vinogradov. With these inputs the following local version requires no global Riemann hypothesis. There are fixed $A_0,A_1$ such that, fixing any $B_0>0$, (1) holds for every $P$ satisfying:

* for each $d\le L^{A_0}$, each primitive Dirichlet character whose conductor $f>L^{B_0}$ divides $4Pd$ has no nontrivial zero of real part $>1-H^2/L^{1/10}$ and imaginary part $|\gamma|\le L^{A_1}$.

The external fixed zero-free half-plane $\Re s>7/8$ for **all Dirichlet characters** implies this criterion for every sufficiently large $P$. This is exactly the family asserted in [OpenAI, 30 September 2026, Theorem 1.1](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) and its [Dirichlet statement](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean). Thus the every-target assertion uses this external result; it does not require full Dirichlet GRH, nor just RH for zeta. We do not here verify that external proof or the underlying JLL paper. All estimates are uniform in $P$ with these dependencies.

## 1. A truly projected major bound

Use the notation of the linked comparison, with $z=\exp(L^{.24})$, rectangular $m,n$ supports in intervals of relative width at most $.1$, $M,N\ge P^\delta$, $MN\asymp P$, $mn<P$, and both factors $z$-rough, coprime to $P$. Take $\alpha_m=\mu(m)m^{iv}$ on that full interval with just the stated rough/unit restrictions and $|v|\le L^C$; $\beta_n$ can be arbitrary with $|\beta_n|\le L^C$. Each of the $K$ tag sets is the **full** set of primes $p\equiv1\bmod4$, $p\nmid P$, in $[\exp(L^{\vartheta_i}),\exp(2L^{\vartheta_i})]$, with the separation/gap conditions of the comparison. For any prescribed fixed $R$ and its sufficiently large fixed $K$, the mean square $Q$ of that comparison satisfies
$$ Q\ll_R PY L^{-R}.                                                     \tag{2}$$
The constants $A_0,A_1$ in the local criterion may depend on the requested accuracy and fixed box/coefficient budgets. Only a single fixed accuracy is needed for (1).

Here are details on the actual $P$-congruence. Write an arc $\theta=b/d+\xi$, $|\xi|\le2 L^{A_0}/Y$, $d\le L^{A_0}$. The variables $a,c,m,n,r,s'$ of the double sum are all units modulo $Pd$ (all prime factors exceed $d$ and none divide $P$). Write $k=cmn-ars'$, split $t=ars'\pmod d$ among the units, and in $G=(\mathbb Z/Pd)^\times$ let $H_0=\ker(G\to(\mathbb Z/P)^\times)$. For $u=cmn/(ars')$ in $G$ the exact factor at rational frequency is
$$
 {\bf1}_{P\mid k}e_d(bk/P)={\bf1}_{H_0}(u)e_d(bt(u-1)/P).
$$
The right side is interpreted only on $H_0$, where $(u-1)/P\bmod d$ is well defined. Its multiplicative Fourier coefficients have absolute value at most $1/\phi(P)$, since reduction is onto. This includes $(P,d)>1$. The condition on $t$ and $e_d(b(a-c))$ split into characters on the unit group modulo $d$ with total cost at most a fixed power of $d$. Thus the two independent groups of variables carry $\chi,\bar\chi$ modulo $Pd$ and possibly additional $d$-characters on individual variables.

The residual real multiplier is
$$
 \psi((cmn-ars')/(PY))\,e\{\xi[c(mn/P-1)-a(rs'/P-1)]\}.
$$
On the six normalized log variables in their compact boxes its derivatives of every fixed order $j$ are $O_j((1+L^{A_0})^j)$. Insert fixed smooth bounding boxes equal to one on the original supports. Fourier separation has total transform $L^{O(A_0+1)}$ in $L^1$ (use any fixed order $>6$). Truncation to $|\mathbf v|\le L^{C_1}$ gives arbitrary $L^{-D}$ uniform error by increasing $C_1$ and the integration-by-parts order. Do this **before** expanding the rational factor: on $P\mid k$, fixing $a,c$ and $mn$ permits $O(1)$ values of $rs'$ and conversely. Hence the projected absolute total is $O(PY^2 L^{O(C+1)})$ by Cauchy and $\sum_{l\ll P}\tau(l)^2\ll PL^3$. This error after arc measure is negligible. Individual coordinate powers after separation change only polynomial times in Dirichlet polynomials.

For characters $\chi$ whose conductor does not divide ${\rm lcm}(4,d)$, both $\chi\chi_d$ and $\chi\chi_d\chi_4$ are nonprincipal for every $d$-twist. Either tag sum has bound $O_D(YL^{-D})$. Indeed hold $K-1$ full tag primes fixed with product $A$. The last prime is in a subinterval of $[Y/A,1.1Y/A]$, cut by its full tag interval; $\log(Y/A)\ge L^{.1}-O(1)$ for any nonempty interval. Each primitive twist above has prime sum $\ll_D (Y/A)L^{-D}$ on it, uniformly in prefixes, even after smoothed $\eta$ and polynomial times (by partial summation). Imprimitive omissions cost $O(L)$ primes; reciprocal weights of the other factors sum to $O_K(1)$.

Specifically, with an external fixed zero-free half-plane $\Re\rho\le\Theta<1$ in the Dirichlet family, the ordinary truncated explicit formula at height $\asymp x$, for $x\asymp Y/A$ at half-integer endpoints, gives $\sum_{n\le x}\Lambda(n)\omega(n)\ll_\Theta x^\Theta\log^{O(1)}(2fx)$ for primitive nonprincipal $\omega$. Functional equation bounds real parts away from zero as well. Here $\log(2fx)=O(L)$, whereas $x\ge \exp(L^{.1})/O(1)$. For the local version, $f\le L^{B_0}$ uses Siegel–Walfisz, since $\log x\gg L^{.1}$. At greater conductors truncate at a good height $T\asymp L^{A_1}/2$. In differences across subintervals of $[Y/A,1.1Y/A]$ the constant term cancels. The standard truncation error is $O(x\log^{O(1)}(2fxT)/T+\log^{O(1)}(2fxT))$ at half-integer endpoints; equivalently smooth endpoint margins of width $xL^{-D'}$ can be used. By the local criterion including conjugate characters, $\Re\rho\ge H^2/L^{.1}$ for zeros up to that height. Their reciprocal-modulus sum is $O(L^4)$ by the unit-interval zero count. Their total endpoint contribution is $O(xe^{-(1-o(1))H^2}L^4)$. Take $A_1$ large after the other fixed losses. Partial summation removes $\log p$ and pays any polynomial twists; prime powers are negligible. These are standard explicit-formula and zero-count estimates (Davenport, *Multiplicative Number Theory*, chs. 14, 19–20).

Write $B_\chi=\sum_{m,n}\alpha'_m\beta'_n\chi(mn)$ for either pair of separated endpoint factors, including its own times and low twists. By orthogonality and the divisor-square estimate,
$$ \phi(P)^{-1}\sum_{\chi\bmod Pd}|B_\chi|^2\ll dP L^{O(C+1)},$$
since $mn$ is supported on length $O(P)$ and $\phi(Pd)/\phi(P)\le d$. This spends the actual coefficient $1/\phi(P)$. The high-conductor sum saves every fixed log power after the two tag bounds and Cauchy on the two $B_\chi$'s.

There are at most $4d$ remaining characters, with conductor dividing ${\rm lcm}(4,d)$. For them $B_\chi=O_D(PL^{-D})$ from its *Möbius* factor, not from an arbitrary bounded input. Additional $d$-twists still have small conductor. For the primitive small-modulus twist use $\mu{\bf1}_{P^->z}=\mu*{\bf1}_{P^+\le z}$, small-modulus Möbius Siegel–Walfisz on the free sum for smooth $j\le\sqrt M$, and $\sum_{j:\,P^+(j)\le z}1/j\ll\log z$. Larger smooth $j$ have reciprocal mass $\ll(\log z)^{O(1)}\exp(-\log M/(2\log z))$ by Rankin at $1/\log z$. Missing target primes $>z$ in the rough sum cost $O(L(M/z+1))$; the others never occur. Partial summation pays polynomial times. Tags here have the trivial $O_K(Y)$ bound. Since $P/\phi(P)\ll H$, the low modes also save every fixed log power after the rational coefficient. Multiply by the major-arc measure $\ll L^{3A_0}/Y$ and the polynomial separation losses. This proves the major bound; the previously proved minor comparison gives (2).

## 2. Exact residual and the Type I calculation

Use either $b(s)=1$ or $b(s)=\lambda(s)$. Put
$$ F_b(m)=\sum_{\substack{m=sq,\ q>P/S\ {\rm prime}\\(s,P)=1}} b(s)\log q/L \qquad(1\le m\le P).$$
It is bounded by one. For $a$ a tag product, $F_b(ah)=b(a)F_b(h)$ whenever $ah\le P$: all prime factors of $a$ are far below $P/S$ and $(a,P)=1$. The scalar $b(a)$ is constant within each family. No coprimality of $a$ with $h$ is needed. On actual prime rows $p=P-sq\in I$, the unit restriction on $s$ omits at most the primes $p\mid P$, and $q\mid P$ likewise contributes $O(SL)$ triples (weights here are harmless). Let $W_j(s)$ be the product of the $K$ tag divisor counts divided by their reciprocal masses, for the $j$th set of disjoint separated families, and $\bar W=J^{-1}\sum_j W_j$, $J\asymp_K H$. Such a grid with full tag intervals is [JLL (2.1)–(2.5)](https://arxiv.org/html/2611.12467v2#S2); deleting divisors of $P$ costs $O(L\exp(-L^{.1}))$ in reciprocal mass. Since $q$ is too large to be a tag, $W_j(P-p)=W_j(s)$ exactly.

In $\sum_{n\in I}\Lambda(n)F_b(P-n)W_j(P-n)$ insert the $z$-rough and target-unit restrictions on $n$. Except for prime divisors of $P$ or proper prime powers these cost nothing. The possible discarded contribution is $O(P^{1/2+o(1)})$ since for fixed $K$ divisor weights pointwise are $P^{o(1)}$. Take $D=P^{1/5}$ and expand
$$ \Lambda=\mu_{\le D}*\log-\mu_{\le D}*\Lambda_{\le D}*1+\Lambda_{\le D}
                   +\mu_{>D}*(\Lambda_{>D}*1).                         \tag{3}$$
The first two are Type I; the third vanishes. In the last put the Möbius factor in one slot and the remaining convolution in the other; its coefficients are $\le L$, and both slot lengths are $\ge D/O(1)$. The independent rough/unit masks are exact. Extract the tags from $P-mn$ and apply (2) shellwise by Cauchy on $h$ (there are $O(P/Y)$ choices). A smooth partition into fixed-ratio $a$ shells costs $O_K(L)$, with uniform derivatives in $a/Y$. Type II thus contributes $O(PL^{-3})$ by fixing sufficiently high accuracy in (2). For the sharp $mn\in I$ use log-mesh boxes of relative width $L^{-B}$ for fixed large $B$. Boundary products lie in $O(PL^{-B})$ integers. Their total mixed divisor/tag weight is bounded by Hölder, losing only an absolute power of $L$ and replacing $L^{-B}$ by $L^{-B/2}$: use $\sum_{l\ll P}\tau(l)^4\ll P L^{15}$ and $\sum_{0<l<P}W_j(P-l)^4\ll_K P$. For the latter expand at most $4K$ prime labels, group repeated labels and count ordinary multiples of their lcm. Each lcm is $\exp(O_K(L^{.2}))$, individual reciprocal tag masses are bounded, and the sum of all rounding errors is $P^{o(1)}$. Thus $B$ and the needed precision can be chosen independently of $K$ **before** choosing $K$, avoiding a circular cutoff.

For Type I open the actual $P-n=sq$, $q>P/S$, with $s\le S$, $(s,P)=1$. Then $n$ is automatically a target unit when $q\nmid P$; the exceptional $q\mid P$ carry a negligible $P^{o(1)}$ after all physical divisor weights. The short divisor $d$ in (3) is $z$-rough; in the negative term it is the product of the two separately truncated factors. Open the remaining $z$-rough mask on $n/d$ by inclusion–exclusion over squarefree $e$ with primes $\le z$, stopped at $k=\lfloor L^{.1}\rfloor$. The absolute pointwise remainder is bounded by the positive sum at $k+1$ factors. Then $de\le P^{.4+o(1)}$; $(e,d)=1$, and $d,e$ are uniquely recovered from $de$. At fixed $s$ no $de$ sharing any prime with $Ps$ contributes except in the discarded $q\mid P$ case. The true progression on $q$ is therefore the reduced class $P\bar s\bmod de$. Use ordinary **maximal-prefix** Bombieri–Vinogradov at $x=P/s=P^{1-o(1)}$. Variation of $\log(n/d)$ over $I$ costs $O(L)$, the negative coefficient at fixed $d$ is bounded by $\sum_{b'|d}\Lambda(b')\le L$, and $\sum_{s\le S}W_j(s)/s\ll_K L^{O_K(1)}$. Replacing each true prime sum weighted by $\log q$ by its integral divided by $\phi(de)$ costs $O_A(PL^{-A})$ in total, for any fixed $A$. Proper powers in BV cost $O(x^{1/2}P^{.4+o(1)})$ per $s$ at worst, summably negligible. The same BV applies to the nonnegative remainder: its principal $e$-sum is at most $(O(H))^{k+1}/(k+1)!$, superlogarithmically small; the same controls the tail in completing the Euler product. In this argument, after restricting to the reduced classes, reintroducing a possible $q\mid P$ harmlessly costs $P^{o(1)}$ summed with actual divisor multiplicities. The effect of the $e$ mask is the factor
$$ V(Ps;z)=\prod_{\substack{r\le z,\ r\text{ prime}\\ r\nmid Ps}}
                         (1-1/(r-1))$$
up to arbitrary fixed log saving. The even prime always divides $P$.

In the remaining $d$ weights, $\phi(d)^{-1}=d^{-1}(1+O(L/z))$ since $d$ is rough, and exclusions from primes dividing $sP$ cost only $O(L^{O(1)}/z)$ in the absolute harmonic sums: each such prime is $>z$, there are $O(L)$ of them, and divisor coefficients cost only log powers. Let $\mu_z=\mu{\bf1}_{P^->z}$ and $V_0(z)=\prod_{r\le z}(1-1/r)$ over primes. Uniformly for $n\in I$ the remaining Type I density is
$$
 \sum_{d\le D}\frac{\mu_z(d)}d\log(n/d)
 -\bigg(\sum_{a\le D}\frac{\mu_z(a)}a\bigg)
  \bigg(\sum_{b'\le D,\ P^-(b')>z}\frac{\Lambda(b')}{b'}\bigg)
 =V_0(z)^{-1}+O_A(L^{-A}).
$$
Indeed $\sum_{d\ge1}\mu_z(d)d^{-1-u}=\zeta(1+u)^{-1}\prod_{r\le z}(1-r^{-1-u})^{-1}$ has value $0$ and derivative $V_0(z)^{-1}$ at $u=0$. Partial summation allows truncation of both series at $D$ with $O_A(L^{-A})$: for every $x\ge D$ use the earlier smooth convolution split at $\sqrt x$, the classical Mertens bound on the free factor and the Rankin bound on its smooth cofactor. The resulting relative error $\ll(\log z)^{O(1)}(\exp(-c\sqrt{\log x})+\exp(-\log x/(2\log z)))$ is integrable against $dx(1+\log x)/x$ beyond $D$ with arbitrary log saving. The rectangular truncation in the second Type I term is essential here.

Define the binary singular series $\mathfrak S(P)=2\prod_{r>2}(1-(r-1)^{-2})\prod_{r|P,\ r>2}(r-1)/(r-2)$ over primes. Define $h_P(s)=\prod_{r|s}(r-1)/(r-2)$ for $(s,P)=1$ and zero otherwise. On target units $V(Ps;z)/V_0(z)=\mathfrak S(P)h_P(s)(1+O(L/z))$ by multiplying individual local factors; primes $>z$ dividing $sP$ have summed reciprocal $O(L/z)$. With $T(n)=S(P-n)/P\in[S/3,2S/3]$ the Jacobian $dq=|dn|/s$ yields the **literal weighted sum**
$$
 \frac{\mathfrak S(P)}L\int_I
       \sum_{s<T(n)}\frac{b(s)h_P(s) W_j(s)}s\,dn+O(PL^{-3}).      \tag{4}
$$
This is a principal computation per $s$ only in Type I. We have **not** approximated the actual two-prime count for any prescribed $s$.

## 3. The harmonic measure and removal at the correct, smaller scale

Write $h_P=1*g$ with $g$ squarefree supported and multiplicative: $g(r)=-1$ for $r\mid P$, $g(r)=1/(r-2)$ otherwise. Then
$$ A(P)=\sum_d g(d)/d=\mathfrak S(P)^{-1}.                            \tag{5}$$
Indeed at $r\nmid P$ the factor $1+1/(r(r-2))$ inverts $1-1/(r-1)^2$; at $r\mid P$ the factor $1-1/r$ inverts the singular local factor $r/(r-1)$. Uniformly $\sum|g(d)|/d\ll H$ and $\sum |g(d)|\log d/d\ll H^2$: the absolute Euler product is bounded by $O(\prod_{r|P}(1+1/r))$ and its logarithmic derivative costs $O(1+\sum_{r|P}(\log r)/r)=O(H)$ by splitting at $L^2$. In particular $A(P)\gg1/H$. Convolving the ordinary harmonic sum gives, uniformly in $T\ge2$,
$$
 \sum_{s<T}h_P(s)/s=A(P)\log T+O(H^2),\qquad
 \left|\sum_{s<T}\lambda(s)h_P(s)/s\right|\ll H.                     \tag{6}
$$
For the first bound absorb the main tail using $\log T\le\log d$ at $d\ge T$. For the second use complete multiplicativity of Liouville, the convolution, and the bounded partial sums of $\sum\lambda(n)/n$ (e.g. $\lambda=\mu*{\bf1}_{\rm squares}$ and the prime number theorem with its classical error).

For a squarefree tag union $a$ from at most $2K$ labels, each a target unit above $\exp(L^{.1})$, uniform on $h_P(t)\ne0$ is $h_P(at)/h_P(t)=1+O_K(e^{-L^{.1}})$, without assuming $(a,t)=1$. Moreover $\log a\ll_K L^{.2}$. Thus (6) applies also with $a\mid s$ by $s=at$, replacing $T$ by $T/a$, inserting $1/a$ and, in the signed case, $\lambda(a)$. For $T\in[S/3,S]$ the unsigned answer is $A(P)(\log S)/a$ with relative error
$$ E\ll_K (L^{.2}+H^3)/\log S=o(1).$$
The signed answer is $O_K(H/a)$, the exponentially small perturbation absorbed. For each $j$ we have exactly $\sum_{a\in\mathcal A_j}1/a=\mathcal V_j$. Consequently the normalized first moment of $W_j$ under the unsigned measure equals $1+O(E)$; the same is true for $W_iW_j$ at $i\ne j$ because the grids have disjoint primes. The diagonal moment is $O_K(1)$: in each component the reciprocal lcm sum for two primes is bounded by $V+V^2$, and $V\ge1/4$. It follows that
$$
 \sum_{s<S}\frac{h_P(s)}s|\bar W(s)-1|^2
 \ll_K A(P)\log S\,(J^{-1}+E).
$$
In (4) the signed moment per family is $O_K(H)$ and the unsigned one $A(P)\log S(1+O_K(E))$, uniformly at the *actual* endpoint $T(n)$. The average of the signed (4) is $o(P\log S/L)$; that of the unsigned (4) is $(1+o(1))|I|\log S/L$. In particular the singular series has **canceled** by (5).

To remove $\bar W$ from the physical sum apply the elementary two-linear-form Selberg upper sieve: for each $1\le s\le S$ with $(s,P)=1$, the number of primes $q$ with $P-sq\in I$ prime is
$$ \ll \mathfrak S(P)h_P(s)\,P/(s L^2).                               \tag{7}$$
Indeed the variable $q$ has range of length $\asymp P/s=P^{1-o(1)}$; the two forms are $q,P-sq$. There are two roots modulo $r\nmid Ps$ and one at $r\mid Ps$ (the coefficient case $r\mid s$ gives only $q=0\bmod r$). Both actual primes in the central range exceed any small fixed power e.g. $(P/s)^{1/20}$. A dimension-two upper sieve at that sifting limit, with an absolute constant, gives the local product $\prod(1-\nu(r)/r)$ there times $P/s$ and a power-saving remainder by residue counting $O(\nu(d))$. Equivalently use the standard upper sieve for two linear forms. Mertens and the summable tails after normalization yield (7); target or coefficient primes above the sieve limit contribute relatively $1+O(L(P/s)^{-1/20})$. The local corrections are precisely $\mathfrak S(P)h_P(s)$. Thus with log weights $(\log p)(\log q)/L\ll L$, Cauchy, (5) and the preceding second moment show that removing the auxiliary weights costs
$$ O_K\big((P\log S/L)(J^{-1}+E)^{1/2}\big)=o(P\log S/L) .$$
This also bounds the signed removal by absolute value. There is no division of an error controlled only relative to the larger prime density. Finally $(\log p)(\log q)/L=(1+O((1+\log S)/L))L$ uniformly; replace with $L$ in both statistics, bounding signed error by the known physical unsigned mass. Adding and subtracting and halving gives (1). The omitted $(s,P)>1$ or $q\mid P$ prime rows remain negligible. This completes the proof.

## Scope and related work

No ordinary Goldbach representation is obtained: the extracted tags cannot inhabit $s=1$ and the global unweighting is not accurate on one multiplier. The distinction from the usual almost-all binary Goldbach results is the assertion for an *individual target* under the stated local zero criterion, and under the cited all-Dirichlet half-plane for every target. JLL prove the sum-of-two-squares indicator asymptotic at the fixed shift 1, not this reflected prime with a near-full-size prime factor. [Runbo Li](https://arxiv.org/abs/2508.18285) proves an infinitely-often $p^{.679}$ large factor of $p-1$ at fixed shift. [Guo's October 2026 work](https://github.com/aster2024/openai-math-followups) concerns parity/cancellation of a shifted Möbius or Liouville function (including roughness variants); a parity law alone does not assert that a **second actual prime** exceeds $P/\exp(L^{1/4})$. No priority claim is needed. A zero-density improvement or published status of a newer GRH announcement is not an input.

## 4. A prescribed, fixed number of true small prime factors

There is also a bounded-rank corollary which does **not** use any unweighting. Fix sufficiently large $K$ and **one** of the separated families of $K$ full prime intervals in section 1 (no averaging in $j$). Let $\mathcal A$ be its squarefree products and $\mathcal V=\prod_{i\le K}\sum_{\ell\in\mathcal P_i}1/\ell$; in particular $4^{-K}\le\mathcal V\le2^{-K}$. Under the same external half-plane, or the local criterion with suitable fixed constants, the number of
$$
 P=p+a q,\qquad p\in I,\quad p,q\ {\rm prime},\quad a\in\mathcal A
$$
is
$$
 (1+o_K(1))\,\mathfrak S(P)\mathcal V\,|I|/L^2.                         \tag{8}
$$
Every such complement $P-p$ has **exactly** $K+1$ distinct prime factors. One occurs in each prescribed disjoint subpower interval, and the last is $q\ge(P/3)\exp(-2K L^{.2})$, which is far above all label primes. In particular such configurations exist at every sufficiently large even target in each of two consecutive fixed ranks $K+1,K+2$. The constants and sufficient size of $P$ may depend on $K$. We obtain neither a small specified numerical rank nor an asymptotic for any one specified value of $a$.

To prove (8), start with the physical sum over $n\in I$ of $\Lambda(n)\sum_{a|P-n,\ a\in\mathcal A}f((P-n)/a)$, where $f(h)={\bf1}_{h\ {\rm prime},\,h>P/S}\log(h)/L$. It is bounded on positive $h\le P$, and its size restriction is automatic for these central products. A prime remaining after extracting all the marked labels is the unique large factor; there are no further marks counted by mistake, also when $n$ is composite. Inserting rough and unit restrictions and removing proper powers costs $P^{1/2+o(1)}$ as before. For the Type II term (2) by Cauchy applies **directly** to this single residual $f(h)$, shell by shell, yielding $O_K(PL^{-3})$ after the same source mesh. No identity $F(ah)=F(h)$ is needed at this step. The Type I calculation of section 2 is termwise in the fixed small multiplier and uses ordinary BV on the remaining prime. Here restrict its outer sum to $s=a\in\mathcal A$, with weight one per such product; in particular $\sum_{a\in\mathcal A}1/a=\mathcal V$. Absolute errors are no larger than the analogous bounded-divisor-weight budget there. Every $a$ is a target unit, $a<T(n)$ for all $n\in I$, and $h_P(a)=1+O_K(\exp(-L^{.1}))$ uniformly. The resulting weighted main is therefore $(1+o_K(1))\mathfrak S(P)\mathcal V |I|/L$ before removing logarithms. Since neither prime's log is smaller than $(1-o(1))L$, this proves (8). No inference about rank one is obtained by letting $K$ decrease; the projected minor comparison requires its lower bound on $K$.
