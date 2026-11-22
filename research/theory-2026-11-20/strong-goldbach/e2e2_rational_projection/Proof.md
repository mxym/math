# Removing the rational modes of the actual balanced semiprime covariance

This is an unconditional statement about a same-quotient **quadratic** remainder. It does not evaluate its high-frequency part, assert a representation by two semiprimes, or prove Goldbach.

Let \(N=x\) tend to infinity through the even integers and put \(L=\log x\). Take
\[
U,V\asymp x^{39/80},\qquad T,S\asymp x^{41/80},\qquad
UT,VS\asymp x.
\]
Choose disjoint subintervals of \([U,2U]\) and \([V,2V]\), and let \(\mathcal U_0,\mathcal V_0\) be arbitrary subsets of their actual primes coprime to \(N\). Disjointness means that \(u\ne v\) throughout. Fix long windows \(I_t\subset[T,2T]\), \(I_s\subset[S,2S]\) and assume that the contributing physical products \(ut\) and \(vs\) stay in a fixed central subinterval of \((0,x)\). One may obtain this by choosing the four windows inside smaller macroscopic boxes. Constants in all scale comparisons are fixed.

Write \(\lambda_N(n)=\log n\) if \(n\) is prime and \((n,N)=1\), and zero otherwise. Define the all-actual count and its purely geometric factor by
\[
\begin{split}
R&=\sum_{u\in\mathcal U_0,v\in\mathcal V_0}\log u\log v
 \sum_{\substack{t\in I_t,\ s\in I_s\\ut+vs=N}}\lambda_N(t)\lambda_N(s),\\
\mathcal V&=\sum_{u\in\mathcal U_0,v\in\mathcal V_0}\frac{\log u\log v}{v}
  \big|\,I_t\cap[(N-v\sup I_s)/u,(N-v\inf I_s)/u]\,\big|.
\end{split} \tag{1}
\]
Endpoints may be fixed half-open in the counting sum, with their natural meanings in the length. In particular \(\mathcal V\ll x\); if the label windows have fixed positive widths and an interior feasible product region, the full unmasked \(\mathcal V\) is of order \(x\). The weights on both short labels in (1) are true prime weights.

Put
\[
w=\frac{L}{\sqrt{\log L}},\qquad W=\prod_{p\le w}p,\qquad
g(n)=\frac W{\varphi(W)}{\bf1}_{(n,W)=1},\qquad A(n)=\lambda_N(n)-g(n).
\tag{2}
\]
For each \(u,v\), write its exact target line as
\[
 t=t_0+vj,\qquad s=s_0-uj,\qquad ut_0+vs_0=N,\quad j\in\mathbb Z.
\tag{3}
\]
The admissible \(j\)'s are those in the actual windows of (1). Fix any \(D>0\). Choose sufficiently large constants \(B_1,B\), in that order after \(D\). Divide each long physical window into a grid of intervals of length \(Z\asymp U L^B\) (an end interval can be shorter). Intersect the two grids on each line (3). The resulting cells are finite integer intervals in the variable \(j\). Discard cells with fewer than \(L^{B_1}\) integer points. For each retained cell \(C\), let \(\mathcal P_C\) be the ordinary complex orthogonal projection in \(\ell^2(C)\) onto the span of
\[
  j\longmapsto e(kj/h),\qquad 1\le h\le L^D,\quad 0\le k<h,\quad (k,h)=1,
  \tag{4}
\]
with \(0/1\) included and \(e(r)=e^{2\pi ir}\). The same projection acts on the two legs of the **same physical line and cell**. The span is conjugation invariant, so the projections of real arrays are real.

Then the actual asymptotic reduction is
\[
 R=\mathfrak S(N)\mathcal V+
 \sum_{u,v}\log u\log v
   \sum_{C}\left\langle(1-\mathcal P_C)A(t_0+v\,\cdot),
                  (1-\mathcal P_C)A(s_0-u\,\cdot)\right\rangle_{\ell^2(C)}
 +o\bigl(x\mathfrak S(N)\bigr).
\tag{5}
\]
Here \(\mathfrak S(N)\) is the standard Goldbach singular series for ordered prime weights. The retained \(\ell^2\) products have no known sign. We use only classical short-interval Siegel–Walfisz, the primitive large sieve (and its familiar two-prime product consequence), and calculus of finite Fourier projections. Low rational frequencies are evaluated, **not** simply declared negligible by an unsigned variance or a pole approximation.

## 1. The three model terms and exact centering

Let \(S_w(N)\) be the finite local product
\[
 S_w(N)=\prod_{p\le w}(1-1/p)^{-2}\bigl(1-2/p+{\bf1}_{p\mid N}/p\bigr).
 \tag{6}
\]
It includes the factor 2 at \(p=2\). Uniformly for even \(N=x\),
\[
 S_w(N)=(1+o(1))\mathfrak S(N),\qquad
 \sum_{\substack{p>w\\p\mid N}}\frac1p
 \le \frac{\log N}{w\log w}=o(1).
 \tag{7}
\]
The other factors of the infinite series have absolutely convergent tail \(O(1/w)\).

In the \(\lambda_N(t)g(s)\) term, open \(g(s)=(W/\varphi(W))\sum_{d\mid W}\mu(d){\bf1}_{d\mid s}\). The exact condition on the source product is
\[
  ut\equiv N\pmod{v d},\qquad ut\in[N-v\sup I_s,N-v\inf I_s].
 \tag{8}
\]
Terms with \((d,N)>1\) cannot occur, since the genuine \(u,t\) source is a unit modulo \(N\). For all other \(d\), the modulus \(v d\) is a target unit, and the entire genuine source \(u,t\) is a unit modulo \(v d\): \(u\ne v\), \(t\gg v\), and all primes dividing \(d\) are at most \(w\). Here \(\log W=O(w)=o(L)\), so every such modulus is \(<x^{.499}\) for large \(x\). The map \(v,d\mapsto vd\) is injective, since \(v\gg w\) is its only possible prime factor above \(w\). Fixed bounded short-sequence masks are allowed; the \(\log\) weights cost fixed powers of \(L\).

We use the below-root two-prime product estimate from the independently proved [long-prime-slot dispersion note](../prime_slot_dispersion_512/Proof.md), whose proof in this range uses only primitive character large sieve and Siegel–Walfisz on the long prime slot. It applies with the actual single residue \(N\) across all these moduli. The maximizing endpoint version needed for (8) follows without introducing a \(W\)-loss. Check endpoints on a grid of relative mesh \(L^{-A_1}\). For the interval between a moving endpoint and its grid point, a modulus \(q\) has at most \(O(x/(qL^{A_1})+1)\) possible integer products in that reduced class, each with at most one legitimate \(u,t\) factorization. The corresponding principal loss is \(O(xL^{-A_1}/\varphi(q))\) before weights. Sum over \(q\le x^{.499}\), then use the uniform discrepancy with sufficiently high log reserve at the polylogarithmically many grid points. Thus the prescribed interval of (8) may depend on \(v\), with aggregate error \(O_A(x L^{-A})\).

The principal factor after opening \(d\) is
\[
 \frac1{\varphi(v)}\frac W{\varphi(W)}
       \sum_{\substack{d\mid W\\(d,N)=1}}\frac{\mu(d)}{\varphi(d)}
 =\frac{S_w(N)}{\varphi(v)} .
 \tag{9}
\]
To verify (9), a prime \(p\nmid N\) contributes \(p(p-2)/(p-1)^2\), while \(p\mid N\) contributes \(p/(p-1)\). For each \(u,v\), the genuine prime log sum over the corresponding \(t\) interval differs from its length by \(O_A(TL^{-A})\), uniformly in its endpoints, by ordinary PNT for prefixes. It excludes only \(O(1)\) possible prime divisors of \(N\) on this polynomial scale. Replace \(1/\varphi(v)\) by \(1/v\) at power-small cost, since \(v\) is prime of fixed positive exponent. Consequently the mixed term equals \(S_w(N)\mathcal V+o(x)\), with any needed log reserve. The other mixed term \(g(t)\lambda_N(s)\) is identical after swapping the two legs; the physical \(s\)-interval has length \(u/v\) times the \(t\)-interval, and the lattice spacing is now \(u\), so the geometric factor is exactly the same.

For \(g(t)g(s)\), open two divisors \(d,e\mid W\) for each fixed \(u,v\). On (3), simultaneous \(d\mid t,e\mid s\) imposes one residue class modulo \([d,e]\) if \((d,e)\mid N\), and is impossible otherwise, since \(u,v\) are units modulo \(W\). The floor error is \(O(1)\) for each \(d,e,u,v\). Its total is \(O(UV L^C\tau(W)^2)=x^{39/40+o(1)}\), also including \((W/\varphi(W))^2\). The main multiplies \(\mathcal V\) by the Euler product (6). Expanding \((A+g)(A+g)\) now yields the exact reduction
\[
 R=\mathfrak S(N)\mathcal V+
   \sum_{u,v}\log u\log v\sum_{j\ {\rm in}\ (3)} A(t_j)A(s_j)
   +o(x\mathfrak S(N)).
 \tag{10}
\]
Crucially (10) has *both* remaining coefficients on the same short integer parameter \(j\). There is no claim that their errors can be made independent.

## 2. A maximal short-interval estimate with one large prime modulus

Let \(I\) be any padded physical grid bin on the \(t\)-side, of length \(O(Z)\). Enlarge the raw bin by \(O(V)\) at both ends. This accounts for the last lattice step when a retained \(j\)-cell is replaced by a real half-open progression interval of exact length \(v|C|\). A similar pad \(O(U)\) is used on the \(s\)-side. All padded bins stay at the same polynomial long scale.

Fix \(h\le L^D\). For prime \(v\asymp V\), unit \(a\bmod v\), and any \(b\bmod h\), define the following two local discrepancies, for interval \(I'\subset I\):
\[
\begin{split}
E_\lambda(v,a,b;I')&=
 \sum_{n\in I',\,n\equiv a(v),\,n\equiv b(h)}\lambda_N(n)
 -\frac{|I'|}{\varphi(v)\varphi(h)}{\bf1}_{(b,h)=1},\\
E_g(v,a,b;I')&=
 \sum_{n\in I',\,n\equiv a(v),\,n\equiv b(h)}g(n)
 -\frac{|I'|}{v h}\,G_{\gcd(h,W)}(b),\\
G_d(b)&=\frac d{\varphi(d)}{\bf1}_{(b,d)=1}.
\end{split} \tag{11}
\]
Use integer endpoints in the maximum below; real endpoints differ by the same sums and a change \(O(1)\) in the continuous length, already harmless.

Uniformly in \(h\), either discrepancy satisfies
\[
 \sum_{\substack{v\asymp V\\v\ {\rm prime}}}\ \sum_{a(v)^*}\ \sum_{b(h)}
 \max_{I'\subset I}|E(v,a,b;I')|^2
 \ll (ZV+Z^2/V)L^{C_1}+O_{A,D}(Z^2 L^{-A})
 \tag{12}
\]
with an absolute fixed log power \(C_1\). To see this, use multiplicative characters **only modulo \(v\)**, keeping \(n\equiv b\bmod h\) inside the coefficient. For nonprincipal characters the conductor is \(v\) itself. Parseval over \(a\bmod v\) and the primitive multiplicative large sieve on \(v\asymp V\), for a fixed subinterval \(J'\) of \(I\), give
\[
 \sum_{v,a,b} |E_{\rm nonprinc}(v,a,b;J')|^2
       \ll (|J'|/V+V)\sum_{n\in J'} |F(n)|^2 ,
 \tag{13}
\]
where \(F=\lambda_N\) or \(g\). The sum over \(b\) does not increase the energy of the coefficients because their supports for different \(b\)'s are disjoint. For the maximum, split every subinterval into \(O(L)\) pieces in the ordinary dyadic decomposition of a padded bin. Cauchy costs \(O(L)\) and summing (13) over the dyadic intervals costs at most another \(O(L)\), since at each level the intervals are disjoint. Use \(\|F\|_\infty\ll L\). This proves the first term of (12).

For the principal character on the prime side, \(n\gg v\) ensures that deleting multiples of \(v\) does not remove an actual prime of the bin. The stated main in (11) is given by short-interval Siegel–Walfisz, uniformly in log-sized \(h\). For example [*Prime Number Theorem for Analytic Skew Products*, Proposition 9.4](https://arxiv.org/pdf/2004.01125#page=71) records it for lengths \(>T^{7/12+\varepsilon}\) and \(h\le L^{O(1)}\). Apply it to intervals of length at least \(T^{.9}\); for shorter intervals use the pointwise bounds and \(T^{.9}L\ll_A ZL^{-A}\). This last inequality holds since \(39/41>.95>.9\). The removal of the polynomial-sized prime divisors of \(N\) is \(O(L)\). After dividing by \(\varphi(v)\), the error in each \(a,b\) class is \(O_{A,D}((Z/V)L^{-A})\). Summing its square costs at most \(O(V^2h)\) classes, and can absorb all \(h\le L^D\) by choosing the fixed SW accuracy first for that loss. Nonunit \(b\) has no eligible prime at this scale, and its model is zero.

For the \(g\) principal, first sum \(g\) in the single progression modulo \(h\). Opening \(d\mid W\) and counting by CRT gives \((|I'|/h)G_{\gcd(h,W)}(b)+O((W/\varphi(W))\tau(W))\). This uniform floor error is \(x^{o(1)}\), negligible compared with \(ZL^{-A}\) at the **unrestricted** bin length. Restricting to \((n,v)=1\) can discard at most \(O((Z/V+1)W/\varphi(W))\) from this principal. After division by \(\varphi(v)\) replace \(\varphi(v)\) by \(v\) in the main at the same power-small scale. This gives the second term in (12). It would not suffice to use that \(x^{o(1)}\) floor bound directly on every large-residue cell; (13) is essential there. The symmetric estimate holds for the \(s\)-bins with \(u\) as the large prime modulus.

## 3. Actual Fourier coefficients on the cells

There are \(O(T/Z+S/Z+1)\) nonempty intersected cells per \((u,v)\), since \(t,s\) change monotonically, in opposite directions, along (3). Dropping all those with \(|C|<L^{B_1}\) costs \(O(xL^{B_1-B+4})=o(x)\) in (10), for \(B>B_1+6\). This includes all thin boundary intersections; no claim of \(L^B\) lattice points on each retained row is needed. The count of all candidate \(j\)'s, even before using primality of the short labels, is \(O(UV\,T/V)=O(x)\).

Let \(q_C=|C|\). Define normalized coefficients, for reduced \(k/h\) as in (4), by
\[
 a_C(k/h)=q_C^{-1/2}\sum_{j\in C}A(t_j)e(-kj/h),\qquad
 b_C(k/h)=q_C^{-1/2}\sum_{j\in C}A(s_j)e(-kj/h).
\]
Then in summed square norm (over all cells and these frequencies, even with weight \(\log u\log v\)) we can replace them, to error \(O_A(xL^{-A})\) for any prescribed \(A\), by
\[
 \begin{split}
 a_C^0(k/h)&=\sqrt{q_C}\,\frac{\mu(h)}{\varphi(h)}
                   {\bf1}_{h\nmid W}\,e(k\bar v t_0/h),\\
 b_C^0(k/h)&=\sqrt{q_C}\,\frac{\mu(h)}{\varphi(h)}
                   {\bf1}_{h\nmid W}\,e(-k\bar u s_0/h).
 \end{split} \tag{14}
\]
The powers \(B_1,B\) may be increased in terms of the desired saving.

Indeed, the \(t\)-interval for \(C\) can be taken half-open of length \(v q_C\), from its first \(t_j\) to one lattice step after its last, inside the padded bin of §2. The correspondence \(j\bmod h\longleftrightarrow t_j\bmod h\) is a bijection. For fixed \(h\), additive Parseval shows that the error contributed by (11) to the sum over all \(k\bmod h\) of squared coefficient errors in this cell is at most \(2h q_C^{-1}\sum_{b\bmod h}(|E_\lambda|^2+|E_g|^2)\). Reduced \(k\)'s only decrease this bound. In any fixed \(t\)-bin and for fixed \(v\), a given unit residue \(a=N\bar u\bmod v\) has \(O(1)\) possible short integers \(u\), by \(U\asymp V\). Each such \(u,v\) pair crosses only \(O(1)\) \(s\)-bins during that \(t\)-bin, since \(ds/dt=-u/v\asymp-1\). Thus (12), summed over the \(O(T/Z)\) padded bins and divided by the actual lower bound \(q_C\ge L^{B_1}\), bounds the total coefficient error for this \(h\) by
\[
 \ll h L^{-B_1}\frac TZ\big((ZV+Z^2/V)L^{C_1}+Z^2 L^{-A'}\big).
 \tag{15}
\]
Attach at most \(O(L^2)\) for the short weights and sum over \(h\le L^D\). The first term uses \(TV\asymp x\); choose \(B_1\) large in terms of \(A,D,C_1\). The part with \(TZ/V\ll T L^B\) saves a fixed power. The \(TZL^{-A'}\) part allows a short-SW reserve \(A'\) after \(B_1,B\) have been fixed. The inverse orientation is exactly the same, including the decreasing slope of \(s_j\).

For the local means in this calculation, the first mean in (11) gives, at primitive \(k/h\), the complex coefficient
\(\sqrt{q_C}\,[v/\varphi(v)]\,\mu(h)e(k\bar v t_0/h)/\varphi(h)\), by the Ramanujan sum in \(t\bmod h\). The \(g\) model \(G_{\gcd(h,W)}\) is periodic with period \(\gcd(h,W)\); it contributes zero unless \(h\mid W\), in which case its coefficient is the same without \(v/\varphi(v)\). The factor \(v/\varphi(v)=1+O(1/V)\) can now be discarded in summed square norm by the polynomial size of \(V\), the polylogarithmic number of frequencies, and \(\sum q_C=O(x)\). These are the means in (14). The same calculation for \(s_j=s_0-uj\) gives the indicated opposite sign in its phase. This argument treats composite \(h\), repeated prime factors in \(h\), and nonunit \(b\bmod h\) explicitly.

## 4. The calibrated low rational contribution

The frequencies in (4) have circle separation at least \(L^{-2D}\) and number \(O(L^{2D})\). On each interval of \(q_C\ge L^{B_1}\) consecutive integers, the unit-\(\ell^2\)-normalized mode vectors have a Gram matrix differing from the identity in operator norm by \(O(L^{4D-B_1})\), using the geometric sum for every off-diagonal entry and the row-sum bound. In particular the error is small enough for inversion once \(B_1>4D+1\). The exact projected bilinear product
\(\langle\mathcal P_C A(t_\cdot),\mathcal P_C A(s_\cdot)\rangle\)
therefore equals \(\sum_{k/h} a_C(k/h)\overline{b_C(k/h)}\) up to an error bounded by \(O(L^{4D-B_1}\|A(t_\cdot)\|_2\|A(s_\cdot)\|_2)\). The summed physical norms squared, with the short weights, are \(O(xL^4)\) by \(|A|\ll L\). The Gram bound also controls the sums of squared actual mode coefficients by twice those norms. Thus (14), Cauchy, and a large \(B_1\) justify replacing the complete projected sum by the product of the local coefficients in (14), with an arbitrary prescribed log saving.

On this **same cell with the same quotient coordinate**, at denominator \(h\) the local pair sum is
\[
 \sum_{k(h)^*} a_C^0(k/h)\overline{b_C^0(k/h)}
 =q_C\,\frac{\mu(h)^2c_h(N)}{\varphi(h)^2}{\bf1}_{h\nmid W}.
 \tag{16}
\]
Indeed the phase is \(k(\bar v t_0+\bar u s_0)/h=k\overline{uv}N/h\), and \(uv\) is a unit modulo \(h\). This is not a diagonal energy identity: it retains the signed Ramanujan factor of the **actual target**. Uniformly in \(N\),
\[
 \sum_{h\nmid W}\frac{\mu(h)^2|c_h(N)|}{\varphi(h)^2}
 \ll \mathfrak S(N)\left(\frac1w+\frac{L}{w\log w}\right)
 =o(\mathfrak S(N)).
 \tag{17}
\]
For the absolute squarefree Euler series use \(|c_p(N)|=1\) for \(p\nmid N\) and \(p-1\) otherwise. Its total product is \(O(\mathfrak S(N))\), by comparison at each prime (the nontarget factors differ by a summable error). The contribution with some \(p>w\) is bounded by that product times the sum of its local increments at these primes; (7) and \(\sum_{p>w}1/(p-1)^2=O(1/w)\) give (17).

Finally \(\sum_{u,v}\log u\log v\sum_C q_C\ll x\): each line has \(O(T/V+1)\) points and each short-prime log sum in a dyad is \(O(U)\) or \(O(V)\). Hence (16)–(17) make the entire projected-onto contribution \(o(x\mathfrak S(N))\), without a loss of extra powers of \(L\) from the prime label weights. Mixed projected/off-projected terms are **exactly zero in each cell** by the common orthogonal projection. Combine this with (10) and the discarded-cell estimate to get (5).

The windows in \(j\) here are at polylogarithmic length, and (4) has polylogarithmic denominators, selected before choosing the larger cell length. The residual is the full orthogonal complement of those modes, not a negligible discretization error. In particular no absolute or one-sided bound on that residual follows from (12); a correlation of two actual fluctuations at the same \(j\) can survive all these rational-mode restrictions. A relative lower for the right side of (5) at a single fixed target still needs new input.

## Comparison

The variance estimate is classical large sieve plus unconditional short-interval Siegel–Walfisz. The separate determinant main with two smooth long slots also fits [Bettin–Chandee, Corollary 1](https://arxiv.org/abs/1502.00769); that corollary does not apply to two genuine long prime weights. The mixed distribution in §1 uses only the below-root range, not Wright's preprint or the upper \(.512\) endpoint proved in the linked note. The work here keeps the literal \(ut+vs=N\) line and evaluates the rational-mode part of its actual centered covariance rather than inferring a sign from separate residue averages. Arneth’s [September 2026 preprint PIHR–Goldbach XIII](https://zenodo.org/records/23016390) concerns character-nullmode cancellation in a Type-II reduction for binary Goldbach. Here “modes” are instead all primitive additive rational frequencies on a common physical quotient cell for two actual semiprime legs; no estimate from that preprint is used. The [2025 preprint on exact semiprime sums](https://www.preprints.org/manuscript/202510.2442) claims a different whole-correlation conclusion, not used here. No priority is claimed for the classical inputs, and this calculation is not a whole Type II estimate.
