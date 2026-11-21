# Central Goldbach with prescribed non-minority residue in the exceptional windows

This is an addendum to [the small-conductor theorem](SmallConductorExceptionalGoldbach.md) and [the polynomial-conductor extension](PolynomialConductorExceptionalGoldbach.md). As in those notes, every assertion is conditional on the existence of the stated real zero; no ordinary-no-exception conclusion is made.

Let \(N\) be sufficiently large even, \(L=\log N\), and \(\chi\bmod q_0\) a primitive quadratic character with a real zero \(1-\delta\). We work in either:

- \(q_0\le \exp(c\sqrt L)\), \(0<\Delta:=\delta L\le\Delta_0\), for sufficiently small fixed absolute constants; or
- \(q_0\le N^\kappa\), \(0<\Delta\le L^{-A_0}\), for any fixed \(A_0>0\) and a sufficiently small fixed \(\kappa=\kappa(A_0)>0\).

Let \(\mathcal A=\{a\bmod q_0:(a(N-a),q_0)=1\}\), put \(D_q=|\mathcal A|/\varphi(q_0)\), and let \(T\subset\mathcal A\) be nonempty with \(\nu=|T|\). Each \(a\in T\) is required to have \(\chi(a)=-1\). If all reflected signs \(\chi(N-a)\) on \(T\) equal \(+1\), there are actual central prime pairs \(p+(N-p)=N\), \(p\bmod q_0\in T\), with majority-prime log-weighted count
\[
     \gg \frac{\nu}{|\mathcal A|}\,\delta N\mathfrak S(N).              \tag{1}
\]
If all reflected signs on \(T\) equal \(-1\), their count with the log of \(p\) instead satisfies
\[
     \gg \frac{\nu}{|\mathcal A|}\,\frac{N\mathfrak S(N)}{L}.           \tag{2}
\]
These are uniform down to \(\nu=1\). The central interval is \(I=(N/3,2N/3)\). If one wants a particular residue of the minority prime in (1), exchange the two summands. We do not establish a prescribed minority–minority pair.

## 1. Residue tracking without a hidden loss

For the mixed case use \(\lambda(m)=1*\chi(m)\) as in the previous notes, \(m=N-p\), with the prime row restricted to \(p\bmod q_0\in T\). Then \(m\) is a unit of sign \(+1\) and the original hyperbola is unchanged. The exact retained prime density is now \(\nu/\varphi(q_0)\) times \(1+t^{-\delta}\) for a fixed \(t\in I\), before the factor 2 from the hyperbola. On the integer reference keep all \(\chi(m)=+1\) classes as before. The comparison of sifted Euler products remains, with the actual number of retained classes now external:
\[
         \frac{M_{\rm pr}}{M_{\rm int}}
                    =\frac{\mathfrak S(N)}{D_q}(1+O(1/z)),\qquad
    D_q=\prod_{\ell\mid q_0,\ell\nmid N}\left(1-\frac1{\ell-1}\right).
 \tag{3}
\]
For primes \(\ell\mid q_0,\ell\nmid N\), the second factor in (3) exactly accounts for the missing local \(N-a\) class. The hard case identified \(\nu=|\mathcal A|/2\) when all majority classes are used; no such identity is assumed here.

Here are the changes to the errors, in particular at a single residue. Let \(w=[u,k]\) be the auxiliary factor in the actual power presieve, \(d=u v\), and \((v,q_0w)=1\), as in the base proof. In both windows the ABL high-conductor term is treated by splitting unit classes of \(v\bmod q_0w\), and splitting the \(\nu\) allowed prime classes, not all \(q_0\) classes. Its unmeshed bound is
\[
      \ll \nu N^{\,1-\omega/11+33\eta} q_0^2 N^{o(1)}
\]
with the same small power choices \(\omega,\eta\). In the polynomial window the mesh has \(O(\delta^{-2}L^{C_0})\) intervals. For comparison to \((\nu/|\mathcal A|)\delta N\) we can divide by \(\nu/q_0\); the resulting exponent loss is at most \(33\eta+(9/2)\kappa+o(1)\) (two powers of \(q_0\) here, one for \(|\mathcal A|\), a further \(\kappa\) from the mesh and \(\kappa/2\) from the relative \(\delta\)). It stays below \(\omega/11\) by decreasing \(\kappa\). In the small-conductor window the original exponential-size mesh and \(q_0\) are subpower so the asserted saving remains a power saving.

For the polynomial window, the low \(q_0\)-character factor is no longer the special four-term formula of the previous note and does not need to be. The Fourier coefficient of **any** \(q_0\)-character against \(1_T\) is \(\le\nu/\varphi(q_0)\) in absolute value, with principal coefficient \(\nu/\varphi(q_0)\) and exceptional coefficient \(-\nu/\varphi(q_0)\). A character modulo \(q_0\) corresponds one-to-one to its primitive inducing character with conductor dividing \(q_0\). For each full primitive product with outside conductor \(s_*r_*\) coprime to \(q_0\), the full product determines its unique \(q_0\)-induced factor, including all 2-adic choices. There is no multiplicity corresponding to \(\varphi(q_0)\) even if \(T\) is a singleton. The harmonic induction bounds on \(s_*,r_*\) from the polynomial note are unaltered. Its collective zero estimate thus gives the whole low analytic error with an extra factor \(\nu/\varphi(q_0)\); dyadic and mesh losses are the same \(L^{C_2}\delta^{-2}\) and leave \(o((\nu/|\mathcal A|)\delta N)\). In the small-conductor window one may keep the original absolute \(O(N e^{-b\sqrt L})\) error and make \(c\) smaller to gain precision relative to \(\delta N/q_0\).

The physical mesh error at a variable hyperbola boundary uses exactly \(\nu\) admissible CRT classes modulo \(q_0[d,k]\), since \((q_0,[d,k])=1\). Thus the bound per \(k,d\) for mesh width \(H\) is \(O(\nu L[H/(q_0[d,k])+1])\). Summing with \(H=N\delta^{2}L^{-C_0}\) gives \(O((\nu/q_0)N\delta^2 L^{-2}+\nu N^{1/2+\eta+o(1)})\), by the harmonic lcm calculation. The first is now relative-small even at \(\nu=1\); the second has a power margin. The imprimitive corrections before mesh are \(\ll \nu N^{1/2+11\eta+\kappa+o(1)}\) in the polynomial window by counting each \(w,v\) once (a bound ignoring the \(\nu\) would also suffice). The mesh is polynomially bounded by \(N^{\kappa+o(1)}\) and leaves fixed slack. The discarded large-\(u\) term \(N^{1-9\eta/2+o(1)}\), harmonic completion error \(N^{1/2+10\eta+\kappa/2+o(1)}\) at scale \(N\), and proper-power terms each have a fixed power saving compared with \(\delta N/q_0\) by taking \(\kappa\ll\eta,\epsilon\). For the exponential-conductor window all these powers save more than needed. The same applies to the elementary integer reference floor and its harmonic completion.

In the mixed composite switch \(m=r s\), \(s\) largest minority prime and \(r>1\) product of the others, the exact varying-\(s\) residue set is \(r^{-1}(N-T)\bmod q_0\), size \(\nu\), consisting of reduced minority classes, as \(\chi(r)=+1\). This is an actual condition on the same prime carrying the log weight. In the exponential-conductor window use the adjusted AP main in those \(\nu\) classes and the spare relative error \(\delta X/q_0\) at \(X=N/r\gg N^\epsilon\). In the polynomial window its normalized Fourier coefficients again have size \(\le\nu/\varphi(q_0)\), so the collective error is \(\ll (\nu/\varphi(q_0)) X L^{C_3}[(\delta\log X)^J+X^{-c_1}]=o((\nu/|\mathcal A|)\delta X)\) uniformly, with power-small aggregate proper-power corrections. Having omitted all conductor primes in the upper sieve for \(N-rs\) multiplies its density relative to \(\mathfrak S(N)/\log X\) by at most \(D_q^{-1}\) (also \(r/\varphi(r)=1+O_\epsilon(1/z)\)). The factor \(\nu/\varphi(q_0)\) in the minority main pays this exactly. Thus the switched log-prime upper is \(\ll_\epsilon (\nu/|\mathcal A|)\delta X\mathfrak S(N)\), up to errors that carry \(X=N/r\). Summing against the cofactor harmonic weight \(O_\epsilon(\Delta)\), plus the power-small squarefuls, proves (1) as in the base proof. In particular a single residue costs the expected density factor and no further loss.

## 2. A real-zero-shifted proxy for the majority–majority case

On \(\chi(m)=-1\), the base \(\lambda(m)\) is zero. Instead use the nonnegative multiplicative proxy
\[
       F_\delta(m)=\sum_{d\mid m}\chi(d)d^{-\delta}.
\]
Nonnegativity follows at each prime power from geometric sums (including alternating sums when \(\chi(\ell)=-1\)). Exact reflection of divisors gives
\[
       F_\delta(m)=\sum_{\substack{d\mid m\\d<\sqrt m}}
                    \chi(d)(d^{-\delta}-m^{-\delta}d^\delta).
 \tag{4}
\]
There is no square diagonal on the unit \(\chi(m)=-1\) row. Both terms use the same primary ABL high estimate and identical lcm and exceptional low processing as §1: \(u^{\pm\delta}\), \(v^{\pm\delta}\) at \(uv<\sqrt N\) and \(m^{-\delta}\) for \(m\in I\) have bounded magnitudes and total variations (use partial summation against the applicable variable's interval prefix). Endpoint floors use the same absolute estimates. The coefficients at the retained \(q_0\)-characters give precisely the majority density from \(p\bmod q_0\in T\); \(\chi(m)=-1\) is a consequence of the chosen residue, not an averaging assumption.

In the \(m^{-\delta}\) term freeze the divisor cutoff on each \(p\)-mesh cell first, keep \(m^{-\delta}=(N-p)^{-\delta}\) as a real weight and use partial summation in \(p\) for that fixed cutoff. After restoring the true cutoff, the resulting main integral at each real endpoint \(t\) contains \((N-t)^{-\delta}\) as a scalar, outside the finite divisor sum \(d<\sqrt{N-t}\). The uniform harmonic completion below then multiplies the full \(G_k(-\delta)\) by exactly that scalar; it never needs a separation of the original moving cutoff.

For the analytic main, write for \(|s|\le\delta\)
\[
   G_k(s)=\sum_{\substack{d\ge1\\(d,Nq_0)=1}}
                         \frac{\chi(d)d^{-s}}{\varphi([d,k])}.
\]
In the integer comparison use \(1/[d,k]\) in place of \(1/\varphi([d,k])\). For \(|s|\le\delta\), continued tails after \(d<\sqrt m\) have the same power reserve: by partial summation with the harmonic tail bounds of [ABL Lemma 5.2](https://arxiv.org/html/2005.13915v1#S5), the \(v>T\) tail in coprime \(\chi(v)v^{-s}/\varphi(v)\) is \(\ll \tau(kNq_0)\sqrt{q_0}(\log(2q_0T))^{O(1)}T^{-1+\delta}\). Since \(\delta L\ll1\) and \(T\asymp\sqrt N/u\) for \(u\le N^{10\eta}\), this is the same power as before. For \(u>N^{10\eta}\) the analogue of the Rankin bound gains \(U^{-1/2+\delta}k^{1/2}N^{o(1)}\), with \(U=N^{10\eta}\). The full \(v\)-sums are log-bounded also at \(s=-\delta\), using elementary periodicity to bound \(L(1+s,\chi)\) and absolutely convergent complementary Euler factors; their finite partial sums at \(v\le\sqrt N\) are log-bounded absolutely. The integer version follows from the ordinary coprime \(\chi(v)/v\) tail without the totient. Thus all relative error checks of §1 still apply.

The decisive point is that
\[
                     G_k(-\delta)=0 \quad\text{for every }k.            \tag{5}
\]
In fact the base Euler factor at an unexcluded \(\ell\) is
\[
 T^{\rm pr}_\ell(s)=1+\frac{\chi(\ell)\ell^{-s}}
                              {(\ell-1)(1-\chi(\ell)\ell^{-1-s})}.
\]
Multiplication by \(1-\chi(\ell)\ell^{-1-s}\) leaves \(1+\chi(\ell)\ell^{-s}/[\ell(\ell-1)]\); the latter product converges absolutely. The \(k\)-local change replaces the exponent-zero term 1 by \(1/(\ell-1)\), and is a finite regular multiplication. For \(\ell\ge3\) the denominator \(T_\ell^{\rm pr}(s)\) is nonzero throughout this small real interval. Thus the full value has a factor \(L(1+s,\chi)\), including at \(s=-\delta\), justified by the preceding convergent tails. The same is true for the integer model with \(T_\ell^{\rm int}(s)=(1-\chi(\ell)\ell^{-1-s})^{-1}\). Hence the second half in (4) contributes no main term at all, not just an error \(O(\Delta)\).

At \(s=\delta>0\), the model sieve densities obtained by the same local change are nonnegative, \(<1\), and \(\le 2/\ell+O(\ell^{-2})\), uniformly for both models. For example, when \(\chi(\ell)=-1\), the modified numerator \(1/(\ell-1)+T_\ell^{\rm pr}(\delta)-1\) is positive since \(\ell^{-\delta}/(1+\ell^{-1-\delta})<1\); the \(\chi(\ell)=+1\) case is immediate. The dimension is at most two. The lower sieve on the actual nonnegative \(F_\delta\), and the upper sieve on the integer reference, are therefore valid. The integer reference now uses all majority residue classes. On each of its central majority primes, \(F_\delta(m)=1-m^{-\delta}\asymp\Delta\); their number is \(\gg N/L\) by the majority adjusted PNT on all its own classes, so the reference is \(\gg\delta N\). Its Euler ratio with the prime-row model is again (3): at \(\ell<z\) the local change cancels the factor \(T_\ell(s)\), and the tail now has \(1+\chi(\ell)\ell^{-\delta}/[\ell(\ell-1)] =1+O(\ell^{-2})\). The absent factor 2 in (4) compared with the mixed hyperbola affects only an absolute constant. We conclude
\[
 \sum_{\substack{p\in I,\ p\ {\rm prime}\\p\bmod q_0\in T,\ P^-(N-p)\ge z}}
                  \log p\,F_\delta(N-p)
           \gg (\nu/|\mathcal A|)\,\delta N\mathfrak S(N),
 \tag{6}
\]
with the same exclusions of the \(O(\log N)\) prime divisors of \(N\) at negligible cost.

On squarefree \(m\) in this row the number of \(\chi=-1\) prime factors is odd. If there is exactly one such factor \(s\) and \(m\) is composite, \(r=m/s>1\) consists only of minority primes and \(F_\delta(m)\ll_\epsilon\Delta\); their cofactor harmonic sum is \(O_\epsilon(\Delta)\). If there are at least three \(\chi=-1\) factors, use \(F_\delta(m)\ll_\epsilon\Delta^3\), choose any unique largest factor \(s\), and bound the harmonic sum of the remaining cofactors by \(O_\epsilon(1)\): all factors are \(\ge z=N^\epsilon\) and the rank is bounded, while \(\sum_{z\le\ell\le N}1/\ell\ll_\epsilon1\). In either case, for each fixed \(r\) the required actual \(s\)-residue set is \(r^{-1}(N-T)\), size \(\nu\). The same switched upper sieve as §1 bounds the \(\log s\)-total by
\[
             \ll_\epsilon (\nu/|\mathcal A|)\,X\mathfrak S(N)/\log X,
                   \qquad X=N/r,
\]
because the principal-plus-or-minus-exceptional density in each actual residue is at most twice the principal. In particular no minority saving is presumed on the varying \(s\) variable. The power-bound and collective errors still sum relative to the same scale used in §1. Multiplying by \(\log p/\log s\ll_\epsilon1\), and using \(\log X\asymp_\epsilon L\), the two squarefree composite contributions are respectively at most
\[
        O_\epsilon\!\left((\nu/|\mathcal A|)\frac{N\mathfrak S(N)}{L}
                                             (\Delta^2+\Delta^3)\right).
\]
The original power-saving squareful bound holds since \(F_\delta(m)\le\tau(m)\). These errors are smaller than (6) when the fixed \(\Delta_0\) is decreased or in the polynomial window where \(\Delta\to0\). On the surviving minority-free prime \(m\) of sign \(-1\), \(F_\delta(m)\le\Delta\). Dividing the positive remainder by this bound proves (2).

## 3. All target strata and the earlier soft alternative

If the complete character average \(C_\chi(N)\) is less than 1, then an admissible opposite-sign pair exists by its definition. Orient it with a majority first summand and apply (1). If \(C_\chi(N)=1\), all admissible pairs preserve sign and all conductor prime factors \(\ell\ge5\) divide \(N\) by Matomäki–Merikoski's local product. There is at least one such factor for \(N\) large in either window: the primitive quadratic conductors involving only 2 and 3 are bounded, whereas a near-one real zero as in either hypothesis forces \(q_0\to\infty\). Varying the unit residue at this prime factor while holding all other local residues admissible gives both signs, since its local quadratic character is nonprincipal and \(\ell\mid N\). Thus there is an admissible majority–majority class, to which (2) applies. This proves a **central** pair in every local stratum of either conditional window independently of the packaged error in the prior soft result.

For comparison, there is also a direct reparameterization of [Matomäki–Merikoski v2, §7](https://arxiv.org/html/2112.11412v2#S7) in the soft strata \(C_\chi(N)>-1\). Their first display in §7 allows \(X=N/4\) on the minus branch, so a fixed nonnegative nonzero smooth \(g\) supported in \((4/3,2)\) places both summands in \(I\). Fix their \(A,C,\varepsilon\) and sieve \(\beta\); take a **large fixed** \(u\) rather than increasing \(u\) according to (41). Their rough-proxy replacement display immediately before (41) has normalized errors \(u^8/(V^2\eta_{\rm MM}^{V/(3u)})\), \(u^6 V/\eta_{\rm MM}\), \(u^{10}/q_0^{V/(2u)}\), plus an additive \(O((z+\omega(q_0))L^2)\), where \(V=\log N/\log q_0,\ \eta_{\rm MM}=V/\Delta,\ z=X^{1/u}\). Their already-summed \(S,S\) and \(L,L\) displays around (43) have analogous normalized errors, at most \(O((1+u)e^{-Au/3000})\), and power errors \(O(X^{7/9+3/1000}q_0^2)\); the mixed main before Siegel's step is \(O_\varepsilon((N/\varphi(N))X u^4/q_0^{1-\varepsilon})\). All are small after fixing \(u\) large and then \(\Delta_0\) small, as the other terms tend to zero in the small-conductor window; the argument likewise works in the polynomial window with \(\Delta\to0\) and fixed sufficiently small \(\kappa\). Their \(1+C_\chi(N)\ge2/3\) supplies a positive fixed weighted main. This alternative does not give prescribed classes or the hard stratum on its own, and nothing here removes the exceptional hypothesis.

### Prescribed-progression comparison

[Bhowmik–Halupczok–Matsumoto–Suzuki, Theorems 1–2](https://pro.univ-lille.fr/fileadmin/user_upload/pages_pros/gautami_bhowmik/Publications/gap.pdf) study summatory binary Goldbach counts for prescribed progressions; a summatory formula does not give a lower bound at this fixed integer. [Wright, arXiv:2609.35950v1](https://arxiv.org/abs/2609.35950v1) studies the distribution of a single prime in large moduli under a Siegel zero, rather than a pointwise pair count. In particular, an additive relative-principal error in the one-prime model need not be small compared with the nearly cancelled minority density used in (1). No priority is asserted.
