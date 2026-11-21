# Polynomial-small factor deletion for a high smooth q cutoff

Keep the actual favorable reflected rank-six rows of
[FullFavorableRankSixAbsorption.md](FullFavorableRankSixAbsorption.md).
In particular \(N=2x\), \(L=\log x\), \(n=sq\in(x/2,x]\),
\(m=N-n=pG\), the short \(s\) is true prime in one of the stated
bands, and \(G\) is the product of five true independent prime
labels at exponents bounded away from zero. The given \(\rho,\eta\)
and true \(p\)-band give
\[
 \log_xG=.5695+\eta+O(\rho),\quad 0<\eta<.002,\qquad
 \log_xs\le.139+\rho .
\]
The proof also applies to the same narrow shape with differently
allocated five true labels, all above \(x^{.02}\), provided the
same length relations and unit support hold. Keep the actual
positive \({\cal W}(s,q)=W_s(q)(-C^\dagger(m))=O(L)\) on that
favorable profile, with \((q s,N)=1\); the proof of the
absolute estimate below only uses its positivity and upper bound.

Let \(f\) be any fixed real compactly supported \(C^\infty\)
function on \(\mathbb R\), equal to 1 on \([0,.002]\) and zero on
\([.45,\infty)\). Define
\[
 D_f(q)=\sum_{d\mid q}\mu(d)f(\log d/L),\qquad
 C_f(q)=\Lambda(q)/\log q-D_f(q).
\]
For a smooth high-cutoff insertion in the actual rank-six rows, use
a positive-side derivative supported in a fixed positive
exponent interval and an endpoint below the applicable short
modulus exponent for \(a\). The same first-order finite masked
\(\mu/\phi\) moment as in
[FavorableRankSixLeastPrimeDeletion.md](FavorableRankSixLeastPrimeDeletion.md)
then makes the whole change to \(C_f\) log-small. In particular
this can hold even for a cutoff near .429 rather than .199.
The absolute deletion below does not require that arithmetic
exchange and does not require a second-moment modulus \(x^{2(.429)}\).

**Claim.** For a sufficiently small absolute \(\delta_0>0\), uniformly
in \(0<\delta\le\delta_0\) and each actual even \(N\),
\[
 \sum_{\substack{s,q\\P^-(q)\le x^\delta}}
       {\cal W}(s,q)|C_f(q)|
  \ll_{\eta,f}\delta\,\mathfrak S(N)x/L+O_{A,\eta,f}(xL^{-A})
 \tag{1}
\]
for every fixed \(A>0\) and large \(x\).
The constant of the main upper is independent of \(\delta\).
This is an actual absolute small-factor gain at the
reference scale, including for a high cutoff beyond the
available square-modulus method. It is not a sign estimate
for the remaining rough part.

## 1. Marked extension of the physical modular hyperbola

Set \(\kappa=.001\), \(c_1=.00002\), and
\(\gamma_0=\delta_0=.000001\).
Let \(\gamma\in[C_0/(2\log L),\gamma_0]\) with fixed \(C_0>0\).
Suppose that \(u\le x^\kappa\) is a fixed integer with all prime
factors \(\le x^\gamma\) and \((u,N)=1\). Write
\(q=u r t\) with both \(r,t>1\), \(P^-(rt)>x^\gamma\);
they are **integer** factors, not assumed prime.
Optionally fix a squarefree product \(a\le x^{c_1}\) of primes in
\((x^\gamma,x^{2\gamma}]\), with \(a\mid r\) and \(r\ge x^{\kappa/4}\).
There is also the unmarked case \(a=1\), with no extra lower
bound on \(r\).
For fixed true \(s,G\), the weighted count of all such actual
splittings \(r,t\) with true \(p\) is
\[
 \ll_\eta
       \frac{\mathfrak S(Nu)x}{sG\,u a\,\gamma^3 L}.
 \tag{2}
\]
In particular it remains valid without specifying dyadic sizes
for either \(r,t\). The same bound holds with the marked side
interchanged.

Here are the exact changes in
[FavorableRankSixHyperbolaNeck.md](FavorableRankSixHyperbolaNeck.md).
Use the real congruence \(r t\equiv N\overline{s u}\bmod G\) and
\(p=(N-s u r t)/G\). The barred argument is a unit on the actual
support: \(sG\) are coprime there, and \(u\) and the annulus primes
are smaller than every prime in \(G s\).
On a rectangle at \(R_1,R_2\) with \(R_1R_2\asymp x/(s u)\),
small-modulus residue classes modulo \(d\) of \(r,t\) now have
steps \(a d,d\) respectively. Both steps are units modulo \(G\).
They preserve the restricted nonzero Fourier bounds in the
hyperbola completion, also when a box is longer than \(G\).
For each CRT pair the double-zero main is
\(\phi(G)R_1R_2/(G^2 a d^2)\), understood with the exact interval
lengths in place of \(R_j\).
Summing over the prohibited residue pairs modulo \(d\) puts the
same \(d^2\sqrt G\) in the Weil error, and replaces the axial
error by \(d(R_1/a+R_2)/G\), up to log powers.
Integers \(a\) are all coprime to the actual sieve moduli
\(d\) here, by prime sizes.

At a small sieve prime \(\ell\), if \(\ell\nmid Nu\) the
three-condition local density is \((3\ell-2)/\ell^2\).
If \(\ell\mid Nu\) it is instead \((2\ell-1)/\ell^2\).
When \(\ell\mid u\), the actual \(p\) is automatically nonzero
modulo \(\ell\) because \((u,N)=1\), so only the two coordinate
axes are excluded. When \(\ell\mid N\) and \(\ell\nmid u\),
the third condition equals the axes.
Thus the exact singular comparison has \(\mathfrak S(Nu)\)
in place of \(\mathfrak S(N)\).
Use the Selberg level \(D_0=x^{\gamma/20}\) and all sieve primes
\(\le D_0^{1/2}\). That upper comparison gives logarithmic
factor \(O(\mathfrak S(Nu)/(\gamma L)^3)\).
This is the same dimension-three Selberg denominator proof,
uniform for the polynomial \(Nu\).

The double-mode Weil reserve is at least
\(.0037-\kappa-c_1-3\gamma/20>.0026\) before harmless log losses.
For the axes, in the marked case \(R_1/a\gg x^{\kappa/4-c_1}\)
and \(R_2\gg x^\gamma\). In the unmarked case both
\(R_1,R_2\gg x^\gamma\). Consequently the axis errors after
summing through \(D_0\) save \(\exp(-c\gamma L)\)
relative to \(R_1R_2/(G a)\), sufficient for any log reserve
through the stated range. This proves the per-box upper
\(O(\mathfrak S(Nu)R_1R_2/(aG(\gamma L)^3))\).
There are \(O(L)\) choices of the first dyad and \(O(1)\)
second dyads per first choice, and the actual weight is
\(O(L)\). Their sum proves (2), including its true
\(1/(sG u a)\) factor.

## 2. Exact small core and its Fourier harmonic weight

For each \(q\), define its full core \(u_\gamma\) as the product of
all prime powers in \(q\) with prime base \(\le x^\gamma\).
Thus \(q=u_\gamma v\), \((u_\gamma,v)=1\), and
\(v\) is \(x^\gamma\)-rough. This is an **exact** factorization.
For real Fourier variable \(y\) put
\[
 w_y(u)=\prod_{\ell\mid u}\min(2,|y|\log\ell/L),\qquad w_y(1)=1.
\]
By Fourier inversion, for each divisor \(r\mid v\),
\[
 \left|\sum_{d\mid u_\gamma}
            \mu(d) f\bigl(\log(dr)/L\bigr)\right|
       \le \int_\mathbb R |\widehat f(y)|w_y(u_\gamma)\,dy
       =J_f(u_\gamma).
 \tag{3}
\]
The normalization of \(\widehat f\) is chosen for
\(f(t)=\int\widehat f(y)e^{iyt}\,dy\).
The factorization in (3) is
\(\prod_{\ell\mid u_\gamma}(1-e^{iy\log\ell/L})\);
it remains exact for squareful \(u_\gamma\) because \(\mu\)
only uses each prime base once. In particular all
decay estimates in \(y\) can use rapid Fourier decay, not
bounds for a growing number of derivatives of \(f\).

If \(u_\gamma\le x^\kappa\), the divisor \(r=v\) gives zero:
\(\log_xv>.8\), above the support of \(f\).
The divisor \(r=1\) is zero unless \(u_\gamma=1\):
all its short terms have \(f=1\) and their complete Möbius
sum vanishes. Thus bounds for (3) summed over **proper**
\(r\mid v\) suffice. If \(u_\gamma=1\) and \(v\) is composite,
the leftover \(r=1\) term can be counted by any one of its
proper splits, with another factor at most 2 in the upper.
If \(v\) is prime and \(u_\gamma>1\), both terms are zero.
If \(q\) itself is prime then \(C_f=0\) exactly.
The proper prime powers in \(\Lambda(q)/\log q\) have power-small
mass by their elementary count, so the absolute calculation
may use \(|D_f|\) on the composite inputs only.

Two harmonic estimates will be used. Write
\(R(u)=\prod_{\ell\mid u,\ \ell>2}(1+1/(\ell-2))\), so that
\(\mathfrak S(Nu)/\mathfrak S(N)\le R(u)\).
For odd \(u\) supported on primes \(\le x^\gamma\) and
\(\sigma=0\) or \(1/(\gamma L)\),
\[
 \sum_u \frac{R(u)w_y(u)}{u^{1-\sigma}}
           \ll (2+\gamma |y|)^C.
 \tag{4}
\]
If one requires moreover that \(u\) have a prime
\(\le x^\delta\), with \(\delta\le\gamma\), the right-hand side
gains a factor \(O(|y|\delta)\).
For (4) use the direct Euler product. Each \(p\)-factor is
\(1+R(p)w_y(p)/(p^{1-\sigma}-1)\), and the denominator is
\(\gg p\), uniformly since \(p^\sigma\le e\) and
\(\sigma=o(1)\) through the given \(\gamma\)-range.
The log of the product is
\[
 \ll\sum_{p\le x^\gamma}
       \frac{\min(2,|y|\log p/L)}p
 \ll\log(2+\gamma|y|).
\]
For the last inequality split at \(e^{L/|y|}\), and use the
prime harmonic and the logarithmically weighted prime harmonic
estimates. If \(y=0\) the bound is immediate.
The extra prime condition is charged to one prime factor
and costs \(\ll |y|\sum_{p\le x^\delta}\log p/(pL)
\ll |y|\delta\).
Thus integrating (4) against \(|\widehat f(y)|\) makes the
unrestricted harmonic mass \(O_f(1)\) and the tiny-prime
mass \(O_f(\delta)\).
By Rankin with \(\sigma=1/(\gamma L)\), the same estimates
restricted to \(u>x^{\kappa/2}\) gain \(e^{-\kappa/(2\gamma)}\).

## 3. Exhaustive level selection with an annulus count

Take \(\gamma_j=2^{-j}\gamma_0\) and let \(J\) be the first index
with \(\gamma_J\le C_0/\log L\), so
\(\gamma_J>C_0/(2\log L)\) for all large \(x\).
Take \(C_0>0\) sufficiently small depending on the desired log error
reserve \(A\). Discard the inputs with a repeated prime base
\(>x^{\gamma_J}\); the number of candidate \(q\asymp x/s\)
is \(O((x/s)x^{-\gamma_J})\), by summing reciprocals of squares.
Global divisor moments after summing \(s\) pay the
\(O(L)\) weights and \(|D_f(q)|\ll_f \tau(q)\), so this
is negligible with all log reserves. Repetition within the
final small core remains allowed and is already accounted for
in (3), (4).

Also discard \(q\) for which \(u_{\gamma_J}>x^\kappa\).
The unrestricted count of such \(q\)'s is at most \(x/s\)
times the harmonic tail over \(u>x^\kappa\) fully supported
below \(z=x^{\gamma_J}\). Rankin at \(1-1/\log z\) gives
\[
 \sum_{\substack{u>x^\kappa\\P^+(u)\le z}}\frac1u
    \ \ll\  e^{-\kappa/\gamma_J}\log z.
\]
Indeed \(\prod_{p\le z}(1-p^{-1+1/\log z})^{-1}\ll\log z\)
by ordinary Mertens and
\(\sum_{p\le z}(p^{1/\log z}-1)/p\ll1\).
The integer count \(\lfloor x/(su)\rfloor\le x/(su)\)
uses no progression precision. Since \(C_0\) can be made small
depending on \(A\), divisor moments and Cauchy pay all
pointwise divisor costs and make the discarded contribution
\(O_A(xL^{-A})\). This estimates a true floor, not a
model for the small core.

On the remaining physical support choose the **first** level \(j\)
with \(u_j=u_{\gamma_j}\le x^\kappa\).
At \(j=0\), if \(P^-(q)\le x^\delta\) then this prime belongs
to \(u_0\). Equations (2)–(4), the proper-divisor rule,
and the bounded outer harmonic \(\sum_{s,G}1/(sG)\)
give \(O_{\eta,f}(\delta\,\mathfrak S(N)x/L)\), since
\(\gamma_0\) is a fixed absolute constant.

For \(j\ge1\) we have \(u_{j-1}>x^\kappa\).
If \(u_j>x^{\kappa/2}\), use the exponential tail in §2.
Otherwise, the prime labels of the annulus
\((x^{\gamma_j},x^{\gamma_{j-1}}]\) outside \(u_j\)
have product \(>x^{\kappa/2}\). They are distinct on the
retained support. For every proper split of \(v=q/u_j\)
at least one factor has annulus prime product \(>x^{\kappa/4}\).
It has at least \(M=\lfloor\kappa/(4\gamma_{j-1})\rfloor\)
such prime labels. Mark every \(k\)-subset of these otherwise
preserved labels, where \(k=\lfloor c_1/\gamma_{j-1}\rfloor\);
then the marked product \(a\le x^{c_1}\), and we can
divide the resulting upper sum by \(\binom{M}{k}\).
There are two choices of marked side and it meets the
\(x^{\kappa/4}\) condition in (2).
For independently summed possible marks the harmonic cost is
bounded by
\[
  \binom{M}{k}^{-1}
   \sum_{\substack{a\text{ product of }k\text{ distinct}\\
                    \text{annulus primes}}}\frac1a
 \ \le\ (2C/M)^k
 \ \ll e^{-c/\gamma_j}.
 \tag{5}
\]
Here the annulus prime harmonic is bounded by an absolute \(C\)
(e.g. \(C=2\) for large \(x\)), uniformly down to the given
\(\gamma_J\), by Mertens. We used
\(\binom{M}{k}\ge (M/2)^k/k!\) since \(k\le M/2\).
The stated numerical constants ensure \(M\gg C\) and
\(k\gg1/\gamma_{j-1}\) over every level \(j\ge1\).
No sifting at an annulus prime is imposed: its role is actual
divisibility of a factor, and it is above all sieve primes.

In either \(j\ge1\) subcase the remaining layer has the upper
factor \(O_{\eta,f}(\gamma_j^{-3}e^{-c/\gamma_j})\) after
summing fixed \(u_j\) and the optional marks, times
\(\mathfrak S(N)x/L\).
If \(\gamma_j\ge\delta\), keep the marked tiny-prime condition on
\(u_j\) in (4), gaining a multiplicative \(\delta\) even with the
Rankin tail. If \(\gamma_j<\delta\), no such condition is
assumed on \(u_j\); their total exponential tail as \(j\) varies
is \(O(e^{-c'/\delta})=O(\delta)\).
The other layer factors have a convergent geometric-level sum.
This proves (1) with the announced constants.

The estimate applies to a fixed high smooth function \(f\).
Its constant is not stated to be uniform as the width of a
transition of \(f\) tends to zero. Thus one may take \(\delta\)
small *after* fixing \(f\), but the estimate does not itself
supply an estimate uniform in a sharp-cut limit or a
global bound on the polynomially rough residual.

**Dated comparison.** [Granville–Koukoulopoulos–Maynard](https://dms.umontreal.ca/~koukoulo/documents/publications/sieveweights.pdf) use smooth Möbius divisor weights and Rankin truncations in one-variable moment problems; [Pham, October 30, 2026 v1](https://www.preprints.org/manuscript/202610.3061) treats another rough comparison. This argument combines the exact moving reflected equation, the modular hyperbola upper estimate, and marked annulus counts. The displayed absolute loss is restricted to a fixed smooth weight on the specified rank-six rows, not a new signed Goldbach estimate.
