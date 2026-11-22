# A whole-rank tail for the actual fixed-target even-divisor cusp

Let \(N=2x\) be even, \(L=\log x\), \(\ell=\log L\),
\(w=\ell^{-1}\), \(W=x^w\), and \(J=xJ_0\) for a fixed
nonempty interval \(J_0\subset[1,3/2]\). Write \(P=N-y\)
and always weight its genuine prime values by \(\log P\).
Use the usual positive Goldbach singular factor
\[
 \mathfrak S(N)=2\prod_{r>2}\left(1-\frac1{(r-1)^2}\right)
                    \prod_{\substack{r\mid N\\r>2}}\frac{r-1}{r-2},
\]
where products are over primes. Put \(T_y=\log y/L\);
for genuine squarefree \(y\) define its symmetric divisor cusp
\[
 F(y)=\sum_{d\mid y}\mu(d)
                      \left|\frac{\log d}{L}-\frac{T_y}{2}\right| .
\tag{1}
\]
This cusp vanishes identically on odd \(\omega(y)\).

**Theorem.** With \(\mathcal G_J(N)\) the genuine ordered
prime-pair weight \(\sum_{P+y=N,\ P,y\ {\rm prime},\ y\in J}
\log P\log y\), one has uniformly in the even target
\[
 \mathcal G_J(N)=2|J|\mathfrak S(N)
    -\sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
               y\ {\rm squarefree},\ P^-(y)>W,\ \omega(y)\ {\rm even}}}
                  \log P\,L\,F(y)
    +O_{J_0}\!\left(x\mathfrak S(N)\ell^{-(3/2-\sqrt2)/4}\right).
\tag{2}
\]
There are absolute fixed \(c>0\) and \(K_0\) such that, for
\(K_0\le K\le\ell\), the genuine high-rank part satisfies
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
                y\ {\rm squarefree},\ P^-(y)>W,\ \omega(y)>K}}
                  \log P\,L\,|F(y)|
       \ll_{J_0} x\mathfrak S(N)e^{-cK}.
\tag{3}
\]
Thus the remaining sign problem in (2) can be restricted to a
finite number of actual even factor ranks, with arbitrarily
small absolute tail at its natural scale. No uniform upper
bound below \(2|J|\mathfrak S(N)\) for that low-rank signed
sum is proved here. In particular this is not binary Goldbach,
and its reference is not the reference of a different
all-small-completed score.

### Relation to earlier reductions

The kernel itself, its odd-parity cancellation, and its good
rank-four sign are not new: on the even squarefree rows of
[SymmetricParityReduction](../SymmetricParityReduction.md) its
kernel is exactly \(K(y)=-L F(y)/2\). That result obtains a
whole-interval reference by moving a near-root fixed cutoff
with a separate arithmetic estimate. The
[FixedPowerStoppingSieve](../FixedPowerStoppingSieve.md)
already gives unconditional absolute relative control when
deleting small least primes, as well as a smooth transition
estimate. It uses a different global stopping rule based on
the accumulated *small*-prime product and already uses the
\(\sqrt2\) balance in Euler Cauchy. The related
[ExponentialEvenTail](../ExponentialEvenTail.md) proves an
exponentially small tail after \(\limsup_{N\to\infty}\) for
each fixed rank threshold, for all reflected prime rows and
with the stronger stated fixed-threshold exponent \(0.0154\).
The present contribution is a separate direct proof on the
central \(x^{1/\ell}\)-rough rows, using the *global largest*
actual prime and an exact log mark of another factor. It gives
one quantitative inequality uniform also for moving
\(K\le\ell\) and a direct transition from a genuinely
sub-square-root gap of width \(gL\asymp\ell^{-1/4}L\),
where ordinary BV applies, to the exact own root. No
improvement to the earlier full-interval or fixed-rank
limsup constant is claimed.

## 1. The true largest-prime mark

The following exact device is used before taking any absolute
values within a subset sum. Take a family \(f_T\) on \([0,T]\)
with \(f_T(T-u)=s f_T(u)\), \(s\in\{1,-1\}\), and
\(f_T(0)=0\). On squarefree \(y\) write \(T=T_y\), and
\(q\) for its **globally largest true prime**. For \(R=y/q\),
separating the \(q\)-bit and then complementing divisors of \(R\)
gives the literal identity
\[
 \sum_{d\mid y}\mu(d) f_T(\log d/L)
     =(1+s\mu(y))\sum_{d\mid R}\mu(d) f_T(\log d/L).
\tag{4}
\]
Indeed the translated \(q\)-bit sum is
\(s\sum_{d\mid R}\mu(d)f_T(\log(R/d)/L)
=s\mu(R)\sum_{d\mid R}\mu(d)f_T(\log d/L)\)
with \(\mu(R)=-\mu(y)\).
For \(h_T(u)=f_T(u)/u\), the log-mark identity on the right is
\[
 \sum_{d\mid R}\mu(d) f_T(\log d/L)
    =-\sum_{p\mid R,\ p\ {\rm prime}}
       u_p\sum_{A\mid R/p}\mu(A)h_T(u_p+\log A/L),
       \qquad u_p=\log p/L.                            \tag{5}
\]
This is just \(\sum_{p\mid d}u_p=\log d/L\) at each \(d\ne1\);
the \(d=1\) term is zero by hypothesis. The \(q\)-mask is
global, not a largest-prime condition on any particular
divisor allocation. Consequently **every** remaining label
is free in the complete signed subset sum (5).

For (1), subtract \(T/2\) from the cusp kernel, which does not
alter the full sum for any \(y>1\). Then
\[
 f_T(u)=|u-T/2|-T/2,\qquad
 h_T(u)=
   \begin{cases}-1,&0\le u\le T/2,\\1-T/u,&T/2<u\le T.
   \end{cases}
\tag{6}
\]
Use the same formulas extended slightly beyond this range
and a fixed smooth compact cutoff equal to 1 on \([0,1.1]\).
The \(h_T\) so extended have uniformly bounded Lipschitz norms,
\(\|h_T-h_1\|_\infty\ll |T-1|\), and second distributional
derivatives of bounded total mass, so
\(|\widehat h_1(\xi)|\ll(1+|\xi|)^{-2}\).
The one-sided derivative jump at \(T/2\) is allowed.

We will also use the two kernels, for \(U=\ell^{-1/4}\),
\[
 f^{+}_{T,U}(u)=|u-T/2|\psi((u-T/2)/U),\qquad
 f^{-}_{T,U}(u)=(T/2-u)\psi((u-T/2)/U),                  \tag{7}
\]
where \(\psi\) is fixed smooth, even, equals 1 on \([-1,1]\)
and zero outside \((-2,2)\), and is nonincreasing on the
nonnegative axis. They vanish near \(u=0\).
The functions \(h=f/u\), extended by zero away from
the center, have the same uniform Lipschitz and moving-\(T\)
bounds, and
\[
     |\widehat h_{1,U}^{\pm}(\xi)|
                  \ll_\psi \min(U^2,(1+|\xi|)^{-2}).
\tag{8}
\]
Their mass is \(O(U^2)\); their second derivative measure
has total mass \(O_\psi(1)\), including the cusp jump in the
even case. Equations (4)--(5) apply unchanged to both.

## 2. Genuine fixed-target angular upper

Take the absolute value of the complete sums in (5), only
then use the triangle over the marked prime \(p\). On a
true row now put \(S=y/(p q)\), a squarefree product of
remaining rough primes. Split \(q\) by exponent intervals
\(\beta\le u_q\le2\beta\), using \(\beta=w2^j\) up to
the physical endpoint \(1+O(L^{-1})\); include any common
boundary once. All genuine \(p\) and factors \(r\) of \(S\)
lie between \(W\) and \(x^{2\beta}\). If
\(\beta\le1/8\), then \(S\ge x^{1-4\beta}\) on the true
support. Thus in a positive harmonic upper one may insert
a factor
\[
 e^{-1/(2\beta)}S^{1/(\beta L)}.
\tag{9}
\]
This is at least 1 on that support. For \(\beta>1/8\)
use no tilt; the exponential factor in estimates below may
still be written \(O(e^{-1/(2\beta)})\), with an absolute
constant.

Fix exact \(p,S\) before counting \(q\).
Its two genuine prime forms are \(q\) and \(N-pS q\),
on an interval \(q\asymp Y=x/(pS)\), with \(q\ge x^\beta\).
If \(P\mid N\), there are \(O(1)\) such primes in the
central range and their divisor-power weights cost at most
\(x^{o(1)}\); otherwise the true \((pS,N)=1\) is retained.
The elementary [two-form Selberg upper](../wide_gap_safe_bank_packet/Proof.md)
with \(z_0=x^{\beta/50}\), \(R=x^{\beta/10}\),
sieving both prime forms, gives
\[
 \#\{q,\ N-pS q\hbox{ both prime on the actual support}\}
       \ll \beta^{-2}\frac{Y\mathfrak S(N)}{L^2}
                                      +x^{.6\beta}.       \tag{10}
\]
Indeed Markov in the Selberg normalization keeps an
absolute fraction since the expected logarithm is
\(2\sum_{r\le z_0}(\log r)/r\le .05\beta L\);
the square-weight floors cost \(R^6\).
At primes dividing \(N\) the roots coincide, at primes
dividing \(pS\) only the first form has a root, and elsewhere
there are two distinct roots, with the usual parity at 2.
The slope factors are all \(>W\), and their local correction
is \(1+o(1)\) uniformly by \(\sum_{r\mid pS}1/r=o(1)\).
Both true prime forms exceed \(z_0\). These checks are
uniform for all \(\beta\ge w\), even the smallest dyad.
The floors are summed **before** relaxing
\(H=pS\le1.5x^{1-\beta}\); splitting a fixed \(H\)
into \(p,S\) and bounding the full subset envelope
costs only a fixed divisor power of \(H\). For this dyad
the resulting floor, including both log factors, is
\(O(x^{1-.4\beta}L^C)\) with fixed \(C\). Summing
\(O(\log(1/w))\) dyads still saves every fixed log power.

In the main of (10), the real log mark cancels the prime
harmonic denominator: \(u_p/p\) has limiting measure \(du\)
when \(u=\log p/L\). More precisely, prime Mertens with log
weight starting at \(W\) gives through partial summation
an angular \(du\)-integral on \(w\le u\le2\beta\), with
error \(O(e^{-c_1\sqrt{wL}}L^C)\) times sup and total
variation of the integrated weight. In the actual
coefficient first replace \(T_y\) by 1: (6)--(7) have
Lipschitz error \(O(1/L)\), so each complete difference has
error \(O(2^{\omega(S)}/L)\). After this replacement
the absolute profile as a function of \(u\) has sup and
variation \(O(2^{\omega(S)})\), by summing the Lipschitz
bound over the actual subset shifts. The same estimate
controls moving prime-prefix endpoints. All such errors
against \(1/S\) sum to \(O(L^{-1/2})\) after the local
factors of (10): even with (9) the available positive
Euler harmonic with \(2^{\omega(S)}\) is
\(O(w^{-C'})\) with fixed \(C'\). The \(T\)-replacement
occurs after all actual labels have been named, so it
does not move the maximum-prime condition or a divisor
membership test in (4)--(5).

In particular, apart from negligible errors, the absolute
true weighted contribution of any of these families,
with a restriction \(\omega(S)\in\mathscr R\) if desired,
is bounded by \(x\mathfrak S(N)\) times a sum over \(\beta\)
of a constant multiple of
\[
 \beta^{-2} e^{-1/(2\beta)}
 \sum_{\substack{P^-(S)>W,\ P^+(S)\le x^{2\beta}\\
                  S\ {\rm squarefree},\ \omega(S)\in\mathscr R}}
    \frac{a_\beta(S)}{S}\,
       \big\| \Delta_S h_1\big\|_{L^1([w,\,2\beta])}.
\tag{11}
\]
Here \(\Delta_S=\prod_{r\mid S}(1-\tau_{u_r})\), with
\(\tau_h f(u)=f(u+h)\), and \(a_\beta(S)=S^{1/(\beta L)}\)
for \(\beta\le1/8\), 1 otherwise. Product and maximum-prime
constraints have been relaxed only at the positive
majorant stages just stated. In particular (11) does not
replace a true prime by a smooth density in a signed sum.

## 3. Harmonic weighted Cauchy on the actual subset differences

We give a uniform band bound for (11). Fourier transforms
use \(e^{2\pi i \xi u}\); harmless absolute constants do not
depend on \(w,\beta\) or the number of true labels.
At a dyadic frequency \(X\ge1\) take
\(X\le|\xi|\le2X\). Spatial \(L^1([w,2\beta])\) is
bounded by an absolute constant times spatial \(L^2\).
By Plancherel the band norm for \(S\) is bounded by
\[
 \sup_{|\xi|\asymp X}|\widehat h_1(\xi)|
 \left(\int_{X\le|\xi|\le2X}
          \prod_{r\mid S}|1-e^{2\pi i\xi u_r}|^2d\xi\right)^{1/2}.
\tag{12}
\]
Assign \(c_r=Xu_r\) for \(u_r<1/X\), and \(c_r=\sqrt2\)
otherwise, and write \(c(S)=\prod_{r\mid S}c_r\).
Cauchy over \(S\) with weights \(a_\beta(S)/S\), multiplying
its first factor by \(c(S)\) and dividing its second by
\(c(S)\), separates the two nonnegative Euler expansions.
The first has prime coefficient \(a_\beta(r)c_r\); the
second at frequency \(\xi\) has
\(a_\beta(r)|1-e^{2\pi i\xi u_r}|^2/c_r\).

For \(u_r<1/X\) both prime sums after division by \(r\)
are \(O(1)\), by \(|1-e^{2\pi i\xi u_r}|\ll Xu_r\)
and the log-weighted prime harmonic. For \(u_r\ge1/X\),
the first coefficient without the tilt is \(\sqrt2\)
and the second is \(\sqrt2(1-\cos(2\pi\xi u_r))\).
The prime harmonic of this cosine is \(O(1)\) uniformly
for \(1\le X\le L^{100}\): the continuous integral over
\(\max(w,1/X)\le u\le2\beta\) of
\(\cos(2\pi\xi u)\,du/u\) is \(O(1)\) by integration
by parts since \(|\xi|u\ge1\), and the prime Mertens
Stieltjes error here saves all powers of \(L\)
even after the \(O(X)\) variation cost.
Using the positive tilt changes either sum by \(O(1)\):
the untilted coefficients used there are bounded, and
\[
 \sum_{W<r\le x^{2\beta}}
       \frac{r^{1/(\beta L)}-1}{r}
 \ll \frac{1}{\beta L}
            \sum_{r\le x^{2\beta}}\frac{\log r}{r}\ll1.
\]
Each expansion thus has total mass
\[
                  O((1+\beta X)^{\sqrt2}).               \tag{13}
\]
The same argument for \(|\xi|\le1\) uses \(c_r=u_r\)
and yields constant bounds.
For \(X>L^{100}\), ignore cosine cancellation;
the trivial positive harmonic bounds give \(O(w^{-C})\)
for both expansions in place of (13).
This remote part will be negligible by the Fourier decay.

Combining (12)--(13) bounds each band of the harmonic
angular sum by
\[
 \ll \sup_{|\xi|\asymp X}|\widehat h_1(\xi)|
                         X^{1/2}(1+\beta X)^{\sqrt2}.
\tag{14}
\]
For the full cusp, the exponent at large \(X\) is therefore
\(-\delta\), \(\delta=3/2-\sqrt2>0\).
The dyadic series is summable uniformly in \(\beta\).
The remaining sum \(\sum_\beta \beta^{-2}e^{-1/(2\beta)}\)
is uniformly bounded; this is the reason for the actual
largest-factor tilt (9). Thus all factors and cutoffs in
(11) have a fixed absolute cost at the natural scale.

For ranks \(\omega(y)>K\) the actual \(S\) in (5) has
\(\omega(S)>K-2\). In either positive expansion, for
\(X\le e^{K/100}\) the sum of its prime terms before
exponentiating is at most \(C+\sqrt2\log(1+X)\le .03 K\)
once \(K\ge K_0\). The mass at \(\omega(S)>K-2\) is
therefore bounded by the tail of
\(\sum_j(.03K)^j/j!\), which is \(O(e^{-c_2 K})\).
Apply this inside the same Cauchy estimate for these
frequencies; the high-frequency part
\(X>e^{K/100}\) is \(O(e^{-\delta K/100})\) by
(14). The remote frequency estimate and the true counting
errors \(O(L^{-1/2})\) are smaller, uniformly for \(K\le\ell\).
This proves (3), with for instance a smaller absolute
\(c>0\) than \(\delta/100\).
For (7), use (8) in (14) and split bands at \(X=1/U\);
the sum is \(O_\psi(U^\delta)\).
By (4)--(11), both center-bump sums therefore admit the
uniform **actual** bound
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
                  y\ {\rm squarefree},\ P^-(y)>W}}
       \log P\,L\,\left|\sum_{d\mid y}\mu(d) f_{T_y,U}^\pm
                                             (\log d/L)\right|
                  \ll_{\psi,J_0} x\mathfrak S(N) U^\delta .
\tag{15}
\]

## 4. Direct centered calibration and literal parities

There is no need to use an auxiliary all-small completion
to obtain (2). For \(y>1\) its complete centered Möbius
logarithm identity is
\[
    \Lambda(y)=
       \sum_{d\mid y}\mu(d)(\log(y/d)-\tfrac12\log y),     \tag{16}
\]
since the added constant multiplies \(\sum_{d\mid y}\mu(d)=0\).
Use the literal rough restriction \(P^-(y)>W\), which retains
every true prime \(y\) under consideration. Proper powers
and nonsquarefree rough rows cost \(O_A(xL^{-A})\)
with their fixed divisor-power bounds, as in the
[wide-gap calibration](../wide_gap_all_terminal/Proof.md).
Average the true short cutoff
\(d\le\sqrt y\,x^{-g}\) over \(g\in[U,2U]\) with survival
function \(\psi(t/U)\). The actual weighted short term in
(16) is
\[
                       |J|\mathfrak S(N)+O_A(x\mathfrak S(N)\ell^{-A}).
\tag{17}
\]
To verify it use the same argument as for the short branch
in the [smoothed-gap calibration](../smoothed_gap_two_macro/Proof.md):
open the rough quotient by dimension-one fundamental
lemma at \(x^{g/2}\), ratio \(g/(2w)\gg\ell^{3/4}\),
giving exactly \(dh\le\sqrt{1.5x}x^{-g/2}\) under maximal
weighted ordinary BV at the actual reduced residue \(N\).
The raw coefficient here differs only by a smooth factor
\(-\tfrac12\log y\); partial summation still applies.
For the signed harmonic cumulative \(\rho_w\),
the short main divided by \(L\) at \(y,g\) is
\[
      g\,\rho_w(D_y)+\int_0^{D_y}\rho_w(u)\,du,\qquad
      D_y=T_y/2-g.
\]
Its first term and missing tail save all powers of
\(1/\ell\), and \(\int_0^\infty\rho_w=e^\gamma w\).
The true singular normalization is
\(V_N(W)L=\mathfrak S(N)e^{-\gamma}/w\) to the same accuracy.
This proves (17) with the exact real \(P\) and moving cutoff.
Equalities in \(g\) are of measure zero in the actual
averaging.

For a short complementary pair \(d<\sqrt y,v=y/d\), let
\(t=T_y/2-\log d/L>0\). The long remainder of (16) at the
own root is \(-\mu(v)tL\). The averaged long remainder at
the actual short cutoff is this same term plus
\(\mu(d)tL\psi(t/U)\). Sum the latter over all literal
short \(d\). On even total rank it is half the full
\(f^+\)-subset sum in (15), and on odd total rank half the
full \(f^-\)-subset sum: complement multiplies \(\mu(d)\)
by \(\mu(y)\), and the parity of the respective kernel
matches it. Its absolute weighted cost is consequently
\(O_{\psi,J_0}(x\mathfrak S(N)U^\delta)\).

For odd total rank the own-root remainder summed over the
short pairs is exactly \(\Lambda(y)/2\) by (16):
\(\mu(v)=-\mu(d)\) and the two complementary terms of
the full centered identity equal each other. This includes
the genuine prime \(y\), for which \(d=1\) contributes
\(\tfrac12\log y\); it gives zero on odd composite
squarefree \(y\). For even total rank it is exactly
\(-\tfrac12 L F(y)\), since \(\mu(v)=\mu(d)\) and the
symmetric full cusp counts each pair twice.
All pairs are distinct since \(y>1\) is squarefree.
Substitute these literal identities and (17) into (16),
and move \(\tfrac12\mathcal G_J(N)\) to the left.
This proves (2) with \(U=\ell^{-1/4}\) and the stated signs.

For example the true semiprime contribution in the
remaining even sum is positive:
\(F(pq)=2\log p/L\) for genuine \(p<q\). Estimate (3) does
not bound this contribution or prove its compensation
by other actual even ranks. Reducing the rank tail on
the genuine prime leg does not replace the remaining
low-rank signed comparison by an average over targets,
a sole factor distribution, or a Goldbach proof.

See [check.py](check.py) for an exact rational replay of the
largest-prime mark, both gap parities and the remaining
finite-difference identities. The test has synthetic log
profiles, not a hypothesis on their physical occurrence.
