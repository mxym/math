# Two genuine all-rank signed shoulders for the completed direct score

This note uses the **all-small-subproduct completed** direct score in
Section 4 of the [many-small renormalization](../direct_many_small_renormalization/Proof.md), not
the original fixed-payer score and not any shared-index proxy. It gives
a uniform signed \(o(x\mathfrak S(N))\) bound on two disjoint actual
near-root divisor sectors. It does not infer a natural-scale bound
for the other sectors or replace a prime-pair lower bound.

Let \(N=2x\) be even, \(L=\log x\), \(\ell=\log L\),
\(J=xJ_0\subset[x,1.5x]\) for a fixed nondegenerate interval \(J_0\),
\(P=N-y\), and \(C_y=y/x^{1-\epsilon}\) with a fixed \(0<\epsilon<.005\).
The partner roughness is \(z=x^\chi\) with
\[
                   \ell^{-2}\le\chi\le\ell^{-1}.
\]
Let \(R_z(n)=1_{P^-(n)>z}\), and \(\mathfrak S(N)\) be the usual
positive Goldbach singular factor in the [thin gap](../thin_true_giant_gap/Proof.md).
The symmetric gap parameter \(\delta>0\) may be any function tending
to zero. Its cutoffs are \(R_\pm(y)=\sqrt y\,x^{\pm\delta}\).
In the all-completed score use free weights
\(\mu_2(c)1_{P^+(c)<C_y}\) for every \(c\mid y\); there is no payer.
The raw term is \(\sum_{r\mid y,r>R_-}\mu(r)\log(y/r)\); the added
free term is \(\sum_{c\mid y,P^+(c)<C_y}\mu_2(c)
\sum_{a\mid y/c,a>R_+}\log(y/(ca))\). Both are multiplied by \(R_z(y)\).
The own-root score sets \(\delta=0\) with exactly the same cofactor weights.

For squarefree \(y\) let \(S_d(y)=\prod_{p\mid d,\ p<C_y}p\).
The exact difference of these scores, off the cutoff equality, is a
sum over the **smaller** actual divisors:
\[
 R_z(y)\sum_{\substack{d\mid y\\x^{-\delta}\sqrt y<d<\sqrt y}}
  \left[\mu(d)\log(y/d)-\mu(S_d(y))(\log d-2\log S_d(y))\right].       \tag{1}
\]
Indeed the gap admits the extra raw term at \(d\), and omits the free
term at its complementary \(a=y/d\). The latter is
\(\sum_{c\mid S_d(y)}\mu_2(c)\log(d/c)
=\mu(S_d(y))(\log d-2\log S_d(y))\) by the zeroth and first subset
moments of \((-2)^{\omega(c)}\). For the strict cutoffs, equality with
\(R_-\) or \(R_+\) is confined to \(O(\sqrt x\,x^\delta)\) physical
\(y\), each determined by the equality divisor. A squarefree macroscopic
\(y\) has no own-root tie.

Define two divisor classes:
\[
\begin{split}
 {\cal A}&=\{d:P^+(d)\le x^{.029}\},\\
 {\cal B}&=\{d:\exists\,p_2\mid d,\ p_3\mid d\text{ genuine primes, }\
              x^{.029}<p_2\le x^{.031},\
              x^{.075}<p_3\le x^{.078}\}.
\end{split}
\]
They are disjoint. In \({\cal B}\) choose the **least** genuine prime
of each band; this does not add multiplicity to a divisor.

**Theorem.** For either \({\cal C}={\cal A}\) or \({\cal C}={\cal B}\),
the signed contribution to (1) after inserting \(d\in{\cal C}\) and
summing on the true prime leg is
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\y\ {\rm squarefree}}}
   \log P\,R_z(y)
   \sum_{\substack{d\mid y,\ d\in{\cal C}\\x^{-\delta}\sqrt y<d<\sqrt y}}
     \left[\mu(d)\log(y/d)-\mu(S_d(y))(\log d-2\log S_d(y))\right]
          \ll_{\epsilon,J_0} x\mathfrak S(N)\delta
                      +O_{A,\epsilon,J_0}(xL^{-A}).                  \tag{2}
\]
The bound also holds separately for the raw and the completed free
bracket in (2). It is uniform in the actual even target and in the
indicated \(\chi\). It is a signed statement about divisor
orientations, not a pointwise cancellation at each integer \(y\).

## 1. Genuine prime progression input on both divisor classes

In (2), keep squarefree \(d\), and first remove the \(P\mid N\)
exceptions (at most \(O(1)\) in \([x/2,x]\)). Their total is
\(x^{o(1)}\) by divisor bounds. Otherwise the fixed \(d\) and
the free complement \(y/d\) are automatically units at \(N\).
Temporarily omit the squarefreeness of y while leaving it on d:
the differing rough \(y\) number \(O(x/z)\), and Cauchy–Schwarz
with fixed divisor moments, using the \(O(L\tau(y))\) score envelope
and \(\log P\), costs \(O_A(xL^{-A})\). Under the same envelope the
cutoff equalities have a power-small cost.

Open \(R_z(y/d)\) via upper and lower dimension-one fundamental-lemma
weights of level \(D=x^{.000005}\), as in [the thin gap](../thin_true_giant_gap/Proof.md).
The exact modulus is \(d h\), \(h\le D\) squarefree and supported on
primes \(\le z\) not dividing \(N\). Since \(d\) is \(z\)-rough, \(dh\)
is squarefree and recovers both \(d,h\) uniquely. The allowed sieve
density is \(1/(p-1)\) on the displayed primes. Its relative error
\(O(u^{-u/2})\) at \(u=.000005/\chi\ge .000005\ell\) saves every
fixed power of \(L\) eventually. The absolute fixed-factor harmonic
\(\sum_{d\le1.5x}R_z(d)/d\ll\chi^{-1}\); both coefficient magnitudes
are bounded by \(O(L)\). Positive upper-minus-lower control then
handles the roughness errors even for the signed bracket. For each
d, the points at which \(S_d(y)\) changes are literal \(p x^{1-\epsilon}\)
for \(p\mid d\), at most \(O(L)\) points. On the intervening
intervals its sign and the free weight are constant, and the first
logarithm can be handled by partial summation. The interval
\(x^{-\delta}\sqrt y<d<\sqrt y\) also restricts y to a single interval.
The corresponding total weight variation in y is \(O(L^2)\).

For \({\cal A}\), choose \(I=\{p\le X^{.03}:p\nmid N\}\) at each
prime-test scale \(X\). In [Polymath's primary v3 paper, Claim 2.3,
Theorem 2.4(i), and Lemma 2.10(iii)](https://arxiv.org/pdf/1402.0811v3)
take \(\varpi=.001\), smoothness exponent \(.03\):
\(600\varpi+180(.03)=6<7\).
Every involved modulus is squarefree with prime factors at most
\(x^{.029}\) for sufficiently large \(x\) and \(\chi\le1/\ell\);
hence it belongs to \(\mathcal D_I^{(4)}(X^{.03})\)
on the relevant scales. There is one **actual integer** residue
\(N\), coprime to \(P_I\) even when it varies with x, not a
different arbitrary large residue in unrelated classes.
The true modulus is \(\le\sqrt{1.5x}\,x^{.000005}\),
below \(X^{.502}\) with fixed room.

For \({\cal B}\), write \(d=p_2p_3 b\) with the two actual least
tags and use modulus slots \((bh,p_2,p_3)\). The d and h
restrictions need not be dropped from the signed main.
For the AP error take its absolute value before extending the
ranges to a full tuple sum as in [Maynard, *Primes in arithmetic
progressions to large moduli III*, Theorem 1.2](https://arxiv.org/pdf/2006.08250).
Choose its fixed parameter \(\delta_0=.00002\).
On each dyad of \(p_2,p_3\), take \(Q_2,Q_3\) at their upper
endpoints and \(Q_1=X^{.50002}/(Q_2Q_3)\). The \(bh\) upper
bound fits this \(Q_1\): the dyadic cost is at most a factor
four, while total true modulus is \(O(x^{.500005})\).
At exponent scales \(\alpha_2\in[.029,.031]+o(1)\) and
\(\alpha_3\in[.075,.078]+o(1)\) the strict source rails are
\[
 40\delta_0<\alpha_2<.05-7\delta_0,\qquad
 .10+12\delta_0-\alpha_2<\alpha_3<.10-4\delta_0-.60\alpha_2 .
\]
For example the lower \(\alpha_3\) rail is at most .07124
and upper is at least .08132. For each \((q_1,q_2)\) the
residue \(b_0=N\bmod q_1q_2\) is independent of the third slot,
and nonunits are omitted. Thus the genuine \(N\)-class has
the source's stated not-fully-arbitrary residue structure.
Given the tuple, at most one squarefree d and h are
reconstructed. No factorability condition on the signed
Möbius coefficient is assumed when using this absolute theorem.

Both inputs give arbitrary-log absolute prime AP errors
uniformly at each fixed prefix \(T\in[x/2,x]\), including
weighted \(\log P\) by partial summation. For MPZ, construct
a prefix from the dyadic intervals
\([T/2^{j+1},T/2^j]\) above \(x/L^M\), where the smoothness
and level comparisons retain the displayed fixed exponent
slack for each fixed M. Omit the tail below \(x/L^M\) using
\(O(L(x L^{-M}/q+1))\) per modulus (and the analogous
principal bound). The sum is negligible after \(M\)
is chosen large, since the harmonic count over moduli (or
the factor triples) is log-bounded, and the extra ones total
at most \(O(x^{.50002}L^{O(1)})\). For MPZ's coprime prime
principal, replacing by the unmasked prime PNT costs at most
\(O(L\omega(q))/\varphi(q)\); standard PNT supplies the
desired main length. Maynard’s PNT main is already written
in terms of all primes. To obtain variable endpoints, use
a grid of \(O(L^B)\) prefixes of step \(\ll xL^{-B}\) in
\([x/2,x]\). For a fixed q, the difference from the nearest
grid point is bounded by the same trivial progression estimate
\(O(L(x L^{-B}/q+1))\). Summing first over moduli (or over
the triples in a dyad) and paying the grid count from a larger
arbitrary-log reserve proves the maximal-prefix form needed
above. We do not posit a given-prime asymptotic on each small box.
There are only log-power many dyads. The argument applies to
actual prime weights by deleting proper powers: at most
\(x^{1/2+o(1)}\) proper powers occur overall, and only a divisor
power many eligible moduli/tuples of \(N-P\) can contribute to
their actual progression terms. Either in the grid argument
or by taking AP errors for the actual prime source directly,
this is negligible.

Consequently the true prime sums become the integrals over y
of their harmonic main, with common factor
\[
 V_N(z)=\prod_{p\le z,p\nmid N}(1-1/(p-1))
     =\mathfrak S(N)V_z(1+O(L/z))\ll\frac{\mathfrak S(N)}{\chi L}.
\]
The original harmonic coefficient \(1/\varphi(d)\) can be
replaced by \(1/d\) at relative cost \(O(L/z)\) pointwise.
Removing the \((d,N)=1\) condition in the harmonic model loses
\(O(L/z)\) times a fixed log-power bound, by opening one prime
\(p>z\) of N. We are left with the original actual harmonic
weights, integrated over \([T_y-\delta,T_y]\) on the geometric
coordinate \(t=\log d/L\), \(T_y=\log y/(2L)\).

## 2. Uniform actual prime harmonic law with a small signed core

For \(\chi\le\ell^{-1}\), write
\(\nu_\chi(dt)=1_{t>\chi}\,dt/t\) on \(t\ge0\).
We will use convolution only locally on \(t\le2\).
If f is a step function taking values \(0,\pm1\) on
a fixed bounded number of intervals (endpoints allowed
to move), a squarefree prime harmonic measure with coefficient
\(\prod_{p\mid b}f(\log p/L)\) and \(P^-(b)>z\) is approximated by
\[
                   \exp^*(f\nu_\chi)
                    =\sum_{j\ge0}(f\nu_\chi)^{*j}/j!.
\]
The error in its cumulative at **every** prefix \(0\le T\le2\)
is \(O_A(L^{-A})\), uniform in f with that interval
bound and in the indicated \(\chi\).
Here are quantitative details. Prime Mertens with its ordinary
PNT error gives
\[
 \sup_{\chi\le a\le b\le2}
  \left|\sum_{x^a<p\le x^b}\frac1p-\int_a^b\frac{dt}{t}\right|
                    \ll \exp(-c\sqrt{\log z})
\]
with suitable absolute \(c>0\); endpoint atoms cost at most \(1/z\).
After imposing any of the finitely many intervals of f this
still holds with the same error up to a fixed factor.
The total variation on \([0,2]\) of either prime measure or its
continuum approximation is \(O(1)+\log(2/\chi)\).
In an ordered j-fold convolution, telescope one slot at a time
at its residual prefix endpoint. Each difference is bounded
by its one-slot cumulative error times \(j\) and the product
of the remaining variation masses, before division by \(j!\).
The exponential sum of these bounds is a polynomial in \(\chi^{-1}\)
times the tiny prime error. The difference between distinct
and unrestricted tuples is bounded by selecting a repeated pair
of prime slots, costing \(O(1/z)\) from \(\sum_{p>z}p^{-2}\), and
again the exponential of the remaining variation mass.
This compares the actual squarefree integer harmonic with
the claimed model, including the atom at 1. It also applies
with an extra marked slot multiplied by a factor t, by partial
summation or the same telescoping with a single \(t f(t)\) measure.
This phase-space approximation makes no assertion about
conditional prime independence on the shifted leg.

The cumulative of \(\exp^*(-\nu_\chi)\) is
\(\rho_\chi(t)=\rho(t/\chi)\) for \(t\ge0\), extended by zero
below 0. This is the ordinary Dickman identity (also proved by
the signed convolution expansion in the
[many-small renormalization](../direct_many_small_renormalization/Proof.md)).
For instance, the Laplace transform of that exponential is
\(\exp(-\int_\chi^\infty e^{-st}\,dt/t)\); its cumulative
solves the Dickman delay equation and is 1 on \([0,\chi]\).
Use \(\int_0^\infty\rho_\chi\ll\chi\) and
\(\rho_\chi(v)\le1/\lfloor v/\chi\rfloor!\).
If \(\beta(dt)=g(t)dt\) vanishes below a fixed positive exponent,
with \(g\) uniformly piecewise \(C^1\) of bounded sup norm and
variation on \([0,2]\), the cumulative of
\(\exp^*(-\nu_\chi+\beta)\) is
\[
             F_\beta(t)=\rho_\chi(t)
                   +\int_0^t \rho_\chi(v)\,h_\beta(t-v)\,dv,
 \qquad h_\beta=\sum_{j\ge1}g^{*j}/j! .                            \tag{3}
\]
The density \(h_\beta\) is bounded on \([0,2]\).
Its terms \(j\ge2\) are uniformly Lipschitz:
\(D(g*g)=(Dg)*g\) is bounded by the variation measure of \(g\)
times its sup norm (extend g by zero outside \([0,2]\)),
and convolve by the remaining \(L^1\)-bounded factors and
sum \(1/j!\). The only possible jumps of \(h_\beta\)
are those of its \(j=1\) term. Thus for \(t\) in a fixed compact
subinterval of \((0,2)\) away from the jumps of g,
\[
 |F_\beta(t)|\ll_\epsilon\chi,\qquad
 F_\beta(t_2)-F_\beta(t_1)
         \ll_{\epsilon} \chi|t_2-t_1|+O_A(L^{-A})                \tag{4}
\]
in absolute value when \(t_1,t_2\) are in the same sufficiently
small such subinterval. Indeed split the integral at small
fixed \(v>0\) so that \(t-v\) remains in a uniform Lipschitz
range. All further \(v\) have factorial decay, as does the
first term \(\rho_\chi(t)\). For \(\chi\le\ell^{-1}\),
a factorial at \(c\ell\) saves every fixed power of \(L\).
Only boundedness, not distance from the jumps, is required for
the first assertion of (4) at \(t\) bounded below away from zero.

One more identity prices the completed logarithm exactly. On
a squarefree \(b\) let \(f=-1\) on allowed primes below \(C_y\)
and \(+1\) on the other allowed primes; zero on the forbidden
primes. The score
\[
 \prod_{p\mid b}f(\log p/L)\,(\log b-2\log S_b(y))
\]
is modeled by marking one genuine prime in b. In the marked
slot its signed coefficient is multiplied by its own sign,
so it becomes \(f(t)^2t\,\nu_\chi(dt)=1_{\mathrm{allowed}}(t)dt\)
and a single factor \(L\). Hence the continuum density for this
mark is \(L\) times the convolution of
\(\exp^*(-\nu_\chi+\beta)\) with Lebesgue measure on the
allowed intervals. On an interval \([a,b]\) its contribution
to that density at \(t\) is
\[
                          L\,[F_\beta(t-a)-F_\beta(t-b)].         \tag{5}
\]
This is a genuine logarithmic coefficient of the completed
orientation. It does not substitute an independent parity
variable for either physical prime factor.

## 3. Applying the harmonic law to the two true sectors

For \({\cal A}\) set \(\kappa=.029\) and
\(\epsilon_y=\log C_y/L\). For the raw Möbius measure use
\(f=-1\) on \((\chi,\kappa]\), zero above, so that
\(\beta=\nu_\kappa\). For the completed free measure use \(f=-1\)
on \((\chi,\epsilon_y)\) and \(+1\) from there to \(\kappa\), giving
\(\beta=2\nu_{\epsilon_y}-\nu_\kappa\) (endpoint prescriptions
are literal in the prior arithmetic measure).
Here \(\epsilon_y=\epsilon+O(1/L)\) and \(\epsilon_y<\kappa\)
eventually. The raw test is linear
\(\log(y/d)=L(\log y/L-t)\) on the interval
\([T_y-\delta,T_y]\). By (4) and partial summation its harmonic is
\(O_\epsilon(L\chi\delta)+O_A(L^{-A})\).
For the free test the allowed mark interval is \([\chi,\kappa]\).
Both arguments of (5) on that integration interval are bounded
below by .45 eventually; therefore (5) has magnitude
\(O_\epsilon(L\chi)\), giving the same \(O_\epsilon(L\chi\delta)\)
bound, with the negligible arithmetic-continuum error from §2.
This estimates the true modeled orientation regardless of rank.

For \({\cal B}\), fix the actual two least tags \(p_2,p_3\);
the rest \(b=d/(p_2p_3)\) is independently forbidden to have
a prime in the portion of either band from its lower endpoint
through the chosen prime, inclusive at the chosen prime.
Thus the two canonical selections become exactly two prohibited
macro-prime intervals in \(b\), with no restriction on its
other factors and no further test involving its product.
Let \(I_{\rm forb}\) denote their union in \(\log p/L\) units
and let \(\nu_{\rm forb}(dt)=1_{I_{\rm forb}}(t)dt/t\).
For the raw coefficient the two tags have \(\mu(p_2p_3)=+1\),
so its remaining signed harmonic has \(\beta=\nu_{\rm forb}\).
For the completed free coefficient both tags are above \(C_y\);
its remaining measure has
\(\beta=2\nu_{\epsilon_y}-\nu_{\rm forb}\).
Their log contribution is the constant mark
\(\log p_2+\log p_3\) multiplying the completed signed
cumulative; all other log terms are (5) with the finitely
many allowed intervals obtained by deleting \(I_{\rm forb}\).
The b exponent interval is the original one translated by
\(-(\log p_2+\log p_3)/L\), hence lies in \([.38,.42]\)
for all large x. Every possible jump of the densities g lies
below .079, and their sup, variation and distance bounds
are uniform in the two real tag values. Formula (4) pays
the linear raw weight and the constant free tag weight,
and (5) pays the remaining free marks: every nonzero argument
\(t-a\) and \(t-b\) occurring at a finite prohibition endpoint
or at \(\chi\) stays \(>.29\); at the terminal allowed endpoint
2 it is negative and \(F_\beta=0\).
Thus each conditional harmonic (before dividing by \(p_2p_3\))
is \(O_\epsilon(L\chi\delta)+O_A(L^{-A})\).
Summing \(1/(p_2p_3)\) costs \(O(1)\) by the genuine reciprocal
prime masses in the two displayed fixed bands. Square factors
at the selected tags were excluded by the same prohibition;
the true squarefree spectrum has not been counted twice.

Finally multiply these harmonic bounds by
\(V_N(z)\ll\mathfrak S(N)/(\chi L)\) and integrate over \(J\).
This proves (2). The proofs of the two sectors use known
distribution inputs at the actual reduced residue, not a new
level of distribution. The complement contains actual
orientations with a giant prime factor near \(x^{.49}\)
and a genuinely attached smaller core, and also rough
multi-prime products that have neither of the two required
bands. The result does not constrain their signed net, nor
does it grant a Goldbach lower bound from the shifted
all-completed score or its distinct calibration.
