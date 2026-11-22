# Natural-scale deletion of a genuine least-factor band

Use the literal *sharply gapped, all-small-completed* score
\(\mathcal R^{\rm all}_{\rm gap}\) of the
[many-small renormalization](../direct_many_small_renormalization/Proof.md),
not the old pair correction with its odd-factor payer.
Thus \(N=2x\) is even, \(L=\log x\), \(\ell=\log L\),
\(z=x^{1/\ell^2}\), \(\delta_x=3\log\ell/\ell\),
\(R_\pm=x^{1/2\pm\delta_x}\), and the central interval
\(J=xJ_0\) has fixed nondegenerate \(J_0\subset[1,3/2]\).
Fix the small-prime exponent \(0<\epsilon<.005\) and put
\(C_y=y/x^{1-\epsilon}\).
The all-small score is
\[
 H_z(y)=1_{\{P^-(y)>z\}}\left[
   \sum_{\substack{r\mid y\\r>R_-}}\mu(r)\log(y/r)
   +\sum_{\substack{csa=y\\a>R_+\\P^+(c)<C_y}}\mu_2(c)\log s
 \right],\qquad \mu_2=\mu*\mu .
\]
All cutoffs, including the moving \(C_y\), will stay exactly
as displayed. Write \(H_W\) for the same arithmetic score with
only the base rough cutoff replaced by \(W\).
Let \(\mathcal G_J(N)\) be the literal logarithmically weighted
Goldbach count on \(y\in J\), and let \(\mathfrak S(N)\) be the
singular factor of the direct identity.

**Theorem.** Put \(Y=x^{1/\ell}\).
Uniformly for \(z\le W\le Y\) and uniformly in the even
target, as \(x\to\infty\) at fixed \(\epsilon,J_0\),
\[
 \sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}\log P\, H_W(y)
 =
 \mathcal G_J(N)+|J|\mathfrak S(N)\,[Q_\epsilon(1/2)-1]
     +o_{\epsilon,J_0}(x\mathfrak S(N)),                       \tag{1}
\]
where the finite positive harmonic mass \(Q_\epsilon\) is
as in the many-small renormalization, Section 4.
Consequently the actual signed score on the entire band
\(z<P^-(y)\le W\) is \(o_{\epsilon,J_0}(x\mathfrak S(N))\).
This conclusion holds also when restricted to squarefree
rows with at least three genuine prime factors below \(C_y\).
No averaging over \(N\), modeled replacement for the
opposite prime, or transfer to an own-root cutoff at
unbounded rank is used. This is a signed removal, not
an assertion of small absolute mass or a Goldbach lower bound.
In particular the surviving \(Y\)-rough rows still require
their true signed comparison with the full explicit calibration.

## 1. The actual moduli at the larger base cutoff

Fix \(W\in[z,Y]\).
First write the raw term as \(1_{\{P^-(y)>W\}}\Lambda(y)\)
minus its sum over \(r\le R_-\). The first expression,
tested against the true prime \(P\), gives
\(\mathcal G_J(N)+O(x^{1/2}L^{O(1)})\), because all true
\(y\) primes in \(J\) exceed \(Y\) and proper prime powers
are negligible.

For the short raw sum keep \(b=r\) fixed and \(W\)-rough.
For the free term keep \(b=cs\) fixed and \(W\)-rough.
The actual free variable is \(a=y/b\).
For this latter term \(a>R_+\) implies
\(b<y/R_+\le1.5R_-\).
Open only \(P^-(a)>W\), using the bounded upper and lower
sieve coefficients from
[Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf)
at level \(D=x^{\delta_x/2}\).
The sieve divisors \(d\) are squarefree and \(W\)-smooth,
so the true prime modulus \(bd\) determines \(b,d\)
uniquely. All actual moduli satisfy
\[
 bd\le1.5x^{1/2-\delta_x/2}
             <\sqrt{x}/L^B
\]
for every fixed \(B\) and sufficiently large \(x\).
Thus the actual reduced residue is \(N\bmod bd\), in
ordinary Bombieri--Vinogradov's range.
The logarithmic weights and the cutoff \(y>bR_+\)
are dealt with by maximal prefixes and partial summation;
each condition \(P^+(c)<C_y\) imposes just one more
moving endpoint. Sum the divisor multiplicities by
\(\tau(b)^{O(1)}\) and use divisor-weighted BV exactly as
in the previous direct identity. Opposite primes dividing
\(N\) cost \(x^{o(1)}\) and may be discarded.
The local factor for the \(W\)-rough free variable is
\[
 V_N(W)=\prod_{\substack{p\le W\\p\nmid N}}(1-1/(p-1)),
 \qquad
 \frac{V_N(W)}{V_W}=\mathfrak S(N)(1+O(L/W)),\quad
 V_W=\prod_{p\le W}(1-1/p).
\]

To handle the signs, apply the upper/lower bracket according
to the sign of each *actual* raw coefficient \(\mu(b)\)
or each actual free coefficient \(\mu_2(c)\). The positive
envelope for the sum of the two approximation errors
uses \(|\mu(b)|\) or \(|\mu_2(c)|\), respectively.
The local dimension-one condition is uniform, since \(2\mid N\)
and prime probabilities are at most \(1/(p-1)\) for \(p\ge3\).
The sieve parameter \(\log D/\log W\) is at least
\((3/2)\log\ell\), so its relative error in either main
is \(\ll \exp(-c\log\ell\log\log\ell)\).
It is essential here to use the *actual harmonic envelope*
instead of a bound growing like a power of \(L\).
Indeed, on \(W\)-rough \(b\), \(1/\varphi(b)=(1+O(L/W))/b\).
Uniformly in \(W\ge z\), Euler products give
\[
 \sum_{\substack{s\le2x\\P^-(s)>W}}\frac1s
       \ll\frac L{\log W},\qquad
 \sum_{\substack{c\le2x\\P^-(c)>W}}\frac{|\mu_2(c)|}c
       \ll\left(\frac L{\log W}\right)^2 .
\]
For the second, \(|\mu_2(p)|=2\), \(|\mu_2(p^2)|=1\),
and higher powers vanish. Since \(V_N(W)\ll
\mathfrak S(N)/\log W\) and the score supplies one
additional factor \(O(L)\), the absolute free model
is \(\ll x\mathfrak S(N)(L/\log W)^4\ll
x\mathfrak S(N)\ell^8\); the raw bound is smaller.
The relative error above therefore costs
\(o(x\mathfrak S(N))\) uniformly.
Switching \(1/\varphi(b)\) to \(1/b\) and dropping the
unit exclusions on primes of \(b\) exceeding \(W\)
also cost \(o(x\mathfrak S(N))\), by the same Euler
majorants after division by a prime of \(N\).
The analytic quantities it remains to evaluate are thus
the raw short model and the free model of the renormalization,
with \(z\) replaced throughout by \(W\).

## 2. Uniform model at \(W\) and exact cutoff preservation

Set \(\sigma=\log W/L\), so
\(\ell^{-2}\le\sigma\le\ell^{-1}\).
The reciprocal-prime measure above \(W\), in variable
\(\log p/\log W\), has prefix discrepancy
\(O(\exp(-c\sqrt{\log W}))\) from \(du/u\) on
\(1\le u\le\log(2x)/\log W\), by the ordinary quantitative
PNT and partial summation.
The total interval mass is \(O(1+\log\ell)\).
By the signed convolution expansion and the global
factorial bounds in Section 4 of the renormalization, the
cumulative rough Möbius model is \(\rho(u)\), with uniform
error \(O(\ell^{O(1)}\exp(-c\sqrt{\log W}))\).
More explicitly, telescope the prime-to-continuum comparison
once in each coordinate of every \(j\)-fold convolution.
The interval condition on that coordinate is a prefix;
after summing the \(j!\) weights the loss is polynomial in
\(\ell\). Terms with coincident primes cost
\(O(\ell^{O(1)}/W)\).
Prefix partial summation introduces at most one power
of the endpoint \(u\) and the displayed \(\log W\) for
a \(\log b\) weight. All these errors are uniform.
As usual \(\rho\) and \(\omega\) are Dickman and Buchstab;
the normalization is the one in the cited renormalization.

For the actual raw model,
\[
 V_N(W)\sum_{\substack{b\le R_-\\P^-(b)>W}}
          \frac{\mu(b)}b(\log y-\log b)
             =\mathfrak S(N)(1+o(1))
\]
uniformly for \(y\in J\).
Here \(u=\log R_-/\log W\gg\ell\),
\(e^{-\gamma}\int_0^\infty\rho(u)\,du=1\), and
\(\rho(u)\le1/\lfloor u\rfloor!\) pays even the factor
\(L/\log W\) in the term from \(\log y\).
This principal is *subtracted* from the \(\Lambda\) atom.

For the free model use the *exact* coefficient identity
\[
 -\zeta_{>W}'(s)\prod_{W<p<C_y}(1-p^{-s})^2
      = \zeta_{\ge C_y}(s)^2(\zeta_{>W}^{-1})'(s).
\]
In the actual cutoff \(A_y=y/R_+=x^{1/2-\delta_x+O(1/L)}\)
this changes the harmonic model into
\[
 V_N(W)
 \sum_{\substack{h\le A_y\\P^-(h)\ge C_y}}\frac{\tau(h)}h
           \sum_{\substack{b\le A_y/h\\P^-(b)>W}}
                   \frac{-\mu(b)\log b}{b}.                  \tag{2}
\]
Endpoint differences in the \(y\)-integration have measure zero.
The inner sum times \(V_W\) is uniformly bounded, and
uniformly tends to 1 whenever \(\log(A_y/h)/L\)
is bounded below by a fixed positive constant.
This follows from its uniform Dickman model
\(e^{-\gamma}\int_0^{\log(A_y/h)/\log W}\rho(t-1)1_{t\ge1}\,dt\).
The outer positive harmonic CDF converges to
\(Q_\epsilon\), continuously near \(1/2\), uniformly for
the actual \(C_y=x^{\epsilon+O(1/L)}\).
One first removes a fixed small exponent strip below
\(1/2\), uses convergence to 1 away from that strip,
and finally restores it using the uniform inner bound
and continuity. Hence (2) is
\(\mathfrak S(N)[Q_\epsilon(1/2)+o_\epsilon(1)]\),
uniformly in \(W,y,N\).
After the integration over \(J\), the preceding raw
and free signs give exactly (1).
In particular no logarithmic precision of the error on the
unbounded-rank shoulder itself has been invoked.

## 3. The same deletion genuinely concerns many-small rows

The difference \(H_z-H_W\) is exactly the score \(H_z\)
on the band \(z<P^-(y)\le W\), and zero elsewhere.
Squareful \(z\)-rough \(y\) make an \(O_A(xL^{-A})\)
error by Cauchy--Schwarz, a fixed divisor moment and
their \(O(x/z)\) absolute count.
In the deleted band the no-small sector is empty since
\(W\le Y<C_y\) eventually.
The exactly-one and exactly-two score is identical here
to that of the old calibrated completion on squarefree
rows, for either root convention.
Their ranks are bounded at fixed \(\epsilon\); the
bounded-rank transfer to the own root from the original
direct identity hence costs \(o_\epsilon(x\mathfrak S(N))\),
uniformly on any subset of these ranks.

Use the actual one-small and two-small upper bounds in
Section 2 of the renormalization, with the extra real
restriction on the least small prime \(p\le W\).
For one-small, both the true far part (weight \(\log p\))
and the true collar (width \(\log p+O(1)\)) gain
\(\sum_{p\le W}(\log p+1)/p\ll\log W\)
in place of \(O(\epsilon L)\).
Their total is \(O(x\mathfrak S(N)\sigma/\epsilon^2)\).
For exactly two, write \(p<q\) with \(p\le W\).
The two outer strips have width \(\log p+O(1)\)
and weight \(O(L)\). Their harmonic prime sum is
\[
  \sum_{\substack{z<p\le W\\p<q\le1.5x^\epsilon}}
       \frac{\log p+1}{pq}
  \ll \log W\,(1+\log\ell).
\]
The middle strip costs \(2\log p\) with width
\(\log q+O(1)\), giving its bound
\(O(x\mathfrak S(N)\sigma/\epsilon)\).
Thus all exactly-one/two absolute contributions in the
band are \(O_\epsilon(x\mathfrak S(N)
\,\sigma(1+\log\ell))=o_\epsilon(x\mathfrak S(N))\).
Subtract these and the negligible squareful part from (1)
at \(W=z\) and at the chosen \(W\).
The resulting statement is on the actual many-small
composite rows, with the original sharp gap retained.

For the reciprocal cutoff variant, [two actual signed orientation sectors](../completed_gap_two_true_sectors/Proof.md) allow comparison to the own root at the same stronger roughness range, but only on the specified near-root divisors. This is not a whole-score own-root transfer.

A [joint tiny-label refinement](../direct_tiny_label_tv/Proof.md) controls the sum of absolute *profile totals* over all nonempty sets of actual tiny prime factors in a specified sub-band. It permits arbitrary bounded selections by the entire label set but does not bound absolute row mass or settle the surviving empty profile.

An [absolute whole-row deletion](../direct_light_complete_core/Proof.md) applies instead when the complete actual small-prime product is light and has at least two factors. Unlike signed orientation bounds, its full-score estimate remains valid under arbitrary bounded row masks.
