# Same-row payment of non-giant adverse short divisors

This note uses the *all-small-completed* score, with the literal
moving threshold \(C_y=y/x^{1-\epsilon}\) and a symmetric own-root
gap, as in the [two true shoulder sectors](../completed_gap_two_true_sectors/Proof.md).
It separates genuine negative collar terms and genuine positive
safe orientations in the same fixed-\(N\) arithmetic score.
It does not supply a positive lower after the full calibration.

Let \(N=2x\) be even, \(J=xJ_0\) with fixed \(J_0\subset[1,3/2]\),
\(P=N-y\), \(L=\log x\), and \(\ell=\log L\). Fix \(0<\epsilon<.005\),
then take \(x\) large, and fix
\[
    \chi=\ell^{-1},\quad W=x^\chi,\quad
    \delta=3\frac{\log\ell}{\ell},\quad
    \vartheta=\ell^{-1/4},\quad R_\pm(y)=\sqrt y\,x^{\pm\delta}.
\]
All rows below have \(y\) squarefree and \(W\)-rough, with an
actual prime \(P=N-y\). Call a prime factor *small* when it
is \(<C_y\); the complementary factors are called macro.
These names refer to actual prime factors of \(y\).
All orientation identities take place before any modeling.
Let \(\mathfrak S(N)\) be the same positive singular factor as in
the [fixed-target direct identity](../direct_goldbach_composite_gap/Proof.md).

For a short collar divisor
\(R_-(y)<d<\sqrt y\), write \(d=SM\), where \(S\) is its
full actual small subproduct. The gap minus the own-root score
has at this orientation the term
\[
 {\cal B}_y(d)=
   \mu(S)\{\mu(M)\log(y/d)-\log d+2\log S\}.                   \tag{1}
\]
Let \(\mathcal A_y\) comprise adverse orientations
\({\cal B}_y(d)<0\) in this collar which satisfy
\(P^-(d)\ge x^\vartheta\) and either:
- \(S\) has even rank and \(M\) has odd rank at least 3; or
- \(S\) has odd rank and \(M\) has even rank at least 2.

**Theorem.** For each \(y\), there is an explicit selection of
distinct safe orientations \(b<R_-(y)\) with positive *actual gap*
terms \({\cal C}_y(b)\). With this selection,
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\
                  y\ {\rm squarefree},\,P^-(y)>W}}
      \log P\left[\sum_{b\ {\rm selected}}{\cal C}_y(b)
                 +\sum_{d\in\mathcal A_y}{\cal B}_y(d)\right]
        \ \ge\ -o_{\epsilon,J_0}(x\mathfrak S(N)).             \tag{2}
\]
The selection charges each safe orientation at most once per
physical row. All eligible short collar types above are covered,
including either parity of the total rank of \(y\), and \(y\)
may have arbitrarily many \(W\)-rough prime factors as \(x\) grows.
For eligible \(d\) the only negative sign types outside
\(\mathcal A_y\) are an odd small part with \(M=1\), or an even
small part with \(M\) a single true prime. The first is all-small
and is in the already evaluated smooth short-divisor sector.
This theorem does not bound the one-macro-prime case or the
excluded short divisors with \(P^-(d)<x^\vartheta\).

The payment in (2) uses positive terms of the original
same-row score. They cannot also be used as independent
positive reserves in an estimate of the remaining score.
In particular (2) is not a lower bound for the score minus
its full fixed-target calibration.

## 1. Exact adverse and positive weights

For a general short \(b\mid y,\ b<\sqrt y\) let
\(S_b\) be its actual small part and \(M_b=b/S_b\).
Under all-small completion the cofactor weight at \(b\) is
\[
 \sum_{c\mid S_b}(-2)^{\omega(c)}\log(b/c)
       =\mu(S_b)(\log b-2\log S_b).                           \tag{3}
\]
Indeed, the zeroth subset sum is \(\mu(S_b)\) and the
coefficient for each prime logarithm receives the
corresponding first subset sum.
For \(b<R_-(y)\), the complementary \(a=y/b>R_+(y)\)
is admitted in both long score parts; there is no extra
short raw term at \(b\).
Using squarefreeness gives its exact total
\[
 \begin{split}
 {\cal C}_y(b)
   &=\mu(y)\mu(b)\log b+\mu(S_b)(\log b-2\log S_b)\\
   &=\mu(S_b)\{(1+\mu(y)\mu(M_b))\log M_b
                    +(\mu(y)\mu(M_b)-1)\log S_b\}.            \tag{4}
 \end{split}
\]
When \(R_-(y)<d<\sqrt y\), the extra short raw term is
\(\mu(d)\log(y/d)\); its own-root free complement
term (3) is absent in the gap.
This proves (1).
If \(\mu(M)=-1\), the quantity inside (1) is
\(-\log y+2\log S<0\).
If \(\mu(M)=+1\), it is
\(\log(y/d^2)+2\log S\ge0\).
These give exactly the adverse sign table in the theorem.

For each eligible adverse \(d=SM\), keep its entire small
part \(S\). If \(\mu(y)=+1\), delete one genuine macro prime
\(p\mid M\); if \(\mu(y)=-1\), delete a product of two
distinct genuine macro primes.
Write \(v\) for the one- or two-prime deleted product and
\(b=d/v\).
Every such \(v\) has \(v\ge C_y\ge x^\epsilon\),
so \(b<R_-(y)\) for all large \(x\).
The selected \(b\) is nontrivial: in the first type at least
one macro remains, and in the second type \(S>1\).
It has all prime factors at least \(x^\vartheta\).
Also \(S_b=S\), exactly.

If \(S\) has even rank and \(M\) odd rank \(r\ge3\),
the deletion parity forces \(\mu(M_b)=\mu(y)\), and
(4) is \(2\log M_b>0\).
For a one-prime deletion choose the two smallest genuine
macro primes as two different choices. Their positive
weights total at least \(2\log M+2\log p_{\rm left}\)
for any third remaining prime \(p_{\rm left}\mid M\).
For a two-prime deletion choose all \(\binom r2\) unordered
pairs. Their positive weights total
\(2\binom{r-1}2\log M\ge 2\log M\).
In either parity the debit \(-{\cal B}_y(d)\) is
\(2\log M+\log(y/d^2)\).
Thus the payment is short of the debit by at most
\(\log(y/d^2)<2\delta L\);
the inequality has a strict order-\(L\) surplus when
the two-prime deletion has \(r\ge5\) or the one-prime
deletion uses the two distinct choices, for large \(x\).

If \(S\) has odd rank and \(M\) even rank \(r\ge2\),
the deletion forces \(\mu(M_b)=-\mu(y)\).
Now (4) is \(2\log S>0\) for each choice.
Choose all \(r\) macro primes for the one-prime deletion,
or all \(\binom r2\) pairs for the two-prime deletion.
There is at least one choice, with total at least \(2\log S\).
Again the debit is exactly \(2\log S+\log(y/d^2)\),
so the shortfall is at most \(2\delta L\).

The choices within a given \(d\) are distinct and
deterministic. To keep the allocations disjoint across \(d\),
discard every \(d\) having **any** chosen \(b\) in common
with a different eligible \(d'\) on the same \(y\).
Collect all of the remaining chosen \(b\)'s as the selection
in (2).
The sum of the debits of the discarded \(d\)'s is
\(O(L)\) times the total number of ordered collisions
\((b,v,v')\) with \(d=bv\ne bv'=d'\), since every discarded
\(d\) participates in such a collision.
There is no comparison of two different targets or of two
modeled rows.

## 2. A true two-form upper, with a slowly moving minimum

We use the following uniform form of the
[exactly-two two-bank upper](../direct_many_small_gate/Proof.md).
Let \(H\) be an actual fixed \(W\)-rough integer, unit at \(N\),
and let \(a\) vary in the interval \(x\le Ha\le1.5x\).
If its interval length is \(U=x/(2H)\gg x^\vartheta\), then
\[
 \#\{a\hbox{ in this interval}:P^-(a)>W,\ N-Ha\ {\rm prime}\}
        \ll U\,\frac{\mathfrak S(N)}{\chi\vartheta L^2}.        \tag{5}
\]
Here the threshold \(\vartheta=\ell^{-1/4}\) can move
because every sieve exponent below is an explicit multiple
of it. In the first bank of primes at most \(W\) sieve
both \(a\) and \(N-Ha\) with a dimension-two upper sieve
of level \(x^{\vartheta/10}\).
There are two roots except at primes of \(NH\), where
there is one, including at 2.
In the second, disjoint bank \(W<p\le x^{\vartheta/100}\)
sieve only \(N-Ha\), with a dimension-one upper sieve
of level \(x^{\vartheta/20}\).
There is one root except at \(p\mid H\).
The first sieve parameter \(\vartheta/(10\chi)\)
tends to infinity, and the second parameter is 5
when using the indicated upper cutoff.
The dimension bounds are uniform; one may use the
bounded upper weights of
[Koukoulopoulos, *The Distribution of Prime Numbers*, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).
In Theorem 19.1 the dimension-one threshold is
\(1+2/(e^{.53}-1)<5\), and the increasing first-bank
parameter eventually exceeds its dimension-two threshold.

The two upper polynomials are individually nonnegative,
so their product remains an upper for the true sifted
indicator. By CRT its main is the product of the two
upper model factors, each with a uniform constant.
The small-bank factor is
\(\ll\mathfrak S(N)/(\chi L)^2\), and the large-bank
factor is \(\ll\chi/\vartheta\).
These follow by Mertens and the usual singular product:
primes of \(H\) are \(>W\), so the additional omitted
or colliding factors cost at most
\(\prod_{p\mid H}(1+O(1/p))=1+O(L/W)\).
Primes of \(N\) give the actual local one-root
conditions and are not omitted from their model.
The product error from the actual CRT floors is
\(\ll x^{\vartheta/5}L^{O(1)}\), using
\(2^{\omega(d)}\) as the small-bank root bound and the
single-root bound in the second bank.
Because \(U\gg x^\vartheta\) and \(L\vartheta\to\infty\)
much faster than \(\log L\), this is negligible in (5).
The actual prime \(N-Ha\ge x/2\) is never a sieve prime.
Opposite primes dividing \(N\) are omitted throughout
at a negligible error \(x^{o(1)}\): at most \(O(1)\)
occur at this scale and a divisor power bounds the full
number of covered orientations and collisions.

We also use a uniform true harmonic width bound:
for an exponent interval of width \(\Delta\) in
\([\vartheta,1]\),
\[
      \sum_{\substack{x^a\le b\le x^{a+\Delta},\ b>1\\
                       P^-(b)\ge x^\vartheta}}\frac1b
                   \ll\frac{\Delta+L^{-1}}{\vartheta}.
                                                                  \tag{6}
\]
One can sum dyads, on each of which
\(\#\{b\sim B:P^-(b)\ge x^\vartheta\}\ll
B/(\vartheta L)\).
For \(x^\vartheta/2\le B\le x^{100\vartheta}\),
this follows by opening the at most 101 prime factors:
fix all but one of the possible actual primes in each
rank and apply the ordinary prime upper on its resulting
dyad, then sum the other primes harmonically. The
harmonic mass of \(x^\vartheta\le p\le2x^{100\vartheta}\)
is bounded by an absolute constant; the number 101 is fixed.
For \(B\ge x^{100\vartheta}\), ordinary upper sieving
at level \(x^{20\vartheta}\) gives the same dyadic bound,
with \(x^{20\vartheta}\) integer floor errors negligible.
For a single macro prime, the sharper absolute
\[
   \sum_{\substack{p\ {\rm prime}\\
       p\ge x^\epsilon,\ a\le\log p/L\le a+\Delta}}\frac1p
                \ll_\epsilon \Delta+L^{-1}
\]
follows by the same dyadic prime upper.
This remains true if \(a<\epsilon\) after intersection
with the displayed macro range.
All fixed one- or two-prime macro products have bounded
total harmonic mass in the physical range, for fixed
\(\epsilon\).

## 3. Collision and collar bills on the actual prime leg

For every counted collision let \(g=(v,v')\), \(v=gs\),
\(v'=gt\), and put
\(H=b[g s,g t]=b g s t\).
Here \(b\) is coprime to \(g s t\), and \(s,t\) are
coprime; all factors come from the same squarefree \(y\).
The number of deleted primes is the same for both
options on a fixed \(y\), so \(v,v'\) are incomparable
and \(s,t>1\). If some deleted prime is shared, then
\(g\) is one prime; otherwise \(g=1\).
The products \(s,t\) each have one or two genuine
macro primes.
We have \(H\mid y\) exactly and \(y=Ha\).
Because both \(bgs\) and \(bgt\) are \(<\sqrt y\),
\[
      H=\frac{(bgs)(bgt)}{bg}\le \frac{y}{bg},
      \qquad \frac{x}{H}\gg bg\ge x^\vartheta .
\]
Thus (5) applies to the actual remaining \(a\), even
if \(a\) itself is not \(x^\vartheta\)-rough.
The \(W\)-roughness of all its factors is retained.

For fixed \(g,s\) the true collar
\(x^{1/2-\delta}<bgs<\sqrt{1.5x}\)
restricts \(b\) to exponent width
\(\delta+O(1/L)\).
Equation (6) therefore saves
\(O((\delta+L^{-1})/\vartheta)\) in its harmonic sum.
The ratio \(s/t\) is within \(x^{\pm\delta}\), since both
original divisors share the same physical own root.
Thus for the \(t\)-sum one can fix its other macro prime,
if there is one, and sum its one remaining true prime
in exponent width \(2\delta+O(1/L)\).
The last bound in Section 2 gives a second
\(O_\epsilon(\delta+L^{-1})\) harmonic saving.
The harmonic masses of \(g,s\), and of the other
possible prime of \(t\), are bounded for fixed \(\epsilon\).
All exclusions that were dropped here only enlarge the
upper. This includes dropping the rank parity
of the free part and the precise memberships \(S,M\):
the two shared geometric widths and the actual
fixed-\(N\) prime and \(W\)-rough gates were kept.

Combining (5) and \(1/H=1/(bgst)\), and multiplying
by the score weights \(O(L^2)\) for the discarded
debit and the true \(\log P\), bounds the collision bill by
\[
       O_\epsilon\left(
          x\mathfrak S(N)
             \frac{(\delta+L^{-1})^2}{\chi\vartheta^2}
                      \right)=o_\epsilon(x\mathfrak S(N)).
                                                                  \tag{7}
\]
Indeed the ratio here is
\(O((\log\ell)^2/\sqrt\ell)\).

The width shortfall of every non-discarded \(d\) costs
at most \(2\delta L\).
Fix \(d\) as the coefficient in (5); the remaining
interval length for \(a=y/d\) is \(\gg\sqrt x\).
The harmonic mass of all \(d\)'s in the same root
collar and with minimum prime at least \(x^\vartheta\)
is \(O((\delta+L^{-1})/\vartheta)\) by (6).
The true weighted bill of the shortfall is therefore
bounded by the right hand side of (7), also \(o(x\mathfrak S(N))\).
Adding these two bills proves (2).
When one of the original cutoffs coincides with a divisor
endpoint, the difference convention affects at most
\(O(\sqrt x\,x^\delta)\) actual \(y\)'s (each determined
by the divisor and the equality).
The same fixed-divisor-moment bounds make this negligible,
so the result applies with the strict own-root gap as stated.

Finally, the common true calibration at this roughness
is unchanged:
the proof of the [least-factor deletion](../direct_completed_rough_deletion/Proof.md)
applies with \(W=x^{1/\ell}\) and the present symmetric
own-centered gap, without transferring any unbounded rank
to the own-root score. In the actual raw short sum the
inequality \(b\le\sqrt y\,x^{-\delta}\) just imposes one more
interval endpoint for each \(b\); the free short inequality
has the same upper length. Actual BV and the Euler model
therefore hold at the moving \(v_y=\log(\sqrt y\,x^{-\delta})/L
=1/2-\delta+O(1/L)\).
This gives the same \(Q_\epsilon(1/2)-1\) at natural
accuracy. It does not turn the paired subcomponent (2)
into a bound for the calibration remainder.

[Arneth’s September 2026 compensation framework](https://zenodo.org/records/23016346) gives a finite example across different partner integers and an open capacity criterion; the present packet evaluates an explicit divisor selection on the identical physical partner row and pays its collision losses. The global signed inequality is still open.

The [literal-score upgrade](../direct_literal_collar_payment/Proof.md) uses all single-prime deletions to pay the actual raw collar, rather than only the gap-versus-own-root difference, on the indicated types. The same positive terms cannot be used twice.
