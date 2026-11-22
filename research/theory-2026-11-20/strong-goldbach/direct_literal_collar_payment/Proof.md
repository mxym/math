# Paying the literal raw collar with positive safe orientations

Use the same target, squarefree \(x^{1/\ell}\)-rough rows,
moving \(C_y\), and symmetric gap as in the
[macro-collar payment](../direct_macro_collar_payment/Proof.md).
Thus \(N=2x\), \(L=\log x,\ \ell=\log L,\ \delta=3\log\ell/\ell\),
\(\vartheta=\ell^{-1/4}\), \(R_\pm(y)=\sqrt y\,x^{\pm\delta}\),
and all rows are tested against their actual prime \(P=N-y\).
Keep \(0<\epsilon<.005\) fixed first.
We now pay terms of the **literal all-completed gap score**,
not just a difference from the own-root score.
This is an alternative use of the same safe scores, not
an additional reserve to add to that earlier payment.

The exact grouping is as follows. For short \(d<\sqrt y\),
write \(a=y/d\), and let \(d=SM\) with \(S\) its complete
actual small part (prime factors \(<C_y\)).
If \(R_-(y)<d<\sqrt y\), the two admitted raw terms at
\(a,d\) and absence of the free paired term give the
literal gap contribution
\[
       {\cal A}^{\rm raw}_y(d)
         =\mu(d)\{\mu(y)\log d+\log(y/d)\}.                  \tag{1}
\]
For a safe \(b<R_-(y)\), the exact actual gap contribution
is instead
\[
       {\cal C}_y(b)=
        \mu(S_b)\{(1+\mu(y)\mu(M_b))\log M_b
                   +(\mu(y)\mu(M_b)-1)\log S_b\},           \tag{2}
\]
where \(b=S_b M_b\) is its actual small/macro factorization.
All endpoint equality losses are negligible as in the
earlier macro-collar payment.

**Theorem.** On the true rows just specified, take the
polynomial-minimum collar \(P^-(d)\ge x^\vartheta\).
If \(\mu(y)=-1\), the complete literal raw contribution
of this collar is \(o_\epsilon(x\mathfrak S(N))\) in absolute
mass after summing with \(\log P\).
If \(\mu(y)=+1\), the negative collar terms in either class
\[
 \text{A: } \mu(S)=+1,\ \omega(M)\ \text{odd}\ge3,
 \qquad
 \text{B: } \mu(S)=-1,\ \omega(M)\ \text{even}\ge2
\]
can be assigned distinct safe actual positive terms
\({\cal C}_y(b)>0\) on each physical row.
The total shortfall on the true prime leg is
\[
 O_\epsilon\!\left(
       x\mathfrak S(N)\frac{(\delta+L^{-1})^2}
                            {\chi\vartheta^3}\right)
       =o_\epsilon(x\mathfrak S(N)),\qquad \chi=1/\ell.
                                                                  \tag{3}
\]
Each assigned \(b\) itself has \(P^-(b)\ge x^\vartheta\).
Thus the theorem concerns a genuine subcomponent of the
literal fixed-target score, including both rather than
one of the two raw orientations in (1).
No conclusion is made on the remaining safe scores, on
the calibration, or on the missing macro-rank zero or one
collar types. The analytic signed bound for a *difference*
at an all-small divisor is not asserted to price the
literal term (1) at even total rank.

## 1. Same-row positive partners

When \(\mu(y)=-1\), (1) is at most \(2\delta L\) in
absolute value for every collar \(d\).
Use the true two-bank upper (5) of the macro-collar payment
with fixed coefficient \(d\) and free rough \(a\), and its
harmonic width bound (6).
There is \(O((\delta+L^{-1})/\vartheta)\) harmonic mass
of the relevant \(d\)'s, and \(x/d\gg\sqrt x\) leaves
the required polynomial length. The resulting absolute
cost is \(O(x\mathfrak S(N)(\delta+L^{-1})^2/
(\chi\vartheta^2))\), and is negligible.

Now take \(\mu(y)=+1\). The negative (1) is exactly
\(-\log y\) when \(\mu(d)=-1\).
For each selected negative \(d=SM\), choose *every*
orientation \(b=d/p\) obtained by deleting one actual
prime \(p\mid d\), except when its value in (2) is zero.
These choices are distinct within \(d\).
They are all safe, since \(p\ge x^\vartheta\) and
\(\vartheta>\delta\) eventually.
They are nontrivial in the two claimed macro-rank ranges
and hence retain a prime factor \(\ge x^\vartheta\).

For A, deleting a macro prime gives \(2\log(M/p)\).
Their total is \(2(\omega(M)-1)\log M\).
If \(S>1\), it has even rank at least 2; deleting a small
prime gives \(2\log(S/p)\), totaling
\(2(\omega(S)-1)\log S\).
Together these weights are at least \(2\log d\); if
\(S=1\) the missing second sum is zero with no change.
For B, deleting a macro prime gives the value \(2\log S\)
for each of the \(\omega(M)\) choices.
Deleting a small prime gives \(2\log M\) for each of the
\(\omega(S)\) choices.
Again their sum is at least \(2\log d\).
Thus any noncolliding allocation misses the actual debit
\(\log y\) by at most \(\log(y/d^2)<2\delta L\).
The bill of this width is the same as for odd total rank
just shown.

## 2. The actual collision cost with arbitrary deleted primes

Discard every \(d\) any of whose selected positive \(b\)'s
is selected by a different \(d'\) on the same physical \(y\).
Then the retained receivers are distinct across all
remaining adverse \(d\)'s.
A lost negative debit is \(O(L)\) times a collision
with \(d=bp\), \(d'=bq\), \(p\ne q\) true primes;
each discarded \(d\) participates, and an ordered
collision counts its full permitted multiplicity.
One may ignore which original prime was small or macro
in assigning this upper bound, but \(p,q\ge x^\vartheta\)
and \(P^-(b)\ge x^\vartheta\) remain in force.

Put \(H=bpq\); squarefreeness ensures the factors of
this product are distinct where required.
The actual remaining quotient \(a=y/H\) satisfies
\(x/H\gg b\ge x^\vartheta\) as \(bp,bq<\sqrt y\)
and \(y\le1.5x\).
It is \(x^\chi\)-rough; thus we may use the same true
two-bank upper (5) for \(a\) and \(N-Ha\).
The fixed-factor harmonic factor is exactly \(1/(bpq)\).
Keeping \(p\) fixed, the true collar condition on \(bp\)
restricts \(b\) to harmonic exponent width
\(\delta+O(1/L)\), or
\(O((\delta+L^{-1})/\vartheta)\) by the moving width bound.

Both \(d,d'\) share the same own root, so
\(|\log p-\log q|\le\delta L\).
For \(p\ge x^\vartheta\) and \(\delta=o(\vartheta)\),
the prime harmonic sum over linked \(q\)'s is
\(O((\delta L+1)/\log p)\); divide into dyads and
use the ordinary prime upper.
Consequently the remaining two labels contribute at most
\[
   \ll (\delta L+1)
       \sum_{\substack{p\ge x^\vartheta\\p\ {\rm prime}}}
                                  \frac1{p\log p}
    \ll \frac{\delta+L^{-1}}\vartheta .
\]
The final inequality uses the standard prime upper
with partial summation. Thus there is **no additional
\(\log(1/\vartheta)\) loss** from the full range of the first
deleted prime. The harmonic widths and the true sieve bound,
times the two logarithms \(O(L^2)\), give (3).
In the parameters above the ratio in (3) is
\(O((\log\ell)^2/\ell^{1/4})\).
The opposite-prime exceptions dividing \(N\) and the strict
cutoff equalities have the same negligible costs as in
the earlier collar proof.
This handles the actual literal paired score without
moving any long free term across its root, and proves the
theorem.

A [tiny-factor extension](../direct_tiny_literal_collar_payment/Proof.md) pays additional even-rank subfamilies while retaining every very small factor in the safe receivers. Its receiver sets are disjoint from the minimum-factor packet above.
