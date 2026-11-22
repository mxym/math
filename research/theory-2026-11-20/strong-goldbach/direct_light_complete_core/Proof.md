# Absolute deletion of rows with a light complete small factor

Use the literal reciprocal all-small-completed score, with the
same moving small-factor threshold as the
[many-small renormalization](../direct_many_small_renormalization/Proof.md).
This is a whole row estimate in absolute value, not a
signed subset of the near-root terms.

Let \(N=2x\) be even, \(L=\log x\), \(\ell=\log L\),
\(J=xJ_0\) with fixed \(J_0\subset[1,3/2]\), and \(P=N-y\)
the actual opposite prime.
Fix \(0<\epsilon<.005\), and let
\[
 \ell^{-2}\le\chi\le\ell^{-1},\quad W=x^\chi,\quad
 C_y=y/x^{1-\epsilon},\quad
 R_\pm(y)=\sqrt y\,x^{\pm\delta},\quad \delta=o(1).
\]
The proof also works with \(R_\pm=x^{1/2\pm\delta}\);
only a fixed factor needs changing in the moving bounds.
Write \(H(y)\) for the actual score
\[
 H(y)=1_{\{P^-(y)>W\}}\left[
       \sum_{\substack{r\mid y\\r>R_-(y)}}\mu(r)\log(y/r)
       +\sum_{\substack{csa=y\\a>R_+(y)\\P^+(c)<C_y}}
                                      \mu_2(c)\log s\right],
 \qquad \mu_2=\mu*\mu .
\]
The cofactor condition includes \(c=1\).
When \(y\) is squarefree, let \(Q=Q(y)\) be the product
of **all actual primes** \(p\mid y\) with \(p<C_y\), and
write \(y=QB\). Thus the remaining macro part \(B\)
has all prime factors \(\ge C_y\ge x^\epsilon\).
No fixed rank restriction is made on \(Q\).

**Theorem.** Uniformly for \(\chi\le q\le.001\) tending
to zero, on the actual fixed even target,
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime},\ y\ {\rm squarefree}\\
                 P^-(y)>W,\ \omega(Q(y))\ge2,\ Q(y)\le x^q}}
           \log P\,|H(y)|
         \ll_{\epsilon,J_0}
           x\mathfrak S(N)\,\frac{q^2}{\chi}.                \tag{1}
\]
Here \(\mathfrak S(N)\) is the same positive singular factor
as in the direct identity. For example, choosing \(q=\chi^{3/5}\)
gives \(O_\epsilon(x\mathfrak S(N)\chi^{1/5})\);
one can take any \(q=o(\sqrt{\chi})\) in the displayed range.
This pays all the safe and collar orientations on these
physical rows together, for either actual parity of \(y\).
It does not bound either orientation separately after
the cancellations below have been undone.
The condition \(\omega(Q)\ge2\) is essential to the argument.

## 1. Exact subset cancellation with the full small part

For \(M\mid B\), set \(A=B/M\).
Every raw divisor \(r\) whose macro part is \(M\) is
\(r=Mu\) for a unique \(u\mid Q\).
Its log weight, apart from the factor \(\mu(M)\mu(u)\), is
\[
                   \log A+\log(Q/u).                         \tag{2}
\]
It is present exactly when \(Mu>R_-(y)\).
For the free contribution, group by the macro part of the
large divisor \(a=Mu\), which is present when \(Mu>R_+(y)\).
The other small divisors allowed in the free coefficient
are exactly \(c\mid Q/u\).
Using squarefreeness, Boolean subset sums give
\[
 \sum_{c\mid Q/u}\mu_2(c)\log(AQ/(uc))
       =\mu(Q/u)[\log A-\log(Q/u)].                          \tag{3}
\]
Indeed \(\sum_{c\mid T}(-2)^{\omega(c)}=\mu(T)\) for
squarefree \(T\); the coefficient of any \(p\mid T\)'s
logarithm in \(\sum_c(-2)^{\omega(c)}\log(T/c)\) is
\(\mu(T/p)=-\mu(T)\).
All signs and the actual moving \(C_y\) are therefore kept.

If **all** \(u\mid Q\) pass a given raw or free cutoff,
the group's total vanishes: \(\sum_{u\mid Q}\mu(u)=0\)
and each of the first logarithmic subset sums is zero
when \(\omega(Q)\ge2\).
If none pass the group is also zero.
Consequently only the windows
\[
              R_\pm(y)/Q<M\le R_\pm(y)                       \tag{4}
\]
need to be considered in their respective groups.
In particular, for \(Q\le x^q\) these are genuinely near
the macro square-root scale; no all-small row \(B=1\) can
occur in the physical range \(y\in J\).

Let \(p=P^-(Q)\) be the actual least prime factor of the
full small part. Pair the subsets \(u\mid Q/p\) and
\(pu\). In each of (2) and (3) their signs are opposite,
their log weights differ by \(\log p\) in magnitude,
and each magnitude is \(O(L)\).
If both pass, the absolute pair difference is \(\log p\).
If only the larger passes, \(M\) lies in the shorter
window
\[
                   R_\pm(y)/(pu)<M\le R_\pm(y)/u,            \tag{5}
\]
of width \(\log p\) in logarithmic coordinates, and the
absolute pair cost is at most \(O(L)\).
Otherwise it is zero.
We retain the original cancellation outside (4), then
apply the triangle inequality only within (4), using the
pair subdivision (5).
Thus the argument never counts all pairs separately
on an interval where their complete subset sum is zero.

## 2. Actual prime count and the least-factor gain

For each fixed actual \(Q,M\), put \(D=QM\).
The variable \(A=y/D=B/M\) ranges in an interval of
length \(\asymp x/D\), and remains \(x^\epsilon\)-rough
on every genuine row.
By (4), \(D\le x^{1/2+q+\delta+o(1)}\);
the available length exceeds \(x^{.49}\) for all large
\(x\) after \(q,\delta\to0\).
The true opposite prime is \(N-DA\), not an independent
benchmark. Use the
[exactly-two gate's two-bank upper](../direct_many_small_gate/Proof.md):
in the first bank of primes up to \(x^\epsilon/2\)
sieve both \(A\) and \(N-DA\), in the following bank
up to \(x^{.04}\) sieve only the latter.
It gives
\[
   \#\{A\ {\rm in\ the\ box},\ P^-(A)\ge x^\epsilon,\
                                 N-DA\ {\rm prime}\}
          \ll_\epsilon \frac{x\mathfrak S(N)}{D L^2}.
                                                                  \tag{6}
\]
For clarity, \(D\) need not itself be \(x^\epsilon\)-rough.
All of its true prime factors exceed \(W\); the missing
or colliding roots at those primes cost only
\(\prod_{r\mid D}(1+O(1/r))=1+O(L/W)\) in the upper model.
The same actual \(N\) root coincidences give
\(\mathfrak S(N)\).
The positive two-bank sieve products and CRT floors
work at the long displayed length, exactly as for the
gate. Opposite primes dividing \(N\) cost only
\(x^{o(1)}\) after divisor weights, and can be omitted.
No divisibility between \(D\) and the variable \(A\)
is enforced in this upper, which only enlarges the set.

For fixed \(Q,u\) one may relax the intervals (4) and
(5) over all \(y\in J\).
Their logarithmic widths increase by only \(O(1)\),
since \(R_\pm(y)/x^{1/2\pm\delta}\in[1,\sqrt{1.5}]\).
The actual fixed macro \(M\) has \(P^-(M)\ge x^\epsilon\)
and lies at \(x^{1/2+o(1)}\).
The true harmonic mass of such \(M\)'s in a logarithmic
window of width \(D_1\) is
\(O_\epsilon((D_1+1)/L)\): split into at most \(O(D_1+1)\)
dyads and apply ordinary integer upper rough sieving in
each long dyad. This is the harmonic width bound
used in the exactly-two gate.

Apply (6) with the original pure-prime log weight
\(\log P\ll L\), and sum over the possible macro \(M\)'s.
For a pair \(u,pu\), its shorter jump window (5) gives
a contribution at most
\(O_\epsilon(x\mathfrak S(N)(\log p+1)/(QL))\).
The both-passing part within (4), with individual
weight \(\log p\), contributes at most
\[
       O_\epsilon\left(
        \frac{x\mathfrak S(N)}{Q}
            \frac{\log p}{L}\frac{\log Q+1}{L}\right).
\]
The latter is bounded by the former in the stated range.
There are \(2^{\omega(Q)-1}\) paired subsets.
Taking both raw and free thresholds, the remaining
upper is therefore
\[
       O_\epsilon\left(
       x\mathfrak S(N)
       \sum_{\substack{Q\le x^q,\ \omega(Q)\ge2\\ P^-(Q)>W\\
                       Q\ {\rm squarefree}}}
          \frac{2^{\omega(Q)}}{Q}\,
                        \frac{\log P^-(Q)+1}{L}\right).       \tag{7}
\]
The added least-prime logarithm is what improves upon
using the full width \(\log Q\) for each separate subset.

Fix \(p=P^-(Q)\), which satisfies \(W<p\le x^q\).
Dropping the product constraint on the other prime
factors only for the positive upper, Mertens gives
\[
 \prod_{p<r\le x^q}(1+2/r)
                   \ll \bigl(qL/\log p\bigr)^2.
\]
Every prime in the product is a true possible physical
label; no asymptotic independence on the \(P\)-leg
is used. With \(p>W\), \(\log p+1\ll\log p\).
The harmonic sum in (7) is bounded by
\[
  \ll q^2 L\sum_{\substack{p>W\\p\ {\rm prime}}}
                     \frac1{p\log p}
       \ll \frac{q^2}{\chi}.
\]
The last estimate is ordinary prime upper partial
summation, \(\sum_{p>W}(p\log p)^{-1}\ll1/\log W\).
This proves (1), with an explicit absolute row bill.

## 3. Compatibility of the deletion

It is legitimate to remove these entire physical rows
first: (1) pays the total actual change and also its
change under any additional bounded mask on the rows.
Rough squareful rows, if present in the common starting
score, have the usual negligible \(O(x/z)\)-plus-divisor-
moments bill since \(W\ge z=x^{1/\ell^2}\).
At a calibrated sharp gap the prime atom is unchanged
by this removal, since true \(y\) primes have \(Q=1\).
So the same explicit calibration and its unresolved
Goldbach-scale comparison remain on the retained
genuine heavy-small rows (and the cases with at most
one small prime).

The deletion is particularly compatible with
[all actual tiny-label profile bounds](../direct_tiny_label_tv/Proof.md)
when the same score and parameter choice are used:
the sum of changes of all profile coefficients is
bounded by the absolute row bill.
Likewise, a deterministic same-row payment whose
unpaid bill has an absolute true upper may be applied
after deleting these rows; its allocation is made
only on the surviving rows, and its nonnegative
error majorant can only decrease.
For example this applies to the
[literal collar](../direct_literal_collar_payment/Proof.md)
and [arbitrary-tiny same-row payment](../direct_tiny_literal_collar_payment/Proof.md)
on their stated parameter ranges.
It does **not** assert that any separately signed
orientation sector already averaged over all \(y\)
retains its cancellation on the restricted row set.
No part of (1) is counted as a positive lower bound.
