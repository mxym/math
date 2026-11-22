# A literal wide-collar debit with true safe-divisor receivers

Let \(N=2x\) be even, \(L=\log x\), \(\ell=\log L\), and
\(J=xJ_0\) for a fixed nonempty interval \(J_0\subset[1,3/2]\).
All sums below use **actual primes** \(P=N-y\), with \(y\in J\), and
weight \(\log P\). Put
\[
 U=\ell^{-1/4},\quad w=\frac{U}{100\log\ell},\quad W=x^w,\quad
 \epsilon=\ell^{-1/100},\quad C_y=\frac{y}{x^{1-\epsilon}},\quad
 h=\ell^{-1/20}.
\]
Use the full all-small completion and the genuine reciprocal gap
\(R_\pm(y)=\sqrt y\,x^{\pm U}\) of the
[wide-gap theorem](../wide_gap_all_terminal/Proof.md), with its original
moving \(C_y\) and without a fixed payer. The full-score deletion at
the same \(W\) is the [unchanged-cutoff addendum](../adaptive_first_three_completion/FixedFullCutoffAddendum.md).
This note concerns the surviving **squarefree \(W\)-rough** rows.
It does not use the signed least-prime deletion as an unsigned
estimate on any orientation.

At a short pairing label \(d<\sqrt y\), write \(v=y/d\) and
\(t=(\log\sqrt y-\log d)/L\).
The literal two-raw-term score in the strict collar \(0<t<U\) is
\[
 A_y(d)=\mu(d)\{\mu(y)\log d+\log v\}.
\tag{1}
\]
At a safe label \(b<R_-(y)\), let \(S_b\) contain all actual prime
divisors \(p<C_y\) of \(b\), and \(M_b=b/S_b\).
The entire paired raw-plus-free score there is
\[
 C_y^{\rm pair}(b)=\mu(S_b)
      \big\{(1+\mu(y)\mu(M_b))\log b-2\log S_b\big\}.      \tag{2}
\]
These are the raw/safe pair formulas of full completion.
For example the safe free sum is
\(\sum_{c\mid S_b}(-2)^{\omega(c)}\log(b/c)=
\mu(S_b)(\log b-2\log S_b)\), and the other short term is
\(\mu(y)\mu(b)\log b\).

## The actual packet

Set the two fixed-at-\(x\) prime banks
\[
 {\cal B}=(x^{3U},x^h],\qquad {\cal H}=(x^h,x^{\epsilon/2}]. \tag{3}
\]
An allowed source is any actual short \(d\) in the collar containing
no prime in \({\cal B}\cup{\cal H}\). This imposes no rank bound or
factor-type restriction on \(d\). There is a choice of distinct
actual safe receivers \(b\) at each \(y\), each with
\(C_y^{\rm pair}(b)>0\), such that their weights together with
**all** allowed source raw scores (1), tested against \(\log P\),
sum to at least
\[
             -O_{J_0}\big(x\mathfrak S(N)\ell^{-1/100}\big). \tag{4}
\]
In particular this pays negative raw scores in the literal gap
score, not just a difference of cutoff scores. Receiver selection
may instead be applied to any subfamily of the debit sources,
with the same bound.

A specific subfamily is \(d=pA\) where \(p\ge x^{.45}\) is prime and
\(P^+(A)\le x^{2U}\), with \(A=1\) permitted. When only this
large-prime/small-cloud subfamily is charged, none of its receivers
can be obtained by deleting at most two prime factors from any
short collar label on the same \(y\). This last disjointness is
**not** asserted for all bank-free sources in (4).

### Same-input payment

Odd-total-rank sources have \(|A_y(d)|=2tL\le2UL\) and will be bounded
in absolute value. At even total rank, only \(\mu(d)=-1\) creates a
debit, exactly \(-\log y\), and then also \(\mu(v)=-1\).
Suppose that \(v\) has at least \(j=\lfloor .10\log\ell\rfloor\)
actual prime labels in \({\cal B}\), at least one in \({\cal H}\),
and at least one macro prime \(p\ge C_y\). Take its \(j\) least
\({\cal B}\)-labels. For every odd subset of these of cardinality
at least 5 put \(B\) equal to its product and choose the receiver
\[
                              b=v/B.                       \tag{5}
\]
Every such \(b\) is safe, since its depth is \(\log B/L-t>15U-U>U\).
All deleted labels are strictly below \(C_y\), and no \({\cal H}\)
anchor is deleted. Put \(S=S_v,\ M=M_v\); thus \(\mu(S)\mu(M)=-1\).
Directly from (2),
\[
 C_y^{\rm pair}(v/B)=
 \begin{cases}
 2\log(S/B)\ge2hL,&\mu(S)=+1,\ \mu(M)=-1,\\
 2\log M\ge2\epsilon L,&\mu(S)=-1,\ \mu(M)=+1 .
 \end{cases}                                             \tag{6}
\]
The second branch in fact has at least two genuine macro primes
because \(M>1\). There are \(2^{j-1}-j-\binom j3\gg2^j\) subsets;
since \(.10\log 2>.05\) their positive capacity exceeds \(\log y\)
for all sufficiently large \(x\). This is a pointwise payment on
the same physical \(y\), before averaging. Choices are distinct
even across all good sources at a common \(y\): form \(y/b=dB\)
and remove all the \({\cal B}\)-prime factors to recover \(d\).
The receiver labels are safe, hence distinct from all collar labels.

For \(d=pA\), \(y/b=pAB\). If a proposed earlier short collar label
is \(bG\) where \(G\mid pAB\) has at most two prime factors, either it
uses \(p\) or not. If it uses \(p\), then \(\log(bp)/L\ge .95-jh-o(1)>.6\),
since \(v\ge\sqrt y\) and \(jh=o(1)\). This cannot be a short label.
Otherwise each \(G\)-prime from \(A\) has exponent \(\le2U\),
whereas all B-labels exceed \(3U\) and are outside \(A\). Removing
at most two labels from \(AB\) subtracts no more than the logs of
the two largest B-labels. At least three B-labels remain. Then
\(\log\sqrt y/L-\log(bG)/L=\log(B/G)/L-t>9U-U>U\), so this label
is outside the collar. No pure one- or two-deletion receiver on this
wider geometry can coincide, and none of our receivers spends any
raw-only receiver.

### The actual fixed-target rare-source bills

For \(d\) in the collar, necessarily
\(\sqrt x\,x^{-U}<d<\sqrt{1.5x}\) and \(v\asymp x/d\).
On genuine rows a prime dividing \((y,N)\) must equal \(P=N-y\).
The \(O(1)\) choices \(P\mid N,\ P\ge x/2\) can be excluded from
the start: all their possible source and receiver weights combined
are bounded by \(L^2\tau(y)^C=x^{o(1)}\). Hence \((d,N)=1\)
on the retained rows.

Here is an elementary upper bound that will be used for all rarity
bills. At any fixed \(H\) equal to \(d\), or \(dk\) with \(k\) chosen
below, let \(Y=x/H\ge x^{.44}\). Keep genuine prime \(N-Ha\) on
\(a\asymp Y\), and require \(a\) to be \(W\)-rough and to avoid an
arbitrary subset \({\cal T}\) of the two banks (3).
Sieve the affine forms \(a,N-Ha\) using
\(z_0=x^{.01}\) and \(R=x^{.06}\), excluding:
- the root of \(a\) for primes \(\le W\) and in \({\cal T}\);
- the roots of \(N-Ha\) for primes \(\le z_0\).

Both banks lie below \(z_0\) for all sufficiently large \(x\).
The genuine prime lies above \(z_0\); the imposed root exclusion
is thus a majorant. Let \(\nu(r)\le2\) count excluded residues
and \(g(r)=\nu(r)/r\). Since \(N\) is even and \((H,N)=1\), there is
only one excluded root modulo 2. In particular every \(g(r)<1\).
The elementary Selberg upper gives
\[
 \#\{\text{the true rows at }H\}
 \ll Y\prod_{r\le z_0}(1-g(r)) + R^6.                     \tag{7}
\]
For a direct proof define \(h(r)=g(r)/(1-g(r))\) on primes with
\(g(r)>0\), and \(G(R)=\sum_{a\le R}\mu^2(a)h(a)\) on their products.
The Selberg square with optimized \(\lambda_1=1\), moduli \(a\le R\),
has principal term \(Y/G(R)\) by the standard diagonalization
\(\sum_{a,b}\lambda_a\lambda_b g([a,b])
=\sum_c h(c)^{-1}(\sum_{a:c\mid a}\lambda_a g(a))^2\).
The explicit minimizing weights obey
\[
 |\lambda_a|\le \prod_{r\mid a}(1-g(r))^{-1}\le a
\]
because for \(r\ge3\) at most two roots are excluded, and for 2
at most one. CRT on every interval bounds the absolute endpoint
error by \(\sum_{a,b\le R}ab\,\nu([a,b])\ll R^6\).
In the full finite expansion \(\prod_r(1+h(r))\), the normalized
weight of a product corresponds to independent inclusion of prime
\(r\) with probability \(g(r)\). Its expected log is at most
\(2\sum_{r\le z_0}\log r/r=(.02+o(1))L\).
Markov retains at least half the expansion on products \(\le R\)
for large \(x\). Thus \(G(R)\gg\prod_r(1-g(r))^{-1}\), proving (7)
with one constant independent of \({\cal T}\). This finite expansion
is only a computation of the Selberg principal, not a distribution
assumption for the actual prime rows.

For \({\cal T}=\varnothing\), the product in (7) is
\(\ll\mathfrak S(N)/(wL^2)\). Indeed for \(r\le W\), outside the fixed
prime 2, the ordinary \(1-2/r\) factor is corrected by
\((r-1)/(r-2)\) for either \(r\mid N\) (coincident roots) or
\(r\mid H\) (unit constant on the prime form). The target corrections
are bounded by their product in \(\mathfrak S(N)\); all primes in
\(H\) exceed \(W\) so no slope case actually occurs below \(W\).
For \(W<r\le z_0\) the base factor \(1-1/r\) gets a correction
\((1-1/r)^{-1}\) at \(r\mid H\), with total \(1+o(1)\), since
\(\sum_{r\mid H,\ r>W}1/r=o(1)\) uniformly for \(H\le x\).
Mertens gives \(O((\log W)^{-2}\log W/\log z_0)=O(1/(wL^2))\)
for the remaining factors. For each \(r\in{\cal T}\) not dividing \(NH\)
the new factor relative to the base is \(1-1/(r-1)\). Omitting primes
of \(NH\) changes the bound by at most \(1+o(1)\); all banks start
above \(W\) and both \(N\) and \(H\) are polynomial size. Hence (7) is
\[
 \ll \frac{Y\mathfrak S(N)}{wL^2}
                  \prod_{r\in{\cal T}}(1-1/(r-1)) + R^6. \tag{8}
\]

For insufficient \({\cal B}\) labels, choose a random
\({\cal T}\subset{\cal B}\) by including each genuine bank prime
with probability \(1/2\). For any actual \(v\), the probability that
it avoids \({\cal T}\) is exactly \(2^{-\omega_{\cal B}(v)}\).
The indicator of fewer than \(j\) labels is bounded by \(2^j\)
times this probability. Average (8) at \(H=d\); its principal product
becomes \(\prod_{r\in{\cal B}}(1-\frac1{2(r-1)})\), and the endpoint
error is \(O(2^j R^6)\). For no anchor use \({\cal T}={\cal H}\)
deterministically. By prime Mertens the resulting two main terms,
relative to \(Y\mathfrak S(N)/(wL^2)\), are
\[
      O(\ell^{.10\log2-.10}),\qquad O(\ell^{-.04}),        \tag{9}
\]
respectively. Here \(\sum_{r\in{\cal B}}1/r=.20\log\ell+O(1)\) and
\(\sum_{r\in{\cal H}}1/r=.04\log\ell+O(1)\).
This uses no independence assumption on actual rows; the only
randomization is of which exclusions enter the same valid upper sieve.

If no macro occurs in \(v\), then \(P^+(v)<C_y\le1.5x^\epsilon\).
Multiply actual prime factors of squarefree \(v\) until their
product \(k\) first exceeds \(x^{.05}\). This is possible since
\(v\ge x^{.49}\), and
\(x^{.05}\le k\le1.5x^{.05+\epsilon}\).
Now \(a=v/k\) is \(W\)-rough and
\(Y=x/(dk)\ge x^{.44}\) for large \(x\), with \(H=dk\) unit to \(N\)
on the actual rows. For an upper bound sum (8) with
\({\cal T}=\varnothing\) over all such \(k\), counting extra
factorizations positively. The harmonic multiplier is
\[
 \begin{split}
 \sum_{\substack{k\ge x^{.05}\\P^-(k)>W,\,P^+(k)\le1.5x^\epsilon}}
                  \frac{\mu^2(k)}k
 &\le e^{-.05/\epsilon}
    \prod_{W<r\le1.5x^\epsilon}(1+r^{1/(\epsilon L)}/r)\\
 &\ll e^{-.05/\epsilon}\,\epsilon/w .
 \end{split}                                             \tag{10}
\]
For the final bound the change over the unweighted Euler product is
bounded uniformly, since
\(\sum_{r\le1.5x^\epsilon}(r^{1/(\epsilon L)}-1)/r
\ll (\epsilon L)^{-1}\sum_{r\le1.5x^\epsilon}(\log r)/r\ll1\).
This proves the shifted all-small upper without any smooth-number
asymptotic or theorem for moving tilted weights. Its endpoint error,
summed over all true \(d,k\), is \(O(x^{.5+.05+\epsilon} R^6)\)
up to fixed constants, hence \(O(x^{.93})\) eventually. The errors
from (9) and the baseline (8) total \(O(x^{.5}2^j R^6)\).
Both are negligible even after multiplying by the two logarithmic
weights.

Finally the total reciprocal mass of the allowed collar d-support is
\[
 \sum_d\frac1d\ll \frac{U}{w}\exp\left(-\sum_{r\in{\cal B}\cup{\cal H}}
                                                      \frac1r\right)
           \ll\frac{U^2}{w\epsilon}.                    \tag{11}
\]
Split the full collar d-range into \(O(1+UL)\) fixed-ratio intervals.
Sieve the single form \(d\) by the same proof of (7), requiring
\(W\)-roughness and both banks avoided. Its bound is
\(O(D/(wL)\exp(-\sum_{r\in{\cal B}\cup{\cal H}}1/r)+R^6)\) on an
interval of length comparable to \(D\asymp x^{1/2+o(1)}\).
Divide by \(D\) and sum; the endpoint errors are power-small.
Mertens gives the extra product \(O(U/\epsilon)\).
The \(pA\) subfamily separately admits \(O(U^2/w)\) by fixing \(A\),
using \(O(U)\) reciprocal prime mass in its allowed \(p\) interval
intersected with \(p\ge x^{.45}\), and \(\sum_A 1/A\ll U/w\) by its
rough small-cloud Euler product.

Multiplying by the two logarithmic factors and summing the \(Y=x/d\)
upper gives the uncharged even bill
\[
 \ll x\mathfrak S(N)\frac{U^2}{w^2\epsilon}
    \left(\ell^{.10\log2-.10}+\ell^{-.04}
                   +(\epsilon/w)e^{-.05/\epsilon}\right)
       +O(x^{.94}).                                     \tag{12}
\]
The odd bill is \(O(x\mathfrak S(N)U^3/(w^2\epsilon))+
O(x^{.94})\), by its extra \(U\) in (1).
Using \(U/w=100\log\ell\), \(\epsilon=\ell^{-.01}\), and
\(.10-.10\log2-.01>.020\), both are
\(O(x\mathfrak S(N)\ell^{-.01})\). This proves (4) on the stated strict
collar.

This is a payment inside the **same** fully completed moving-cutoff
score. It neither changes the fixed-target calibration
\(\mathfrak S(N)|J|[Q_\epsilon(.5)-1]\) nor bounds the unselected safe
terms. Section 4 prices additional sources with bank labels. The remaining
wide collar and the large exterior/safe residual after reserving the
used receivers remain unpriced. The general bank-free theorem cannot be added to
another bound using any of its receivers unless disjointness is
checked. It does not prove binary Goldbach.

## 4. Five-label orbits: all odd total ranks and both macro ranks even

Keep precisely the preceding parameters and the genuine wide gap.
An actual collar pair \(\{d,v\}\) has two full macro products \(M_d,M_v\);
its actual \(C_y\)-small products are \(S_d,S_v\).
There is another simultaneous payment: **all odd-total-rank raw
collar contributions and all even-total-rank contributions with both
macro ranks even** have a nonnegative total after adding distinct
actual positive safe receiver weights, up to
\(O_{J_0}(x\mathfrak S(N)\ell^{-.01})\).
It also covers selected mixed macro parities by the exact condition below.
No minimum polynomial prime exponent is imposed on \(d\) or \(v\);
the base roughness is still the same \(W\).

### Canonical bank orbits and abundant actual labels

Let \({\cal K}={\cal B}\cup{\cal H}=(x^{3U},x^{\epsilon/2}]\).
Partition its **logarithmic exponents** into bins
\((3U2^i,3U2^{i+1}]\), truncated at \(\epsilon/2\).
For each actual \(y\), pick the first (least index) occupied bin,
discard its two successor bins, then repeat until five choices
have been made. In each chosen bin take the least actual prime
of \(y\) in that bin. If the construction fails, at most twelve
bins contain all of \(y\)'s \({\cal K}\)-labels: at most four choices
each discarded at most three occupied bins including itself.
There are \(O((1+\log\ell)^{12})\) possibilities for the set of
at most twelve bins, since the total number is \(O(\log\ell)\).
After removing such bins the forbidden bank still has harmonic
\((.25-.01)\log\ell+O(1)\), by prime Mertens (each bin costs
\(O(1)\), uniformly even at the starting exponent \(3U\)).
Therefore in each possible failure both \(d\) and \(v\) avoid
this same fixed remaining bank. Without the original bank-free
condition the d reciprocal mass bound underlying (11) is
\(O((U/w)\ell^{-.24})\) when this arbitrary bank is excluded.
Equation (8) on the true prime v-leg supplies a second factor
\(O(\ell^{-.24})\). The sum of both logarithm-weighted absolute
raw scores on all failures is thus
\[
 \ll x\mathfrak S(N)\frac{U}{w^2}\ell^{-.48}
                                  (1+\log\ell)^{12}
       +O(x^{.94})
 \ll x\mathfrak S(N)\ell^{-.23}(1+\log\ell)^{14}.
\tag{13}
\]
The fixed-ratio subdivision on \(d\) and the complete floors in
(7) are valid for every remaining bank; multiplying those
power-small errors by the same \((1+\log\ell)^{12}\) is harmless.

On the other rows write the five labels as \(r_1,\ldots,r_5\).
Their exponents \(u_i=\log r_i/L\) satisfy \(u_1>3U\) and
\(u_{i+1}\ge4 u_i\). Any two different subset exponent sums
differ by more than \(2U\): after the largest differing label of
exponent \(u\), at most \(u/3\) can be lost to all smaller ones.
Group all divisor pairs with the same **unordered** allocation
of the other primes, allowing the named five labels to change
sides. The two outside-label complementary factors are distinct:
if equal their squarefree coprimality would force both to be 1,
whereas the five removed labels have product at most
\(x^{5\epsilon/2}<x\le y\). Orient within each group by using
the side with the smaller of these fixed outside-label factors.
Each oriented logarithm differs from the next by more than
\(2UL\); hence among all the thirty-two divisor pairs in a group
at most one can meet the actual collar \(|\log(d/\sqrt y)|<UL\).
Moving any selected labels between sides preserves the group.
If a divisor \(e\) is either side of a collar pair, deleting a
nonempty subset of these selected labels from \(e\) places the
new divisor below \(R_-(y)\), because the removed exponent
exceeds \(3U\) and \(e\) started at height \(\le\sqrt y\,x^U\).

### Paying the actual odd and even raw terms

Take first **odd total rank** and a raw debit. Then
\(A_y(d)=-2tL,\ \mu(d)=-1,\ \mu(v)=+1\). At least one side \(e\)
has at least three of the five labels. From this side remove
two of them if \(e=d\), or one if \(e=v\), keeping at least one
label on that same side. Write \(b\) for the resulting safe
divisor. Since the removed labels are all actual small primes,
\(\mu(S_b)=(-1)^{\#\text{removed}}\mu(S_e)=-\mu(M_e)\) and
\(M_b=M_e\). Formula (2) now yields \(C_y^{\rm pair}(b)=2\log M_e\)
if \(\mu(M_e)=-1\), and \(2\log S_b\) if \(\mu(M_e)=+1\).
The first is at least \(2\epsilon L\), the second at least \(6UL\)
by the retained label. Either is larger than the entire raw debit.
This does not require any macro-prime occurrence on the chosen
side or a bound on its total small product.

For **even total rank**, on a negative raw source
\(\mu(d)=\mu(v)=-1\) and its debit is \(\log y\). Suppose one
macro-even side \(e\) of that pair has at least two of the five
labels and \(\log S_e\le .05L\).
Then \(\mu(S_e)=-1\), and deleting either single label gives
\(C_y^{\rm pair}(e/r)=2\log M_e> .87L\) for large \(x\), since
\(\log e\ge(\tfrac12-U)L\). The two distinct safe weights
together exceed \(\log y\). This condition includes a mixed
macro parity whenever its even side satisfies those two actual
conditions. For both macro ranks even there is always a side
with at least three of the labels, and it remains only to price
the exceptional amount of **actual** small-prime factor size.

If either \(\log S_d>.05L\) or \(\log S_v>.05L\), select a
genuine squarefree divisor \(k\) of that small part with
\(x^{.05}\le k\le1.5x^{.05+\epsilon}\) by first crossing, as
above. On the v-leg the prior fixed-target proof (8) and (10)
applies without change: a complete factorization of \(v\) into
small labels is not needed for the extraction. On the d-leg,
at every fixed \(k\), sum \(1/d\) using \(d=ka\) and sieve
\(W\)-rough \(a\) over the d collar divided by \(k\).
The full range is at height \(\ge x^{.43}\) for large \(x\)
with log-width \(UL+O(1)\). The single-form argument of (11)
without a bank gives \(O((U/w)/k)\) including its power-small
endpoint share, uniformly in such \(k\). Sum (10) and then
apply the two-form v bound at \(H=d\).
Together the two costs are at most
\[
 \ll x\mathfrak S(N)\frac{U}{w^2}
                 \frac{\epsilon}{w} e^{-.05/\epsilon}+O(x^{.94}),
\tag{14}
\]
including the two logs. In particular this is \(o(x\mathfrak S(N)
\ell^{-.01})\). This upper uses the correct shifted prime from
the original \(N\) throughout.

Each orbital receiver belongs to the same group as its only
collar source. There is no collision across groups or in the
two singleton choices from an even source. A row of odd total
rank cannot share a receiver with a row of even total rank.
This proves the additional claim with the explicit bills
(13) and (14), including all actual parity cases stated.

### Combining with the first packet

Use the five-label method wherever its sign and capacity conditions
hold, then apply the bank-free method to the remaining bank-free
sources only. This does not spend a receiver twice, even for mixed
macro parity. Indeed if \(b=v/B\) arose from a bank-free source
\(d\), all primes of \(y/b=dB\) belonging to the common bank
\({\cal K}\) are exactly the \({\cal B}\)-labels of \(B\). A
five-label receiver is restored to a collar side by multiplying
by at most two named \({\cal K}\)-primes. They would have to be
among those \(B\)-labels, but after restoring at most two,
at least three labels of exponent \(>3U\) remain removed.
The reconstructed side lies below \(\sqrt y\,x^{-U}\), not in
the collar on either orientation. This proves exact disjointness.
For both macro parts even versus non-even types one may also note
that all the receivers preserve the unordered macro allocation.

This extends the literal deletion geometry of the
[earlier collar theorem](../direct_literal_collar_payment/Proof.md)
on its noticeably narrower gap, not by extrapolating that
theorem's estimates. Receivers are genuine terms from the same
completed score and cannot be spent again on any other proposed
debit without checking overlap. In particular no blanket
disjointness from all other safe-payment schemes is asserted.
The remaining even-type cases, including both macro ranks odd
with bank labels on \(d\), and the residual safe scores after
these payments still require a global signed bound; the calibration
is unchanged. There is no lower bound here for the whole binary
prime-pair count.
