# The remaining high-rank signed debit when either arm has at least four small tags

Use exactly the original sharp sextic \(H\), \(S=G_b+W\),
\(b=.003\), \(L=\log N\), \(M=|J|N\mathfrak S(N)\), and real
pairing \(x+y=N,\ x\in NJ,\ (x,N)=1\) of the
[rank 5–7 four-small comparison](../sextic_four_small/Proof.md).
Let \(\mathcal Y_\ell\) be its actual rank 5–7 side and
\(Y_\ell=1_{\mathcal Y_\ell}H\).
Define \(\mathcal Y_h\) to be the actual squarefree \(n\) of
odd rank at least 9, with all primes \(>N^{.003}\) and at least
four actual primes \(\le N^{.080}\). Put \(Y_h=1_{\mathcal Y_h}H\),
with its **true sign**, and do not assume it is negative.
On each of these physical supports \(S=H\): the tiny gate
passes, \(Q=0\), and \(W=0\) because the true quotient after
any two least labels still contains a prime \(\le N^{.080}\)
and \(W\) would require floor \(>(.555-.065)/3>.163\).

**Proposition.** On the actual remaining pair rows with at least
one \(\mathcal Y_h\) coordinate and **neither** coordinate in
\(\mathcal Y_\ell\), the complete original signed sum is
\[
                              >-.262M+o(M).
\]
Thus the already priced low-rank union is not counted again.
Every previously priced rough or mixed boundary chamber has
both arms with fewer than four such small tags; this also holds
of all exact tag-count chambers 1-by-2, 2-by-3, 3-by-3, and of
the exact semiprime adverse chambers
[0-by-2](../sextic_true_tag_rebate/MediumSemiprimeAdverse.md) and
[1-by-3](../sextic_true_tag_rebate/SmallSemiprimeThreeTagAdverse.md).
In the retained \(.003\)-rough exterior this accounts for all
remaining nonzero rows with a \(\ge4\)-tag arm. Rank 4 there
cannot be central, since four such factors would have product
at most \(N^{.32}\). The even ranks \(\ge8\) have exactly
zero in the original sextic, and nonsquarefree arms also score
zero there. Those zero products may be removed at no cost.
This is a genuine **debit when the exterior is contracted**,
not a better bound with an unchanged exterior or a Goldbach
conclusion.

## 1. Pointwise majorants and the ordinary high-rank mass

Split \(Y_h\) into five physical groups \(Y_i\), of rank
\(9,11,13,15,\ge17\) odd, respectively. At rank \(r\), let
\(u_1\le\cdots\le u_r\) be the actual own-log angles, set
\(T=1-\sum_{j\le4}u_j\), and put
\[
       C_r(T)=1056\,2^{r-5}+80640\,2^{r-7}(T/(r-4))^2 .
\]
The original high-rank absolute envelope in the
[sextic proof](../sextic_true_tag_rebate/Proof.md) gives
\[
  |H(n)|\le P_r(n):=(\log n)\,C_r(T)\prod_{j\le4}u_j
           \qquad(n\in\mathcal Y_h,\ {\rm rank}\ r).
                                                                    \tag{1}
\]
Indeed its smallest-six product includes the four actual least
angles, and the two smallest of the other \(r-4\) have product
at most \((T/(r-4))^2\). Define \(P_r=0\) off that physical
support, and \(P_i\) as the corresponding group sum. Thus
\(P_i\ge|Y_i|\) on every true row. In estimates of harmonic
volumes, use target-log angles with the same names; this
changes only weights by a uniform \(o(1)\) after dividing by
the logs, not any named physical prime or gate. Every considered
rank is at most 333 by the true \(.003\) floor.

Let \(m_i=m(|Y_i|)\), with exactly the ordinary unopposed
normalization in [the rank 5–7 proof](../sextic_four_small/Proof.md).
After the four least reciprocals are canceled by (1), the
ordinary integrand at fixed genuine first four, whose maximum
is \(v\), is at most
\[
                            C_r(T)b_{r-4,v}(T).
\]
Here \(b_{k,v}(T)\) is the actual ordinary quotient density
\((1_{s\ge v}\,ds/s)^{*k}/k!\): the remaining \(k\) actual
primes are at least the fourth angle \(v\), not necessarily
above .080. The excluded tie at the actual fourth prime and
any repetitions or target prime exclusions are power-small
under the fixed positive floor. This is precisely the genuine
ordinary harmonic of prime products with one true final-prime
slot and the unordered factorial, as before.

The [outward rational checker](check.py) uses the very same
four-least integration of §2 of the rank 5–7 proof. At fixed
\(v\) the three smaller angles give volume \((v-.003)^3/6\);
their scaled sum has the exact three-uniform polynomial CDF,
which is an ordinary volume identity, not a paired model.
For the density recurrence set \(k=r-4\) and \(C_k^*(s)=2^k
b_{k,1}(s)\). Then
\[
 C_1^*(s)=2\,1_{s\ge1}/s,\qquad
      s C_k^*(s)=2\int_{k-1}^{s-1} C_{k-1}^*(z)\,dz .
\]
All terms are positive, and the factor \(2\) is exactly the
marking identity in the normalized recursion. On a mesh
\(1/200\), if \(c_{k-1}[j]\) is the previous scaled interval
upper, the next scaled upper for interval \(i\) is
\(\lceil 2\sum_{j<i+1-200}c_{k-1}[j]/i\rceil\) on its possible
support, a direct outward prefix bound. The exact profile
density factor is \((528+10080(T/k)^2)C_k^*(T/v)/v\).
For the odd tail \(k\ge13\) take \(T^2\le1\) in that coefficient
before making the positive sum. This yields the following
upward constants (the second row is proved below):
\[
\begin{array}{c|rrrrr}
 i & 9 & 11 & 13 & 15 & \ge17\ {\rm odd}\\ \hline
 \overline m_i & .01933 & .00345 & .000534 & .000078 & .0000114\\
 U_i & .373 & 1.232 & 12.850 & 8.679 & 35.095
\end{array}                                                         \tag{2}
\]
In particular all the high odd ranks, not just a selected
finite-low slice of them, are charged.

## 2. A genuine receiver for every group

For every genuine nonnegative compact positive-floor
product source \(Z\) on the opposite arm we show the **actual**
bound
\[
                     \langle Z,P_i\rangle/M
                          \le U_i m(Z)+o(1),                       \tag{3}
\]
and the reflected version. All uses below of a floor tending
to zero are after the fixed-floor true product estimate and
use the physical phase limits of the explicit tiny proof.

For \(r=9,11\), apply the [four named least primes upper](../sextic_four_small/Proof.md#1-a-cheap-receiver-on-precisely-the-four-least-labels)
with cap \(C_r(T)\) replacing \(2112+8960T^2\).
The quotient really is rough at the fourth named prime, even
when many more primes are at most .080, and the true joined
level is still \(h e\le N^{.499}\). The outward four-angle
box upper, with its literal choice of levels and no changes in
the true residue, is included in the checker. It is
\(<.372073\) and \(<1.231676\), respectively.

For an individual odd rank \(13\le r\le333\), put
\(j=(r-1)/2,\ k=j-4\ge1\), and now open the **actual** smallest
\(j\) prime factors into the true modulus \(h\). The normalized
sum of the first \(j\) target-log angles is \(\le j/r\); the
largest of those actual names, of angle \(s\), is
\(\le B_r=1/(j+2)\) since \(j+2\) of the true factors are at
least that large. The quotient is rough at \(s\).
Set \(D_r=.499-j/r>0\); even at \(r=333\) it is strictly
positive. The tested modulus \(h e\) is \(\le N^{.499}\)
at sieve exponent \(D_r\). On fixed literal angle boxes
one can upper-sift at the lower rough floor of the box,
with the cutoff lowered further if needed to give parameter at
least 2. The normalized linear receiver is then \(\le2/(3s)\)
when \(D_r/s\ge3\) and \(\le2/D_r\) otherwise, in the limit of
fixed finer boxes. It can always be majorized by their sum.
The first estimate uses the decreasing upper sieve function
above 3. The second uses its \(2e^{\gamma_E}/s_{\rm lin}\)
branch, choosing a floor at most \(D_r/2\) if necessary.

These upper estimates follow by literal product BV of the
true \(Z\) source in the same genuine reduced residue \(N\bmod he\),
with the target factors accounted for as \(\mathfrak S(N)\).
Opening the larger number of labels adds only fixed divisor
multiplicity, because \(r\le333\). Each named prime is still
polynomially large, and omissions of named or actual source
primes outside \(N\) cost a relative \(1+o(1)\) in their
local reciprocals. No particular completed rank of the
free quotient is supplied by the positive sieve. Its exact
rank only forced the physical order, the limit \(j/r\),
and the floor \(s\), all of which are true on the source
cohort before using the upper.

For a convenient explicit integral upper, replace \(C_r(T)\)
by \(C_r(1)\), let \(v\le s\) be the fourth named angle,
and drop lower floors and extra angle restrictions in the
nonnegative harmonic integral. After the first four
reciprocals cancel, the first three ordered names give
\(v^3/6\). For fixed largest name \(s\), the other \(k-1\)
extra named reciprocal factors lie in \([v,s]\) and give at
most \((\log(s/v))^{k-1}/(k-1)!\) with their order accounted
for. Their physical floor and all labels are kept until this
positive enlargement, not before the genuine progression
estimate. Since
\[
             \int_0^s v^3\frac{\log^{k-1}(s/v)}{(k-1)!}\,dv
                      =\frac{s^4}{4^k},
\]
the resulting bound is
\[
  U_r^{\rm an}
     =\frac{C_r(1)}{6\cdot4^k}
            \left(\frac{2 B_r^3}{9}+\frac{B_r^4}{2D_r}\right).
                                                                    \tag{4}
\]
This is an actual receiver coefficient, not an assumed
opposed rank distribution. It bounds the whole-rank majorant
\(P_r\). Use it separately at \(13,15\), and sum it for
\(17\le r\le333,\ r\) odd, to get the last three bounds in (2).
In particular the exponential factor in the pointwise
envelope is canceled by integration of the actual known
half-list of smaller factors. Direct use of just the
least four names for all ranks would not give these bounds.

## 3. The full high-arm union, excluding every old low arm

The sextic product transfer and the actual prime receiver give
a better signed bound than charging the absolute score.
For \(Y_h=Y_+-Y_-\), with its two **real** positive parts, the
signed \(H\) crossing is
\[
           \langle Y_h,H\rangle/M=m(Y_h)
                       -\langle Y_h,\Pi\rangle/M+o(1).
\]
The true adverse prime term is at most \(3.446 m(Y_+)\);
the prime opponent on the negative part can only help.
The two nonnegative corrections \(Q,W\) can hurt only on
\(Y_-\), with their actual receiver sum at most
\((.852+.52844)m(Y_-)\) from
[the original and medium bounds](../sextic_true_tag_rebate/FullMediumCohort.md).
Since \(1+.852+.52844<2.446\), their *combined* worst debit
is \(2.446\, m(|Y_h|)\):
\[
                \langle Y_h,H+Q+W\rangle/M
                             \ge-2.446\,m(|Y_h|)+o(1).             \tag{5}
\]
All these receivers are applied to the actual hard rank and
least-factor sources at fixed positive floors, with the usual
true angle-box approximation. The argument applies separately in
the reflected interval.

Use \(S=H+Q+W-T_{\rm tiny}\) and keep exactly the original
\(T_{\rm tiny}=A+V+E-D\) at \(b=.003\). The signed \(A\)
transfer costs at most \(.228\, m(|Y_h|)\), \(E\) is null,
and \(D\) costs at most \(.007445\,m(|Y_h|)\), at the natural
scale, by the
[explicit cutoff transfer](../sextic_true_tag_rebate/ExplicitTinyStop.md)
and the [.003 tradeoff](../sextic_true_tag_rebate/ExplicitTinyStopTradeoff.md).
For the harder part \(V\), (3) trivially pays
\(U_i m(|V|)\le U_i(.009042)\) on each rank group.
For the large \(U_i\) groups there is a cheaper **actual paired**
Cauchy bound, as follows.

Keep the old genuine least certificates of \(V\) and their
\(\beta\)-weights. Write \(X_V=(H_*/L)^2\sum_{\rm cert}\beta^{-1}\)
and \(Y_V=\sum_{\rm cert}\beta\), exactly as in the explicit proof.
Apply Cauchy to the true pair **and named certificate** measure.
Decompose each \(|H_*(x)|\,|Y_i(y)|\) term as the product of
\(|H_*(x)|\sqrt{P_i(y)/(L\beta)}\) and
\(\sqrt{L\beta}\,|Y_i(y)|/\sqrt{P_i(y)}\), using zero where
\(P_i=0\). Because \(|V|\) is bounded by the sum of these
named \(|H_*|\) terms, this gives
\[
 \begin{split}
 |\langle V,Y_i\rangle|
   &\le\sqrt{\langle L X_V,P_i\rangle\
                   \langle L Y_V,\, |Y_i|^2/P_i\rangle}\\
   &\le M\,\sqrt{U_i(.017667)^2(.8/b)\,\overline m_i}+o(M).
 \end{split}                                                       \tag{6}
\]
For the first factor use (3) and the true ordinary
\(m(LX_V)\le(.017667)^2\); for the second use the old actual
least receiver \(LY_V\), of coefficient \(.8/b\), with the
true source \(|Y_i|^2/P_i\le|Y_i|\).
At fixed positive floors these are compact weighted genuine
product sources. Removal of the auxiliary floor in the
original \(V\) uses the same physical limits, and the true
common certificate measure remains throughout. The bound
does not multiply norms of independent toy distributions.
The two orientation bounds are identical with their own
reflected interval. Taking the smaller of (6) and the direct
\(U_i(.009042)\) bound gives the checked one-orientation cost
\(<.051688\).

Finally let \(m_h=\sum_i\overline m_i\).
For the high/high overlap **upper**, use nonnegative absolute
score receivers with the cheaper genuine orientation in every
ordered group pair:
\[
 \langle Y_h,Y_h\rangle/M
      \le \sum_{i,j}\min(U_i\overline m_j,U_j\overline m_i)+o(1)
      < .026470+o(1).
\]
For each high/old-low cross upper, use the old actual
\(|Y_\ell|\) receiver on the true high absolute source:
\(\langle Y_\ell,Y_h\rangle/M\le .1212 m_h+o(1)\), and likewise
in the reflected orientation.
The original rows with a high arm **and neither low arm** have
the exact signed sum
\[
 \langle Y_h,S\rangle+\langle S,Y_h\rangle
        -\langle Y_h,Y_h\rangle
        -\langle Y_\ell,Y_h\rangle-\langle Y_h,Y_\ell\rangle .
\]
The old low union thus contributes nothing to the new physical
exterior; it is not used again as a negative credit.
Using (2), (5), (6), and the \(A,D\) terms, the
[exact rational replay](check.py) gives the strict total debit
\[
       <.261028185M+o(M)<.262M+o(M).
\]
No opposite ranks or signs were deleted to obtain it.
