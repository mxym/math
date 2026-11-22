# The signed credit on the complete two-tag ambient

Keep the exact current score \(S=G_b+W\), fixed even target,
\((x,N)=1\), and central interval with normalization
\(M=|J|N\mathfrak S(N)\) of
[the tagged negative credit](TaggedNegativeCredit.md).
Retain its same 961 two-tag cells, and put \(a=.110\).
Define \(\mathcal F_{\rm all}\) to require the two appropriate
**actual** least tags on each arm and all quotient factors
\(>N^a\), without a rank restriction on either quotient.
This is the union of the genuine tagged ambients already used
there, not an independent random factor model.
Let \(\mathcal E\) be the previously priced positive-arm block
from [the positive credit](RoughPositiveCredit.md).

**Proposition.** The complete signed block, including all its
opposite-sign products, satisfies
\[
 \sum_{(x,y)\in\mathcal F_{\rm all}} S(x)S(y)>.156M+o(M).
\]
Thus the .883 comparison of the tagged negative credit holds
with \(\mathcal F_{\rm all}\) in place of \(\mathcal F\):
its unpriced sum now omits **every** row in that actual
two-tag ambient, and the same \(\mathcal E\), with no change
to the score. No sign of the new outside-ambient sum is
asserted. The old \(\mathcal F\) credit is not added again.

On this ambient the score is the original \(H\): the tag
bounds still make \(Q=W=0\) there and pass the .003 gate.
A nonsquarefree row has score zero on that arm. If the
quotient is squarefree, the completed rank cannot exceed
10: its total angle is at most \(.934+O_J(1/L)\) after
the two tags, with quotient floor \(.110\). The minimum
completed rank is 3. Ranks 3–5 are negative by the
[actual tagged sign geometry](TaggedNegativeCredit.md#3-literal-p6-negative-sign-and-three-amplitude-layers).
Rank 6 is strictly negative by its exact even formula.
Rank 7 is negative by \(b_7''(0)\le0\) and \(b_7(0)>0\)
in the exact odd formula, with \(b_7\) the symmetric
unimodal centered slice density. Ranks 8 and 10 are
identically zero: at even rank the complementary subsets
give half of a full difference of the polynomial of degree
six. These are literal own-log slice identities from
[the original sextic proof](Proof.md). Thus the only possible
positive values not in the earlier homogeneous negative
block are at completed rank 9.

Write \(B(n)\) for \(|H(n)|\) on the actual squarefree
one-arm tag cohort with this quotient roughness and all
ranks, and \(B_9\) for its rank-nine part.
For an individual row write \(u,v\) for its two tag angles
with own logarithms and \(T\) for its actual quotient
angle sum. The two tags are literally the two least
primes. The high odd slice envelope in
[the sextic ordinary-tail argument](Proof.md) gives
\[
 \frac{B_9(n)}{uv\log n}
  \le w_9(T):=16896(T/7)^2+322560(T/7)^4 .
\]
Indeed the least-four or least-six product includes the two
tags and two or four of the smallest quotient angles.
Their geometric means are at most the mean \(T/7\) of all
seven quotient angles. On every retained cell this is
\(<410\), with a strict fixed margin. That same 410 bound
also covers **all** other ranks. For rank 3 the cap is
\(\sup_{0\le t\le .170}|F''(t)|=78\). In rank 4 use
\(1680q-528\le1152\) and the quotient product at most \(1/4\).
In rank 5 use \(10080\sqrt q-1056/\sqrt q\le9024\)
and quotient product at most \(1/27\). In rank 6 the
quotient product bound is \(40320/4^4\).
In rank 7 use the exact bounds
\(|b_7''(0)|\le2/(u_{(5)}u_{(6)}u_{(7)})\) and
\(b_7(0)\le7\), giving \(2112/5^2+564480/5^5<410\)
after the two tags are factored out.
Even ranks above 6 have vanishing score as just noted.

In the ordinary mass of \(B_9\) the two tag factors cancel
their reciprocal harmonics. On each tag cell of upper
quotient total \(T_+\), the ordinary seven-factor quotient
density is at most
\[
        \frac{(T_+-7a)^6}{7!\,6!\,a^7}
\]
by the true ordered-simplex formula and \(u_i\ge a\)
on each of its seven distinct actual factors.
The sum of these areas times \(w_9(T_+)\) gives
\(m(B_9)<.00000918\), in the \(M\) normalization
of the other ordinary masses. Genuine own-log and target-log
angles may differ by \(O_J(1/L)\) on these positive floors;
the quoted upper has strict room for that perturbation.

There is also a **real** receiver bound on all \(B\) against
any nonnegative compact actual product source \(Z\).
For each of the 961 cells, open the two actual tags
\(h\) and upper-sift the genuine quotient at exponent \(a\),
at level \(N^{.499-s}\) where \(s\) is the sum of the
tag-cell upper endpoints. The literal moduli
\(hd\le N^{.499}\) give ordinary below-root product BV
with the actual reduced source and target unit mask.
The two tagged primes are omitted from the quotient sieve
with \(1+o(1)\) local cost; actual marked squares and any
higher square factors can be ignored for this upper.
The genuine tag harmonic cancels the two angle
factors as before. The quotient upper coefficient is never
above \(2/.329\), by the monotone upper sieve function
at \(s_{\rm sieve}=(.499-s)/a\ge.329/.110\).
It follows that \(\langle Z,B\rangle\) and its reflection
are at most \(U_B m(Z)M+o(M)\), with
\[
                  U_B\le 410\frac{2}{.329}
                              \frac{961}{500^2}<9.581 .
\]
Actual marked products sharing a prime across the two
coordinates are absent from all target-unit rows; these are
the same local coincidence exclusions as in the earlier
tag-cell proof. No second use of the true .555 prime-opponent
rebate occurs here. In particular \(B_9\) is a genuine
fixed-floor, finite-rank source for this inequality.

The earlier checker gave the valid lower
\(.1568695687\ldots M\) on the actual rank-3–5 block.
All additional negative products on the complete ambient
are contained in one of the two reflected \(B_9,B\) pairs.
Their total modulus is \(<.000176M+o(M)\). Actual
additional products of the same sign are nonnegative and
need not be estimated. The
[attached exact replay](check_complete_tagged_credit.py)
verifies all rational upper constants and the strict
remaining \(>.156M\) bound. This pays the signed block as
a whole, with no assumption that the two actual quotient
ranks are independently distributed.
