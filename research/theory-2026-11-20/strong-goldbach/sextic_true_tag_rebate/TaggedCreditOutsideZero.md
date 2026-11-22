# The earlier two-tag credit outside the full zero-tag self-pair

Keep exactly the physical score and sets of
[the complete tagged comparison](CompleteTaggedCredit.md)
and [the full zero-tag self-pair](FullZeroTagAffineSelf.md).
In particular \(M=|J|N\mathfrak S(N)\), the target is fixed even,
\(x+y=N\), \(x\in NJ\), and \((x,N)=1\).

**Proposition.** The earlier **same** complete tagged credit
\[
  \sum_{\mathcal F_{\rm all}\setminus\mathcal Z_{.080}}
             S(x)S(y)>.156M+o(M)
\]
still holds after excluding the entire actual zero-by-zero pair.
Thus (1) of the full zero-tag comparison and this lower can both
be used, on disjoint rows; the old lower on \(\mathcal F_{\rm all}\)
is not added to them. In the full zero-tag comparison there is
no need to forfeit the old \(.156M\) lower or charge a separate
\(.000176M\) to its exterior piece. The replacement increases
the proved bound by \(>.608M+o(M)\) in place of the former
\(.110\) self-pair and low mixed strip, with the exterior reduced
by the actual enlargement. No sign is asserted for that exterior.

In each original tag cell, the two least actual primes lie in
half-open log intervals \((i/500,(i+1)/500]\) and
\((j/500,(j+1)/500]\), and the remaining quotient has no prime
at most \(N^{.110}\). Because \(.080=40/500\) is a grid point,
the genuine number of primes at most \(N^{.080}\) on that arm
is exactly the number of its two upper endpoints at most .080.
This includes the boundary in the nonzero-tag side. Therefore
each original paired cell either belongs wholly to
\(\mathcal Z_{.080}\) or is disjoint from it. Discard the first
kind at the summation stage; do not re-estimate any of the remaining
individual cells. In particular their true receiver, true
two-arm upper ambient and the three separately weighted amplitude
inequalities in the original joint intersection calculation
remain unchanged.

This gives a lower on the original rank-three-through-five block
outside \(\mathcal Z_{.080}\). For **all** additional ranks on
that exterior the original sign classification remains valid.
Use the same proved gross negative upper \(<.000176M+o(M)\)
from the two \(B_9,B\) orientations on the full original chamber;
this bounds the negative part of any subset. Products not
in either crossing are nonnegative or zero, so no other
negative term has been discarded. The resulting outward lower
is \(>.1566932153M+o(M)\).

Run:

    python3 -OB check_tagged_credit_outside_zero.py

The [exact replay](check_tagged_credit_outside_zero.py) uses the
prior certified 961 cell masses by hash, omits only entries with
actual tag counts \((0,0)\), and subtracts the old \(.000176\)
once. The other count masks printed by the checker only split
this same lower into arithmetic components. They give no
information about the rows outside the corresponding
\(\mathcal F_{\rm all}\) subcells.
