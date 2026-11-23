# Far-negative paths of a charge-three cost-37 field

Suppose \(A\) is a hypothetical Conway graph. Assume the actual unit populations \(U_{1,21},U_{0,26},U_{2,28}\) are zero. These hold, in particular, on the rank-36 five-type palette \(\{020,125,127,226,337\}\). The result below is not a population cap or a palette exclusion.

**Theorem.** In any actual \((3,37)\) field \(b\), its two positive vertices \(p,q\) are nonadjacent, both their common neighbours are negative, and the seventeen negative vertices anticomplete to \(\{p,q\}\) induce a forest of paths, each with at most six vertices.

Let \(D=3I-A\) and \(D_X=D1_X\). A marking of charge \(a\) satisfies \(Ab=-4b-2a\mathbf1\), hence \(b\cdot d_i=7b_i+2a\) for \(d_i=D e_i\). The graph identity gives \(D^2=7(3I-A)+2J\), so
\[
 \|D_X\|^2=21|X|+2|X|^2-14e(X).
\]
Adding the all-ones vector reduces the charge by 9 and changes the squared norm by \(99-22a\) when the old charge is \(a\). Negation reverses charge without changing squared norm. These are literal graph-field shifts, not independent residual coordinates.

Recall the [short-shell unit classification](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units). In particular an actual \((3,37)\) is unit: a coefficient at least \(+2\) can be subtracted at its ordinary mark to get charge two and cost at most 20; a coefficient at most \(-2\) can be added at its mark to get charge four and cost at most 44, where equality forces all entries nonpositive but the pivot has become \(+1\). Likewise \((1,21)\) and \((2,28)\) are unit, and the minimum charge-one cost is 21. Because \(U_{1,21}=0\), the raw neutral cost-26 shell is absent as well: orient a nonunit entry to be at most \(-2\) and add \(d_i\) there, producing charge one and cost at most \(26+23-28=21\), with equality requiring an actual unit \(U_{1,21}\).

The \((3,37)\) field has two positives and 35 negatives by its signed sum and squared norm. If \(p,q\) were adjacent then \(b-d_p-d_q\) would have charge one and norm \(37+36-2(14+12)=21\), forbidden. If a common neighbour \(x\) of \(p,q\) were zero then \(b-D_{\{p,q,x\}}\) would be neutral with cost \(37+(81-28)-2(14+18)=26\), forbidden. In addition no mate edge at \(p\) (or \(q\)) can have both sites zero: subtract the triangle mark for \((p,x,y)\) to obtain \(37+39-2(7+18)=26\). These are the same true-root properties as in [the earlier charge-three positive-pair argument](panel-heights.md).

Each of \(p,q\) sees ten negative sites, by its eigen-row and their nonadjacency. Their two common neighbours are negative, so there are eighteen negatives in their open-neighbourhood union. The other seventeen, denoted \(F\), lie away from \(p,q\). Every negative site has internal negative degree \(2+d_{\{p,q\}}\), from \(Ab=-4b-6\mathbf1\). Thus each member of \(F\) has full degree exactly two in the negative shore, and the induced degree in \(F\) is at most two.

## Short transforms exclude long paths and all cycles

For any \(X\subseteq F\), put
\[
 w=2b+D_X-D_{\{p,q\}}+\mathbf1.
\]
If \(r=|X|\), this field has charge \(r-5\). The marked-set norm and dot formulae give
\[
 \|w\|^2=105-13r+2r^2-14e(X).
\]
For example, before the constant fold the base \(2b\) has squared norm 148, the shift \(D_X-D_{\{p,q\}}\) has squared norm \(50+13r+2r^2-14e(X)\) by anticompleteness, and its product with \(b\) is \(-r-26\). The pre-fold charge is \(4+r\), so the last constant adds \(11-22r\) to the squared norm.

Seven consecutive vertices on a path, or on a cycle of length at least eight, give \(r=7,e(X)=6\), i.e. an actual charge-two cost-28 field, forbidden. A 7-cycle would instead give cost 14, below its absolute signed-sum floor 22. A 6-cycle gives charge one and cost 15, below its minimum 21.

A triangle \(T\subset F\) is impossible by a separate standard triangle reflection. The field \(-b-D_T-\mathbf1\) has charge three and cost \(37+39-6-33=37\): \(b\cdot D_T=-3\) since each site has value \(-1\). The two original positives would both have value \(-2\), because \(T\) is anticomplete to them, contradicting the unit classification.

For a 4- or 5-cycle \(X\), all its sites exhaust their full negative degree two inside the cycle. Thus every \(y\in F\setminus X\) has \(w_y=-1\). When \(|X|=4\), \(w\) has charge \(-1\) (signed sum \(+11\)) and cost 29, but its negative mass is at least 13 and positive mass at least \(13+11=24\), giving \(\|w\|^2\ge\|w\|_1\ge37\). When \(|X|=5\), \(w\) is neutral of cost 20, but has negative mass at least 12 and hence \(\|w\|_1\ge24\). Both are impossible. This removes every possible cycle and proves the theorem.

## A conditional contact consequence

Let \(Z_p,Z_q\) be the four actual zero neighbours of \(p,q\), respectively. If \(x\in F\) has degree two in the induced path graph, then its full negative degree is already consumed there. Its two common neighbours with \(p\) must lie in \(Z_p\), and likewise its two common neighbours with \(q\) lie in \(Z_q\). Since a pair in \(Z_p\) has already the common neighbour \(p\), each such pair is used by at most one \(x\). Thus the seventeen-site far-negative path graph has at most six internal vertices. More generally let \(e_F\) be its edge count and \(c\) the number of its degree-one vertices whose remaining negative neighbour is in the common two-site set \(N(p)\cap N(q)\). Every internal path site uses two slots in the two six-slot zero-parent decks, and every endpoint not of the indicated common-parent type uses at least one. Hence \(2e_F-c\le12\). This last inequality permits further path types and is not a rigidity assertion.

If \(X\) is an entire six-vertex path, the same transform is an actual **unit** charge-one cost-29 field. Its four internal vertices use four distinct pairs on each of \(Z_p,Z_q\); four distinct pairs cannot fit on just three vertices, so every zero-neighbour of \(p\) or \(q\) touches \(X\). Write \(d_P(y)=|N(y)\cap\{p,q\}|\). The coordinates at \(p,q\) vanish, and those in \(X\) are \(2-d_X(y)\). At other negative sites the coordinate is \(-1-d_X(y)+d_P(y)\le1\). At zero sites it is \(1-d_X(y)+d_P(y)\le1\), because no zero site is common to \(p,q\), and those seeing either touch \(X\). Thus there are no positive doubles. A negative double would, on adding its site mark, give charge two and cost \(29+23+2(-14+2)=28\); a more negative pivot would give a cost below 22. Both are impossible, so the cost-29 field is unit.

The two path endpoints cannot share an attached negative vertex \(y\) with \(d_P(y)=1\). In that case use the same transform with \(X\cup\{y\}\), seven negative sites with seven internal edges and one contact to \(\{p,q\}\). The squared-cost formula acquires \(14e(X\cup\{y\},\{p,q\})\) from the cross term, yielding charge two and cost 28 again. This does not exclude a shared attachment at a common negative neighbour or distinct attachments.
