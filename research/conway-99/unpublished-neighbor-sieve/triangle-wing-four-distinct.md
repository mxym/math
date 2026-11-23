# Four distinct 18-wing triangles at a root without a 24-wing triangle

At every root of a hypothetical Conway graph, either an incident triangle has a wing component of size at least 24, or at least **four distinct** incident triangles have an 18-site wing component. Consequently, writing \(b_{18}\) for the number of literal triangles whose largest wing component is 18 and \(b_{24}\) for the number with a component of size at least 24,
\[
 b_{18}+4b_{24}\ge132.
\]
This counts distinct triangles, not multiplicities of wing components. It does not prove \(b_{24}>0\). There is no Seidel rank, Fano, or short-shell assumption.

Use the [standard split-axis chart](big-triangle-wing.md). The [three-distinct theorem](triangle-wing-three-distinct.md) leaves only roots with at least three distinct original axes carrying cubic split groups if there is no larger split group. If there are exactly three such axes, the even number of cubic groups is either four or six. [Six were excluded](triangle-wing-six-cubic.md). We rule out four below.

## Reduction to two theta components

There is one doubled axis \(a\), with two cubic groups, and two single axes \(b,c\), each with one cubic group. Suppressing chains of degree-two split vertices does not produce a loop (the equal-parity end columns would pair positively or would cancel and annihilate the third column), or a path between different splits of the same original axis (the end fields agree up to sign but have zero contact with the other own cell). The two groups at \(a\) have total degree six and can only send paths to \(b,c\), whose total degree is also six. Thus there is no \(b\)-to-\(c\) path. The two defect spans at \(a\) are orthogonal by the shared-axis Gram formula. Therefore a cubic group at either \(b\) or \(c\) cannot receive paths from both groups at \(a\): its zero sum would have a singleton in one of the orthogonal spans. Accordingly the cubic core consists of two separate thetas, with original endpoints \(a,b\) and \(a,c\). Other dirty components, if any, are separate degree-two four-cycles.

Each theta has uniform path parity, chains have length at most four, and \(333,444,442\) were excluded by the [theta-path argument](triangle-wing-theta-paths.md), whose relevant proofs are internal to the component. An odd theta therefore has list \(133\). The two long paths are all matching cells and unit by the [universal three-edge lemma](triangle-wing-three-distinct.md#two-local-facts-used-beyond-the-preceding-two-cubic-case). Their internal axes cannot be disjoint, by the [disjoint-overlap identity](triangle-wing-theta-disjoint.md#the-exact-overlap-identity-when-the-internal-axes-are-disjoint): all outside cells touching one of the endpoints are in different split groups, and any other outside cell touches at least one internal axis when the long axes are disjoint. Thus the fields have no common support outside the theta in that case. The middle corrections both vanish for matching cells, whereas the direct cell always has \(m+u>0\), in the notation of that identity. Hence any odd theta here is crossed.

A short path of length two has its unique middle axis distinct from either end. The same holds for all internal axes of a length-three or length-four path, by the disjointness of same-sign chain cells and the different original endpoints. Thus an original edge joining a theta's two endpoint axes, if used by that theta, must be its direct path.

## The even \(422\) case cannot occur

Consider an even \(422\) theta between \(a,b\), with one length-four chain. Its unit long field is supported on its four long cells, on four further signed sites of the short endpoint cells at each end, and the entire cell on the two unused axes of the long path. This is the [length-four support calculation](triangle-wing-theta-paths.md#a-single-length-four-path-and-two-short-paths): each matching end cell has four cross contacts to its two other endpoint cells after its first-layer parent and its own mate; every other cell on an endpoint axis is in a different split group; and nonpath cells on internal axes have zero long value. The unused pair cell sees four opposite signs from the long cells, none from a signed short endpoint cell (different split group on their shared short middle axis), so its internal degrees must be zero or two. It is empty or clean.

If it were clean, the same parity contradiction as in that calculation applies, using \(C_{ab}\). Because the theta is even, \(C_{ab}\) is outside it and belongs to different split groups at \(a,b\): if it were in either of the specified cubic groups, its chain would have to be direct or repeat an endpoint original axis. Thus its sites have zero long value, no signed contact at the theta endpoints, one contact of each sign from the two long interiors, and one further signed contact from the unused-pair grid. A zero site cannot have three signed neighbours. Consequently the unused-pair cell is empty. It cannot be in a pure four-cycle, all of whose own cells are matchings. It is therefore in the other theta. This one must be even too: the only possible empty cell of an odd \(133\) is its direct edge, and a direct edge of the other theta includes the common endpoint \(a\), which is not unused. The empty cell in the other even theta must be on a short path, since long cells are matchings, so its two axes are \(c,d\), with \(a-d-c\) a short path in that theta.

In particular \(c\) is unused by the long \(a\)-to-\(b\) chain. As \(a\) is doubled, the original edge \(ac\) leaves \(a\) in one of the two groups; it cannot leave in the even \(a\)-to-\(c\) theta, so must leave in the \(a\)-to-\(b\) theta. Since \(c\) is unused by the long chain, this forces the short path \(a-c-b\). If the \(a\)-to-\(c\) theta is \(222\), its own edge \(ab\) (not used by the even \(a\)-to-\(b\) theta) forces the short path \(a-b-c\), repeating \(bc\). If it is \(422\), the same empty-cell argument makes \(b\) an unused axis of its long chain (its empty unused pair is in the first theta), so the path starting with \(ab\) is again the short \(a-b-c\). This is the same repetition. The \(422\) case is excluded.

Two even \(222\) thetas also repeat \(bc\) in exactly this way. We now only need one or two crossed odd thetas, with the other theta all-short if even.

## A common far-cell condition for a crossed theta

For a crossed odd theta with long paths \(a-i-j-b\) and \(a-k-i-b\), let \(p,q\) be their start fields. The shared internal axis \(i\) forces \(p\) zero on the \(q\)-end there, so the shared-axis Gram gives \(p\cdot q=0\). The direct cell \(C_{ab}\) is empty and \(p=q=1\) on all four sites there. Each long field is unit, uses eight negatives in its end cells, four positives in its middle, and four positives in the direct cell. It vanishes on the other path's ends by orthogonality and its middle by the shared axis; it also vanishes on non-theta cells touching its ends or internal axes. Hence its other six positives and six negatives fill the three cells on the complement of its four original axes. These will be called its far cells.

The common far cell \(F\) is on the two axes unused by the two long paths together. The four agreements at the direct cell and orthogonality force \(q=-p\) on every site of \(F\). At \(x\in F\), the disjoint-axis defect formula gives \(1+p_x\) contacts in each negative \(p\)-end cell, \(1-p_x\) in the positive \(p\)-middle, and one in the direct cell because its column \(-p-q\) is zero at \(x\). These contribute \(-3p_x\) to \(Ap\). Consequently the other signed neighbours, in the three \(p\)-far cells, must sum to \(-p_x\). The same argument gives the required \(q\)-far sum \(-q_x\). In particular \(F\) cannot be clean: it would have two internal neighbours and none in either other \(p\)-far cell, because they share one of its axes. Its far signed sum would then be even, not \(-p_x\).

Recall also the [four-site outer budget of a separate four-cycle](triangle-wing-theta-no-cycles.md#the-outer-cell-budget-of-any-separate-four-cycle): in its complementary triple of axis cells the induced graph is empty or one four-cycle plus isolates. In particular no one of those three cells can be an actual matching cell, which would already occupy all four nonisolated sites but is not a four-cycle itself.

## One odd and one all-short theta

Let the odd theta join \(a,b\). Because the \(a,c\) theta is even, the original edge \(ac\) leaves \(a\) in the odd group. Thus \(c\) is a first internal axis of one long path of the odd theta. It cannot be its shared internal axis: that would make two degree-two groups at \(c\) in addition to its own cubic group, exceeding the six axis pairs. Therefore the odd paths have labels
\[
 a-i-j-b,\qquad a-c-i-b
\]
with the direct \(ab\); denote the two unused axes by \(d,e\). The three middle axes of the all-short \(a,c\) theta are necessarily \(j,d,e\), the original pairs left at doubled \(a\). The common far cell \(C_{de}\) of the odd theta must be dirty by the far condition. It is in neither theta, so must belong to a separate four-cycle.

This cycle avoids doubled \(a\); its complementary triple is \(\{a,u,v\}\) with \(u,v\) chosen in \(\{b,c,i,j\}\). Neither may be \(c\) or \(i\), since \(ac,ai\) are matching ends of the odd theta. Hence the pure cycle's axes would be \(\{c,i,d,e\}\). But all three pairs \(ci,cd,ce\) have already been used in the two thetas (\(ci\) the odd middle and \(cd,ce\) the all-short ends). No cycle on those four axes can use \(c\), a contradiction.

## Two odd thetas

Write the long paths of the two crossed thetas as
\[
\begin{array}{c|cc}
ab & a-i-j-b & a-k-i-b\\
ac & a-d-h-c & a-e-d-c .
\end{array}
\]
Here \(a,b,c,i,k,d,e\) are the seven distinct original axes, since at doubled \(a\) the first cubic group uses \(b,i,k\) and the second uses \(c,d,e\). The remaining internal choices are \(j\in\{c,d,e\}\) and \(h\in\{b,i,k\}\). The exact nine possibilities, showing any duplicated original edge or the retained representative number, are
\[
\begin{array}{c|ccc}
j\backslash h & b & i & k\\\hline
c & bc & ci & \mathrm{I}\\
d & bd & di & \mathrm{II}\\
e & \mathrm{I}' & \mathrm{II}' & \mathrm{III}
\end{array}
\]
Here \(\mathrm{I}=(c,k)\), \(\mathrm{II}=(d,k)\), \(\mathrm{III}=(e,k)\). Interchanging the two thetas by \(b\leftrightarrow c,\ i\leftrightarrow d,\ k\leftrightarrow e\) sends \((j,h)\) to the renamed \((h,j)\); it takes \(\mathrm{I}\) to \(\mathrm{I}'=(e,b)\), \(\mathrm{II}\) to \(\mathrm{II}'=(e,i)\), and fixes \(\mathrm{III}\).

Any pure four-cycle avoids doubled \(a\). Its complementary triple contains \(a\), and cannot include an axis other than \(b,c\) besides \(a\), since every other \(a\)-end cell is a matching. Thus any pure cycle would use precisely the four axes \(i,k,d,e\).

In case II, the unused-pair cell of the \(ab\)-theta is \(C_{ce}\). It must be dirty by the crossed far condition. It lies in neither theta and cannot belong to a pure four-cycle on \(i,k,d,e\), so case II is impossible.

In cases I and III there is no pure cycle: already the peripheral pairs \(ik,kd,de\) belong to theta chains, so fewer than four unused pairs remain among \(i,k,d,e\). Use the two long fields \(p,q\) of the \(ab\)-theta in the displayed order.

* In case I, their far cells are \(kd,ke,de\) and \(cd,ce,de\), respectively. Their common cell \(F=de\) is the matching middle of \(a-e-d-c\). It is anticomplete to \(kd\) by the different split groups at \(d\) (the \(kd\) middle is on \(a-d-k-c\)), and to the clean \(ke\), which shares \(e\). Thus its \(p\)-far sum comes only from its own mate. However its \(q\)-far sum includes also exactly one contact to \(cd\) in its \(d\)-split group, because both consecutive cells are matchings and the cubic wing degree leaves one such contact after its parent and mate. The third \(q\)-far cell \(ce\) is clean and anticomplete to \(de\).
* In case III, the far triples are \(ck,kd,cd\) and \(ce,de,cd\). The common cell \(F=cd\) is the matching end of \(a-e-d-c\). It is anticomplete to \(ck\): those are the two long end cells of the crossed \(ac\)-theta at \(c\), whose fields are orthogonal. It is also anticomplete to \(kd\) by their different \(d\)-split groups. But it has exactly one contact to \(de\) in its own \(d\)-split group, and \(ce\) is clean and anticomplete to it.

In both cases the \(p\)-far sum forces the own mate of every \(x\in F\) to have value \(-p_x\). Since \(q=-p\) on \(F\), the mate already supplies the required \(-q_x\). The one extra neighbour in the indicated \(q\)-far cell has nonzero unit \(q\)-value, a contradiction. This excludes the two-odd case and the last four-cubic configuration on only three original axes.

At every root not lying in a triangle counted by \(b_{24}\) there are consequently at least four distinct incident triangles counted by \(b_{18}\). If \(R\) roots do lie in one of the \(b_{24}\) triangles, \(R\le3b_{24}\), so \(3b_{18}\ge4(99-R)\). The claimed inequality follows.
