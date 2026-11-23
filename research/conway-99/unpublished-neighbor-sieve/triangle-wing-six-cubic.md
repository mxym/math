# Six cubic groups cannot lie on just three original axes

Use the [triangle-wing split chart](big-triangle-wing.md) at a root. Assume all split degrees are at most three. Exactly three original axes cannot each have two cubic split groups (with no other cubic groups). This excludes a local split profile, not all roots with six cubic groups on more original axes.

When two cells share an original axis and are in different split groups at that axis, their defects are orthogonal by the [shared-axis Gram formula](triangle-wing-theta-paths.md#defects-and-short-chains). At any one cubic group the three columns sum to zero, each has norm in \(\{28,42,56\}\), and each pair has nonpositive pairing. Along a degree-two chain the end columns agree up to sign. These are literal graph-coordinate norms.

Write \(A,B,C\) for the three original axes and suppress the degree-two chains to obtain the cubic core on their six split groups. As in the [earlier analysis](triangle-wing-three-distinct.md#if-only-two-original-axes-had-cubic-groups), no path joins two distinct split groups of the same original axis (its equal or opposite end columns would be zero on an anticomplete own cell), and there are no loops (the two end columns would either pair positively or cancel, forcing the third zero). Since each original axis has six cubic path ends, there are exactly three paths between each of the original pairs \(AB,BC,CA\).

## Dealing with monochromatic groups and disconnected cores

Suppose some cubic group sends all three paths to groups of just one other original axis. Columns arriving at the two different split groups of that other axis are orthogonal. If both groups are used, the cubic zero sum has a singleton orthogonal to the other two, forcing it zero. Thus all three paths go to the same other cubic group, and together they form a separate theta component.

After removing a theta between, say, a group of \(A\) and one of \(B\), no \(AB\) paths remain: all three have been used. The remaining two groups of \(C\) receive all paths from the other groups of \(A,B\). Orthogonality between the two cubic groups of \(C\) again forces each of the remaining \(A,B\) groups to send all three to just one \(C\)-group, with different choices by degree. Thus a separate theta forces two others; there is no mixed theta-plus-connected-four-node case. Three separate thetas were [excluded by their actual peripheral cells](triangle-wing-three-theta.md).

We may now assume every cubic group sends two paths to one other original axis and one to the other. Name a group \(A_B\) if its two paths go to \(B\), and \(A_C\) for the other group of \(A\), and similarly throughout. For each original pair, there are three paths; between its two groups at either end the row and column sums are \(2,1\). With the heavy group first, the only possibilities are
\[
\begin{pmatrix}2&0\\0&1\end{pmatrix}
\quad\text{or}\quad
\begin{pmatrix}1&1\\1&0\end{pmatrix}.
\]
Call them parallel and split, respectively.

In a split layer, the heavy group at either end has its two layer paths going to different groups of the opposite axis. Their columns are therefore orthogonal even at the heavy end. The cubic zero sum makes the third column's squared norm the sum of their two squared norms, at least \(56\) and at most \(56\). Thus both layer paths have norm 28 and the one outside path at that heavy group has norm 56. Each of the three paths in the split layer is incident to at least one heavy group there, so every path in a split layer has norm 28. If \(AB\) is split, the outside norm-56 paths at \(A_B\) and \(B_A\) lie in \(AC\) and \(BC\), respectively; neither of these can be split. Hence at most one layer is split.

## A single split layer is impossible

Take the split layer \(AB\), the other two being parallel. Let \(x\) be its column at \(A_B\) for the heavy-to-heavy path \(A_BB_A\); let \(y\) be the one there for \(A_BB_C\); let \(z\) be the column at \(B_A\) for \(A_CB_A\). These directions are pairwise orthogonal: \(x,y\) reach different split groups of \(B\), \(x,z\) use different groups of \(A\), and \(y,z\) use different groups at both axes. The outside columns at \(A_B,B_A\) are therefore \(r=-x-y\), \(s=-\varepsilon x-z\), where \(\varepsilon=\pm1\) is the parity sign of the heavy-to-heavy path. But \(r,s\) are in the singleton paths of the parallel \(AC,BC\) layers: they reach \(C_B,C_A\), respectively, the two different light groups at \(C\) for those layers. Thus they must be orthogonal; the displayed expressions instead give \(r\cdot s=\varepsilon x^2\ne0\).

## Three parallel layers are impossible

Each parallel layer has a doubled link between two heavy groups and a singleton link between its two light groups. At the endpoints of a doubled \(AB\) link, call the two layer columns \(p,q\) at the \(A\)-end and \(\varepsilon p,\eta q\) at the \(B\)-end. The remaining columns \(r=-p-q\) and \(s=-\varepsilon p-\eta q\) at these two ends are the singleton columns of \(AC,BC\). As above, they reach different split groups at \(C\) and are orthogonal. This rules out equal parity \(\varepsilon=\eta\), since it would make \(s=\varepsilon r\). For opposite parity, the sign of the pairing of the doubled columns reverses between the two ends; each shared-axis pairing is nonpositive, so \(p\cdot q=0\). Also \(r^2=s^2=p^2+q^2\) forces both double columns to have norm 28 and both singleton columns norm 56. Solving the two zero-sum equations shows each double direction is a signed half-sum of its two incident singleton directions.

There are three singleton directions \(R_{AB},R_{BC},R_{CA}\), each of norm 56 and pairwise orthogonal because each pair shares an original axis in different split groups. A double direction in \(AB\) is a half-sum of \(R_{AC},R_{BC}\) with independent signs; one in \(AC\) is a half-sum of \(R_{AB},R_{BC}\) with signs. Consequently their pairing is \(\pm56/4=\pm14\). But their path ends are in the different split groups \(A_B,A_C\) at \(A\), so this pairing is zero. The contradiction proves the exclusion.
