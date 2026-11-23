# Two cubic split vertices leave only two theta types

Use the [split-axis construction](big-triangle-wing.md) at an arbitrary graph vertex \(o\). The seven axes are its neighbour pairs; \(C_e\) is the four-point cell for an original axis pair \(e\). A split vertex corresponds to a connected component of a triangle wing and has degree equal to the component size divided by six. Delete the clean-cell edges from the split graph. Every retained cell is dirty.

**Theorem.** Suppose every wing component at \(o\) has at most 18 sites, and there are exactly two degree-three vertices in its dirty split graph. Their connected component is a theta with path-length multiset either \(\{2,2,2\}\) or \(\{1,3,3\}\). Any other component of the dirty split graph is a four-cycle of matching cells. This excludes a length-four path in this particular theta case only; it does not exclude length-four paths in other split configurations, establish a 24-site wing component, or assert realizability of either remaining theta.

## Defects and short chains

For \(e\) put \(S_e=\{o\}\) together with the four first-layer parents and the four sites of \(C_e\). Let \(v_e=(A-3I)1_{S_e}-1\). The linked construction gives \(v_e=0\) on the closed neighbourhood of \(o\), and on an exterior \(x\) the value is
\[
 v_e(x)=
 \begin{cases}
 d_e(x)-2 & x\in C_e,\\
 d_e(x) & x\notin C_e,\ \text{the axes of its cell meet }e,\\
 d_e(x)-1 & \text{the two axis pairs are disjoint},
 \end{cases}
\]
where \(d_e(x)=|N(x)\cap C_e|\). Each dirty cell has \(m_e\in\{0,1,2\}\) internal edges and \(v_e^2=14(4-m_e)\). Each internal cell degree is at most two; at degree two both neighbours are the sign flips. The defects at a split vertex sum to zero. Cells on a shared original axis but in different split groups there have no edges between them.

For distinct \(e,f\) sharing an original axis,
\[
 v_e\cdot v_f=-7E(C_e,C_f).
\]
Indeed \(v_e=-M1_{S_e}\) with \(M=3I-A+J/9\), \(M^2=7M\). The overlap of the two nine-sets is their common root triangle, giving \(3|S_e\cap S_f|+|S_e||S_f|/9=18\). Directed adjacency from \(S_e\) to \(S_f\) contributes six within that triangle, six each for the two sets of wings to and from it, and the \(E(C_e,C_f)\) cell edges. No first-layer site on either other axis meets the other cell.

Along any path with interior split vertices of degree two, its defects alternate \(p,-p\). Two distinct same-sign cells cannot share an original axis: on one of those cells its own defect is negative somewhere, while the other defect would be nonnegative there. If the path has at least three edges, comparing two same-sign cells shows that their own entries are at least \(-1\), so their internal degree is everywhere at least one. Dirtiness then makes both perfect matchings (\(m_e=2\)), and the entire path has norm 28. If the path has at least four edges, both signs occur at least twice. A coordinate where \(|p|>1\) would have to lie in the own cell of every defect column taking value \(\le-2\), which is impossible for two distinct cells. Hence \(p\) is unit and all its own cells are matchings, with the corresponding uniform sign on each. Five or more edges would place at least three matching cells on one side of a unit norm-28 field, giving at least six same-sign edges, contrary to the [published pair bound \(e\le5\)](big-triangle-wing.md#a-degree-contradiction-for-the-norm-28-cycle-field).

For any such path, its field is identically zero on a nonpath cell touching an internal path axis: the two adjacent chain cells comprise the degree-two split group there, and the nonpath cell has no contacts into either. Evaluate the column of an incident path edge on that nonpath cell. This zero rule also applies if an internal original axis occurs elsewhere in a different split group.

Every separate all-degree-two component is an even cycle (alternating defects are nonzero), of length at least four by simplicity of the split graph. Both signs repeat, giving norm 28 with matching cells; six or more edges again violate the same-sign edge bound. Thus every such component has length four.

## The component on the two cubic vertices

By the handshake identity the two degree-three vertices lie in one connected component. They have distinct original axes, say \(a,b\). For if not, the first and last defects on a simple path between them agree up to sign but belong to different split groups of that same axis. Evaluating on the last cell makes the first defect zero and the last nonzero, a contradiction.

Suppressing degree-two vertices leaves either a theta (three parallel paths) or a barbell (a path and one cycle at each end). At each barbell cycle the two columns incident at the degree-three end are either opposite, forcing the path column zero, or equal and nonzero. The latter is impossible because their inner product as two distinct cells on the same axis is nonpositive. Thus we have a theta. If \(p,q,r\) are the start defects at \(a\), then \(p+q+r=0\). The end defects at \(b\) give the same relation with the three signs \((-1)^{\ell-1}\), where \(\ell\) is the path length. Mixed parity would imply one defect is zero, so all paths have the same parity. Path length is at most four, and length one occurs at most once. For equal parity the signs at \(b\) are common, so pairwise inner products at the two ends agree.

A length-three path has two distinct internal axes, different also from \(a,b\) by the disjointness of its first and last same-sign edges. A length-four path has three distinct internal axes, all different from \(a,b\): same-sign disjointness of edges one and three and of edges two and four gives this using \(a\ne b\). If another path defect has negative pairing with the length-three or length-four defect, its two endpoint cells have nonzero cross contact with its path at the respective ends. By the zero rule, their non-\(a,b\) endpoint axes therefore avoid its internal axes.

This excludes \((3,3,3)\) and \((4,4,4)\): in either case all three norm-28 defects have pairwise inner product \(-14\), by their zero sum. Their two endpoint-neighbour axes per path would be six distinct axes outside \(a,b\), but only five are available.

## Two length-four paths and one short path

Consider \((4,4,2)\), with long defects \(p,q\) of norm 28 and short defect \(r\) through middle axis \(c\). The pairings \(p\cdot r,q\cdot r\) both equal \(-r^2/2<0\). Hence \(c\) is outside both long paths' internal axes. If \(p\cdot q<0\), the start and end internal axes of the second long path must both avoid the three internal axes of the first, and also \(c\); this leaves just one axis outside \(a,b\), impossible.

If \(p\cdot q=0\), then \(r^2=56\), so both its own cells are empty. Therefore \(r=-p-q\) gives eight equal, nonzero unit sign agreements of \(p,q\) on the two short cells, four at each end. The long paths' respective internal triples lie in the same four-axis set outside \(a,b,c\). They cannot be identical because the two length-two internal subpaths would then need four distinct edges on a triple. Their union is thus all four axes. The long fields vanish on each other's path cells: at endpoints use zero cross contact (their pairing is zero), and each of the other path's internal edges meets one of their own three internal axes since its only available other internal axis is the fourth one. The zero rule now confines any common support to the three cells on \(\{a,b,c\}\). There are the eight agreements on the short cells and at most four opposite positions in \(C_{ab}\), contradicting \(p\cdot q=0\).

## A single length-four path and two short paths

Consider \((4,2,2)\) and call the long path \(a-i-j-k-b\), its start defect \(p\), and the two axes *outside* its five axes \(c,d\). These \(c,d\) need not both be the middle axes of the short paths. The long chain's four cells use eight positive and eight negative units. At \(a\), each of its four first-cell sites has one first-layer parent inside the wing of \(T_a\) and one own-cell matching mate, leaving one of its three wing neighbours in the other two cells of that split group. Thus the other two cells receive four contacts in total from the long first cell. Their \(p\)-values are precisely these contacts and \(p\) is unit, so these are four positive sites. The other end supplies four negative sites by the same argument, using the reversed sign. These two sets of short endpoint cells are distinct: no path is the direct edge \(ab\) in this even theta.

All other cells meeting either \(a\) or \(b\) are either chain cells or have zero \(p\)-value by belonging to another split group at that endpoint. The zero rule excludes all other cells touching \(i,j,k\). Since the short endpoint cells and the chain together give twelve positive and twelve negative units, the remaining two of each sign must fill \(C_{cd}\).

For a site of \(C_{cd}\), there is no contact into any short endpoint cell of nonzero \(p\): such a short path must have its middle axis in \(\{c,d\}\) by the zero rule, and its two cells are the entire degree-two split group at that axis, different from the \(cd\) group. All four long chain cells have disjoint axes from \(cd\); their defect formulas give exactly two contacts in each opposite-sign chain cell and zero in each same-sign chain cell. These four neighbours already supply the entire \(-4p\) requirement at the site. Therefore any internal \(C_{cd}\) contacts contribute signed sum zero, and since its four sites all have unit signs and its internal degree is at most two, the internal degrees are zero or two. The degree-two sign-flip rule then makes \(C_{cd}\) either empty or a clean square. It cannot be empty: a dirty \(cd\) edge is outside the theta, hence on a separate four-cycle of matching cells by the earlier argument. So \(C_{cd}\) is clean, and \(S_{cd}\) is an actual nine-site rook grid.

Finally choose any \(x\in C_{ab}\). Its \(p\)-value is zero. Its cell is in different split groups at \(a\) and \(b\) from all the theta endpoint cells, so it has no contacts into their supports. The two interior long cells \(C_{ij},C_{jk}\) have axes disjoint from \(ab\), hence each provides exactly one contact by the zero-value defect formula. A rook grid saturates all pair common-neighbour quotas internally: adjacent grid sites share one and nonadjacent ones share two. Thus any outsider meets at most one grid site, and there are exactly \(9(14-4)=90\) grid-to-outside edges over the 90 outsiders, so each has exactly one. The site \(x\) is exterior to the root and its two first-layer parents lie on \(a,b\), not \(c,d\); its unique grid neighbour must lie in \(C_{cd}\), which is all signed. Hence \(x\) has exactly three signed neighbours in total, impossible at a zero entry of an integral \(-4\) field with unit signed entries.

This rules out all length-four paths in the stated theta case. Together with the odd triple exclusion, the only remaining multisets are \((2,2,2)\) and \((1,3,3)\).
