# Two cubic wing groups force fourteen grids at the root

Continue the split-axis and defect notation of [the theta-path theorem](triangle-wing-theta-paths.md). At a root \(o\) suppose there are exactly two cubic vertices in the dirty split graph and no split vertex of degree at least four. The theta-path theorem gives a single component with path lengths \(222\) or \(133\), and every other dirty component would be a degree-two four-cycle.

**Theorem.** No separate degree-two cycle can coexist with either theta type. Thus type \(222\) would have fifteen clean cells and is excluded by the [published fourteen-grid bound](five-grids/fifteen-grid-exclusion.md), whose original proof independently checks the missing-\(K_{2,3}\) chart. The remaining possibility \(133\) has exactly fourteen actual grids through \(o\). No existence of this root type, or exclusion of roots with more cubic vertices, is asserted.

## The outer-cell budget of any separate four-cycle

Let \(W\) be the original axis set of a separate dirty four-cycle. Its four original axes are distinct: opposite edges have the same defect sign and therefore disjoint original axes. Choose one of its alternating defect columns \(p\). It is unit of norm 28 and its four own cells are matching cells with uniform signs, giving eight sites of each sign. On a noncycle cell meeting an axis of \(W\), \(p=0\): this cell is in a different split group at the shared axis. Thus the remaining twelve nonzero sites of \(p\) are precisely the three cells on the complementary triple of axes. They give six of each sign.

Let \(Y\) be those twelve sites. Every \(x\in Y\) sees exactly two sites of each of the two opposite-sign cycle cells and none in the same-sign cycle cells, because all four pairs of axes are disjoint and the defect value there is contact count minus one, up to sign. Hence its neighbours within \(Y\) have signed sum zero. The [unit norm-28 edge bound](big-triangle-wing.md#a-degree-contradiction-for-the-norm-28-cycle-field) permits at most five same-sign edges on either shore. Four matching edges on each shore are already used by the cycle cells, so the graph on \(Y\) has at most one same-sign edge of either sign.

A nonisolated site of \(Y\) must have at least one same-sign and at least one opposite-sign neighbour there. It follows that either all of \(Y\) is isolated in its own induced graph, or there are exactly two nonisolated sites of each sign, each with one neighbour of either sign. In the latter case the only nonisolated component is a four-cycle. In particular an outer non-theta dirty cell is impossible: it would itself be a matching cell from a separate degree-two component, using all four nonisolated sites of \(Y\), which would force its own internal graph to be the four-cycle rather than the matching. An outer non-theta clean cell, if present, consumes all four nonisolated sites, leaving the other two cells empty and anticomplete to each other.

## Applying the budget to the two theta types

For \(222\), the six theta cells have original axis labels forming \(K_{2,3}\), with endpoints \(a,b\) and distinct middle axes \(c_1,c_2,c_3\). Any triple of axes has at most two theta cells. Thus the complementary triple of a separate four-cycle would have exactly two theta cells and a clean third: if it had two non-theta cells they would both be clean, exceeding the four-site budget. The two theta cells must be empty and anticomplete to each other. If they share a middle axis \(c_i\), they comprise the degree-two split group there. Its wing degree supplies two neighbours inside the cell union to every cell site, once its first-layer parent is counted. With both cells empty all these contacts must cross, a contradiction. If instead the two cells share an endpoint axis, write \(v_i,v_j\) for their columns and \(v_k\) for the third column of that cubic group, with \(m_k\) its own edge count. Their zero sum and the empty cell norms give
\[
E(C_i,C_j)=-\frac{v_i\cdot v_j}{7}
=\frac{56+56-14(4-m_k)}{14}=4+m_k>0.
\]
Here the first equality is the shared-axis Gram identity already proved in the theta-path theorem. This again contradicts anticompleteness.

For \(133\), each of the six cells on the two length-three paths has exactly two internal edges (their common norm is 28), and the direct edge is the only possible empty theta cell. The complementary triple of a separate cycle cannot have a non-theta cell: it would be clean and both remaining cells would have to be empty. Nor can it have three theta cells, because at least two of these would be two-edge cells, each using at least three nonisolated sites. That exceeds the four-site budget. This excludes every separate cycle for \(133\) as well.

The entire dirty graph is therefore the theta: six or seven dirty cells. Since the remaining axis pairs are precisely the clean grids through \(o\), this gives fifteen and fourteen grids respectively, with the first forbidden by the earlier independently checkable theorem.

## The exact \(222\) 24-site count before the grid obstruction

For completeness, the conditional local structure of the excluded \(222\) branch can be checked without any grid theorem. Write \(A_i=C_{a c_i}\), \(B_i=C_{b c_i}\), \(X_i=A_i\cup B_i\), \(X=X_1\cup X_2\cup X_3\). The degree-two group at \(c_i\) makes \(X_i\) internally 2-regular, because every cell site has exactly its one first-layer parent elsewhere in that wing component and three wing neighbours in total. Write \(p_i=v_{a c_i}=-v_{b c_i}\), so \(\sum_i p_i=0\). At \(x\in A_i\) and \(j\ne i\), the columns of \(A_j,B_j\) give \(p_j(x)=d_{A_j}(x)=1-d_{B_j}(x)\), since \(A_j\) shares \(a\) with \(x\) and \(B_j\) has disjoint axes. The corresponding formula interchanges the ends for \(x\in B_i\). Thus each pair of \(X_i\)'s is joined by a perfect matching, and \(X\) induces degree four.

There are two unused axes \(d,e\). Here are all outside sites and their numbers of neighbours into \(X\):

| Sites | Sites in row | Neighbours into \(X\) |
|---|---:|---:|
| Root | 1 | 0 |
| First-layer parents on \(a,b\) | 4 | 6 |
| First-layer parents on the three \(c_i\) | 6 | 4 |
| First-layer parents on \(d,e\) | 4 | 0 |
| Cell \(C_{ab}\) | 4 | 0 |
| Four cells on one endpoint \(a,b\) and one unused axis | 16 | 3 |
| Three cells on two different middle axes | 12 | 2 |
| Six cells on a middle axis and an unused axis | 24 | 4 |
| Cell \(C_{de}\) | 4 | 6 |

The first-layer rows are immediate from the number of incident theta cells and the two sites per parent in each cell. The \(ab\)-cell is in other split groups at both endpoints. For a cell on \(a\) and an unused axis (and symmetrically for \(b\)), its \(A_j\)-contacts vanish by the different group at \(a\); its \(B_j\)-axes are disjoint, so \(p_j=0\) gives exactly one \(B_j\)-contact per \(j\). A cell on two middle axes has no contact to either corresponding \(X_i\), and their columns vanish there; the third column vanishes by their sum, giving one contact into each of its disjoint half cells. For a cell on one middle axis and one unused axis, there is no contact to its own \(X_i\); on either other \(X_j\) the two disjoint-axis formulas give a contact sum of two. Lastly for the unused pair they give a sum of two on every \(X_i\). Thus the outside populations are exactly \(n_0=9,n_2=12,n_3=16,n_4=30,n_6=8\), with no other heights. The weighted sum is \(240=24(14-4)\), consistent with the degree-four core.
