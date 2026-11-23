# Odd theta components cannot pair on four distinct cubic axes

Assume all dirty split degrees at a root are two or three, there are exactly four cubic split groups on four different original axes, and their cubic components are two separate thetas. Then neither theta can be odd. Both cannot have path lengths \(422\) either. The remaining even pairs \(222+222\) and \(222+422\) are not excluded. This says nothing about connected four-cubic cores, or about roots with more cubic groups.

Use the [theta-path facts](triangle-wing-theta-paths.md) and the [universal three-edge matching lemma](triangle-wing-three-distinct.md). The only available theta length patterns are \(222,133,422\): parity is constant in a component, lengths are at most four, at most one direct path occurs, and \(333,444,442\) were excluded by arguments internal to the component. The \(422\) possibility was previously excluded for *exactly two* cubic split groups, but is retained here until a separate test. An odd \(133\) must be crossed even if other components are present: with six distinct long-path axes, its two fields have no common support outside their theta cells, so the [disjoint-overlap identity](triangle-wing-theta-disjoint.md#the-exact-overlap-identity-when-the-internal-axes-are-disjoint) contradicts the universal matching on both middle cells.

The complement of any separate pure four-cycle on four axes has the [twelve-site budget](triangle-wing-theta-no-cycles.md#the-outer-cell-budget-of-any-separate-four-cycle). Accordingly among its three complementary cells there cannot be a known matching cell, and there can be at most one clean cell. All pure cycles are length four with matching own cells. For a \(422\) theta, the two axes unused by its long path give an empty cell. To see this with other components present, use the [length-four support calculation](triangle-wing-theta-paths.md#a-single-length-four-path-and-two-short-paths): its own four long cells and the signed short end sites leave two signed units of each sign in the unused-pair cell, which must be empty or clean by its eigen-equation. If clean, the end-axis pair \(ab\) gives the odd signed-contact contradiction exactly as before. Here \(C_{ab}\) may itself be clean or dirty in another component; it is in other split groups at both endpoints, is zero, and anticontacts the signed endpoint cells, so its own cleanliness is irrelevant. Thus the unused pair is empty, must be in one of the two thetas rather than a matching pure cycle, and fixes its path squared norm to 56.

If two paths of one theta share an original internal axis, they are in different degree-two split groups there, hence their fields are orthogonal. More than one such orthogonal pair among three nonzero fields with sum zero is impossible. In the case of one pair the three norms must be \(28,28,56\), with 56 on the remaining path, since all norms are in \(\{28,42,56\}\). These checks explain the only norm filters in the checker.

## Far-degree parity for a crossed odd theta

Write the long paths \(a-i-j-b,\ a-k-i-b\) and their start fields \(p,q\). Their common internal axis forces \(p\cdot q=0\) (the field of one is zero on the endpoint cell of the other meeting its internal axis). Their direct column is \(-p-q\) of norm 56, hence empty, and both fields are \(+1\) on all four sites of that direct cell. The long chains are wholly matching and their fields are unit. Each field vanishes on the other long chain's end cells by orthogonality and on its middle by the degree-two zero rule. The field \(p\) is supported on its own two negative end cells, its own positive middle cell, the positive direct cell, and the three other far cells on the axes off its four path axes; all twelve sites of those far cells are nonzero units by the norm and support count. The same holds for \(q\). Of their respective far triples, the shared cell \(F\) is the pair of axes unused by the two paths jointly. Orthogonality and the four agreements at the direct cell force \(q=-p\) at every site of \(F\).

At \(x\) in the \(p\)-far cells the two end columns give \(1+p_x\) contacts each of value \(-1\); the reversed middle column gives \(1-p_x\) contacts of value \(+1\). If \(x\notin F\), its cell uses the exclusive internal axis \(k\) of the other path so \(q_x=0\), and the direct column supplies \(1-p_x\) further contacts of value \(+1\). The own-chain and direct contributions exactly exhaust \(-4p_x\), so its remaining signed sum within its far twelve sites is zero. If \(x\in F\), the direct column vanishes there and supplies one contact of value \(+1\); the total before far contacts is then \(-3p_x\) and the remaining signed sum must be \(-p_x\). Modulo two, since every far site is signed, the required degree in the far triple is **odd on \(F\) and even on either other far cell**. Do the same for the \(q\)-far triple.

For the finite test only axis labels and split groups are used. Given a site of one far cell with own-cell degree \(d\), its possible contact count to each other far cell is precisely bounded as follows. If their shared axis uses different split groups (including when either cell is clean), there are no contacts. If the shared group has degree two, the contact count is exactly \(2-d\): the site's cubic wing degree includes its first-layer parent and \(d\) own-cell neighbours. If there is one other cell in the shared group, the contact count is in \(0,\ldots,2-d\); it need not satisfy any further condition in the checker. For each far cell this tests the required parity for at least one local degree \(d\), taken as 2 for a clean cell, 1 for a known matching cell, 0 for a known empty cell, or any of 0,1,2 otherwise. A genuine field must pass this deliberately generous test at each site; rejecting the entire degree range is sufficient to exclude the chart.

## Exact finite coverage

Relabel the seven original axes so the two theta endpoint pairs are \(01\) and \(23\). This is possible because the four endpoints are distinct; it does not assume an automorphism of a graph, or place any restriction on its signed-parent labels. All remaining original axis choices are enumerated as follows.

* For \(222\), choose three of the five nonendpoint axes as its three short middles (10 choices).
* For crossed \(133\), choose the shared internal axis and the two other internal axes in order, writing the paths \(a-i-j-b,a-k-i-b\) plus the direct edge (60 choices).
* For \(422\), choose the three long internal axes in order, and choose the two short middle axes from the remaining three options that avoid the first and last long internal axes (180 choices). The long central internal axis is permitted as a short middle in a different split group.
* Reject a repeated original edge. All separate cycles use four distinct original axes and are enumerated as edge-disjoint cycles on the leftover original pairs. The fixed root has at most 21 pairs, and the two thetas already use at least 12, so at most two such cycles are possible. Every subset of the 105 unlabeled four-cycles (with labeled original axes) of size at most two is included when its edges are disjoint from each other and the two thetas.

The [standard-library checker](triangle_wing_two_theta_odd.py) applies the norm and outer-budget checks first, then the far-degree parity. Ordered symmetric theta types are shown separately. Its counts are:

| Theta lengths | Separate cycles | Before parity | After parity |
|---|---:|---:|---:|
| 133 + 133 | 0 | 228 | 0 |
| 133 + 222 | 0 | 84 | 0 |
| 222 + 133 | 0 | 84 | 0 |
| 133 + 422 | 0 | 24 | 0 |
| 422 + 133 | 0 | 24 | 0 |
| 222 + 222 | 0 | 19 | 19 |
| 222 + 222 | 1 | 42 | 42 |
| 222 + 422 | 0 | 24 | 24 |
| 422 + 222 | 0 | 24 | 24 |

Unlisted rows have zero initial charts from the previous necessary checks, including double \(422\). No vertex adjacencies or graph realizations are enumerated, no floating computation or search budget is used, and the even controls are only axis charts passing these restrictions.
