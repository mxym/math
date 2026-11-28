# A matroid separator obstruction for the first potential linear \(C_7\) improvement

Let \(H\) be a matrix over \(\mathbb F_7\) with check rank \(r\) and \(n\) columns, giving the linear code \(\ker H\) in \(C_7^{\boxtimes n}\), where one-coordinate confusability differences are \(D=\{0,1,-1\}\). Call the columns dissociated if no nonzero \(D\)-combination of them sums to zero, equivalently their binary subset sums are all distinct. This is exactly the condition that the code is zero-error. The rate here is \((n-r)/n\), before taking the base-seven exponential.

**Theorem.** The first check rank at which a rate greater than \(3/5\) is not already ruled out by Lovász theta is five, with exactly thirteen columns. If a zero-error rank-five thirteen-column check system exists, then:

1. Its represented column matroid is simple and internally 4-connected, in the explicit sense that it has no 1- or 2-separation, and every 3-separation has a side of size three.
2. Its proper rank-\(1,2,3,4\) flats contain at most \(1,4,6,9\) columns, respectively. Every 3-separation has a three-column circuit as its small side; that circuit's relation is not proportional, after sign changes and permutation, to \((1,1,3)\).
3. Its column-matroid branchwidth is at least four, with edge width \(\lambda+1\), where \(\lambda(A)=\operatorname{rank}(A)+\operatorname{rank}(A^\complement)-5\).

The new spectral tests concern subspace intersections of column spans and are invariant under arbitrary changes of the parity-check basis. They differ from [forest-supported parity checks](../C7ForestParityCapacity.md) and the existing [row-support treewidth hierarchy](../BoundedWidthParityCapacity.md). This does not decide whether any rank-five thirteen-column system exists, nor determine unrestricted linear or nonlinear Shannon capacity. For the linear capacity setting see [Guruswami–Riazanov](https://arxiv.org/abs/2009.05685). The separator terminology follows the rank convention of [Oxley–Semple–Whittle](https://www.sciencedirect.com/science/article/pii/S0095895604000334).

## 1. Exact low ranks and contraction of saturated subspaces

Write
\[
 t=\vartheta(C_7)=\frac{7\cos(\pi/7)}{1+\cos(\pi/7)}<\frac{1659}{500},
\]
using [Lovász's cycle formula](https://doi.org/10.1109/TIT.1979.1055985). Multiplicativity gives \(7^{n-r}\le t^n\). At check ranks \(1,2,3,4,5\), the maximum lengths allowed by this inequality are \(2,5,7,10,13\). The checker verifies the first excluded values using the displayed rational bound. At ranks \(1,2,3,4\), the allowed maximum is attained: use \([1\ \ 2]\) and the two-row matrix with columns \((1,0),(0,1),(2,1),(4,1),(1,3)\), and take sums of the respective blocks. Thus the length-\(13\), rank-\(5\) case is the first possible improvement by check rank.

A dissociated set of maximum **cardinality** in any given finite vector space has full signed sumset in that space. Otherwise a vector outside its signed sumset could be appended without creating a nonzero \(D\)-relation. If a subset of columns in a proper subspace \(U\) has this property (whether or not maximum), the remaining columns after projection modulo \(U\) are again dissociated: a nonzero signed combination landing in \(U\) could be canceled by the subset. At rank five, thirteen columns, for any \(1\le j\le4\) the sum of the known rank-\(j\) and rank-\((5-j)\) maxima equals 12. No \(j\)-dimensional subspace can therefore contain a rank-\(j\) maximum. This gives the bounds \(1,4,6,9\); there are no zero columns, and no two columns lie on the same line.

## 2. Separator transfer for theta

For a column partition \(A,B\), let \(U,V\) be the spans, \(W=U\cap V\), and \(\delta=\dim W\). Let \(S_A\subseteq W\) be the attainable signed sums of columns in \(A\) that lie in \(W\). Let \(G_A\) be the simple Cayley graph on the additive group \(W\) with nonzero differences in \(S_A\). Then every dissociated check system obeys
\[
             7^{|B|-\operatorname{rank}(B)+\delta}
                 \ \le\ t^{|B|}\,\vartheta(G_A).              \tag{1}
\]
Indeed \(H_B:\mathbb F_7^B\to V\) is onto, so its inverse image of \(W\) has dimension \(|B|-\operatorname{rank}(B)+\delta\). Map its words \(x\) to \((x,H_B x)\) in \(C_7^{\boxtimes |B|}\boxtimes G_A\). If two different images are confusable, their word difference is a nonzero element of \(D^B\) and its syndrome belongs to \(S_A\), including the possibility of zero. It can be canceled by a signed combination in \(A\), contrary to global dissociation. Thus the images form an independent set and (1) follows. This transfer holds for any separator dimension; the present proof only needs one and two.

## 3. Exact small-side bounds

The [verifier](verify_c7_rank_five_separator.js) and [rational Fourier witness table](c7_rank_five_separator_certificate.json) give these uniform bounds:
 
| \(\operatorname{rank}(A)\) | \(|A|\) | \(\dim W\) | Bound for \(\vartheta(G_A)\) |
|:--|:--|:--|:--|
| 2 | 4 | 1 | \(7/t\) |
| 2 | 4 | 2 | \(9/4\) |
| 3 | 4 | 2 | \(16\) |
| 3 | 5 | 2 | \(8\) |
| 3 | 6 | 2 | \(15/4\) |
| 2 | 3 | 2 | \(5\), only for coefficient pattern \((1,1,3)\) up to scalar, signs and permutation |

All checks use only dissociation and the absence of parallel columns in \(A\). For rank two a basis can be chosen from the actual columns and sent to the two standard basis vectors. For rank three and two-dimensional \(W\), choose a basis column outside \(W\) and scale the quotient coordinate to send it to \(e_3\). Complete to a basis with two other columns. By sign changes and interchanging them their quotient coordinates can be taken \(0\le a\le b\le3\). Subtracting their quotient multiples of \(e_3\) gives a basis of \(W\), so the normalized initial columns are \(e_1+a e_3,e_2+b e_3,e_3\). The remaining columns are independently taken up to sign and unordered. A column is accepted at each insertion precisely when it is not in the current signed sumset; its own parallel-ray exclusions are checked separately. This exactly enumerates the required cases without searching over the rest of the thirteen-column matrix.

The rank-two four-column enumeration sees 61 normalized systems. For a boundary line every signed residual has at least five points in that line. A symmetric zero-containing set on a line with five points gives a graph isomorphic to the complement of \(C_7\); with seven points it gives a complete graph. Both have theta at most \(7/t\). The rank-three enumeration checks 1,520, 95,610 and 2,199,000 normalized systems at lengths \(4,5,6\), with respectively 831, 50,360 and 14,737 distinct residual masks before linear equivalences. The last row of the table normalizes the indicated circuit to \(e_1,e_2,e_1+3e_2\). If a plane mask contains a full line, covering by its seven cosets gives \(\vartheta(G_A)\le7\), used when the target bound allows it.

For the remaining plane masks we use the standard Fourier LP for the theta function of a finite abelian Cayley graph, as in [DeCorte–de Laat–Vallentin](https://arxiv.org/abs/1307.5703). To make the finite checks explicit, averaging the theta SDP over translations gives a real even function \(f\) on \(W\simeq\mathbb F_7^2\), with \(f(0)=1\), \(f=0\) on nonzero edges and nonnegative Fourier transform. The objective is \(1+2\sum_x f(x)\), where \(x\) ranges over missing edge sign-pairs. For each character sign-pair (and for the trivial character) the Fourier inequality is \(1+\sum_x K_{ux}f(x)\ge0\), with \(K_{ux}=2\cos(2\pi u\cdot x/7)\). Positive semidefiniteness gives \(|f(x)|\le1\). Thus for any nonnegative weights \(y_u\) the objective is at most
\[
              1+\sum_u y_u+\sum_x\left|2+\sum_u y_u K_{ux}\right|.
\]
This permits rational rounding instead of requiring exactly representable dual equalities. The checker uses nonnegative rational \(y_u\), isolates the three possible nontrivial cosine values by disjoint rational brackets in \(x^3+x^2-2x-1\), and bounds the displayed expression from above with integer interval arithmetic. The same cubic gives the rational bound on \(t\). The 330 checked witnesses cover all residual masks used for the numerical caps under \(GL(2,\mathbb F_7)\) and the full-line shortcut. No optimizer, numerical tolerance, or external software is needed to reproduce the certificate in Node.js.

## 4. Connectivity and branchwidth

There is no split with \(\delta=0\) and both sides nonempty, since sums of the maximum lengths in ranks adding to five are at most 12. For a split with \(\delta=1\) and both sides of size at least two, the possible ranks are \((2,4)\) or \((3,3)\). The latter has at most \(6+6\) columns; the former forces lengths \((4,9)\) by the flat caps. Equation (1) with the line bound requires \(7^6\le7t^8\), contrary to \(t^8<7^5\). This proves 3-connectivity.

Next let \(\delta=2\), with \(4\le|A|\le|B|\). The flat caps leave only the following possibilities, and all violate (1) by exact rational comparison:
\[
\begin{array}{c|c|c|c}
 (|A|,|B|)&(\operatorname{rank}A,\operatorname{rank}B)&\text{required by (1)}&\text{strict upper}\\ \hline
 (4,9)&(2,5)&7^6\le t^9\vartheta(G_A)&(9/4)t^9<7^6\\
 (4,9)&(3,4)&7^7\le t^9\vartheta(G_A)&16t^9<7^7\\
 (5,8)&(3,4)&7^6\le t^8\vartheta(G_A)&8t^8<7^6\\
 (6,7)&(3,4)&7^5\le t^7\vartheta(G_A)&(15/4)t^7<7^5 .
\end{array}
\]
A \(3+10\) split with \(\delta=2\) has ranks \((2,5)\), because ten columns have full rank five by the flat caps. Its small side is a circuit and the \((1,1,3)\) pattern would require \(7^7\le 5t^{10}\), also impossible. This proves internal 4-connectivity with the additional coefficient restriction.

Finally, any branch decomposition on thirteen columns has a cut with both sides at least five. In its ternary tree, take a vertex whose deleted components each contain at most six labeled leaves (a centroid for leaf counts). At least one component has at least five leaves, since their total is thirteen. The corresponding cut has sizes \(5+8\) or \(6+7\). Internal 4-connectivity makes its \(\delta\ge3\), so its edge width is at least four.
