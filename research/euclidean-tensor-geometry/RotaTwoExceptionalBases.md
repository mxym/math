# Two exceptional bases in Rota's problem, and a sharp obstruction to freezing columns

**Yongxian Zhang.** AI-assisted development and internal verification.

The labeled version of Rota's basis problem asks for an \(n\times n\) array with given bases as its rows, after permuting each row, such that each column is also a basis. The following are independent statements about exact construction and its limits.

## Two arbitrary bases amid \(n-2\) parallel copies

**Theorem.** Over any field and for \(n\ge4\), the desired array exists when all but two of the input bases are parallel copies of one basis. Thus, after one invertible coordinate change and rescaling labeled vectors, \(n-2\) rows can be assumed to be standard coordinate bases. This does not restrict the two other bases \(B,C\).

We first prove a matrix observation. For any invertible \(n\times n\) matrix \(B\) over a field, \(n\ge4\), put \(w(\pi)=\prod_i B_{\pi(i),i}\) for a permutation \(\pi\). There are \(\pi\) and an \(n\)-cycle \(\tau\) such that \(w(\pi)\ne0\) and \(w(\tau\pi)\ne w(\pi)\). Indeed, if there were no such pair, \(w\) would be invariant under left multiplication by all \(n\)-cycles: given unequal products, at least one is nonzero and the inverse cycle reverses the comparison if needed. The \(n\)-cycles generate the alternating group for odd \(n\) and the full symmetric group for even \(n\). To see this, their generated subgroup is normal, and for \(c=(1\,2\,\cdots\,n)\) and \(s=(1\,2)\) the product \(c(s c^{-1}s)=(2\,3)(1\,2)\) is a three-cycle; its conjugates generate the alternating group. For even \(n\) there is also an odd \(n\)-cycle.

If \(n\) is even, constancy of \(w\) would give determinant zero, as even and odd permutations cancel. If \(n\) is odd, now \(n\ge5\), there would be two constants \(E,O\) on the two parities. At least one is nonzero. Each matrix entry belongs to a product of that parity, since we can choose the parity of a permutation on the remaining \(n-1\) indices. Thus every entry is nonzero and so are both constants. For any two distinct rows \(r,s\) and distinct columns \(u,v\), the ratio
\[
\frac{B_{r,u}B_{s,v}}{B_{s,u}B_{r,v}}
\]
equals both \(E/O\) and \(O/E\): complete the local pairing of the two rows and columns in either parity and compare with the permutation switching that pairing. So the ratio has the same value \(R\ne0\) for every ordered pair of columns of any fixed ordered pair of rows. With three columns \(u,v,z\), the ratios for \((u,v)\) and \((v,z)\) multiply to the ratio for \((u,z)\); hence \(R^2=R\), \(R=1\). This makes all two-by-two minors zero, a contradiction. The argument works also in characteristic two.

Reorder the columns of \(B\) so that the nonzero product is the diagonal and the unequal product now corresponds to a cycle \(\sigma\). Put
\[
\ell_i=B_{ii}e_{\sigma(i)}^*-B_{\sigma(i),i}e_i^* .
\]
The \(\ell_i\) form a dual basis: the sparse coefficient matrix has only the diagonal and the cyclic determinant products, with signs giving \(\pm(w(\mathrm{id})-w(\sigma))\). Its product with \(C\) is invertible. Thus the determinant expansion gives a permutation \(j(i)\) with \(\ell_i(c_{j(i)})\ne0\) for all \(i\). In output column \(i\), place \(b_i,c_{j(i)}\) and every coordinate vector except those indexed by \(i,\sigma(i)\). The two-by-two minor on these two missing indices is \(\ell_i(c_{j(i)})\), so all output columns are bases. Each coordinate axis is required in \(n-2\) columns, and each column requires \(n-2\) axes. The bipartite graph of these placements is regular, and splits into \(n-2\) perfect matchings by Hall's theorem applied repeatedly. Each matching accounts for one distinct labeled coordinate input row.

## Matroid version with a missing fundamental incidence

There is also an exact non-linear variant. Let \(A,B,C\) be bases of a rank-\(n\) matroid, and use \(n-2\) labeled parallel copies of \(A\) as the other rows. Assume that for some \(a\in A,b\in B\), replacing \(a\) by \(b\) does not give a basis (with labeled occurrences distinguished). Then a full array exists.

In the bipartite incidence graph of valid single replacements, Hall's theorem matches \(B\) perfectly to \(A\): a subset \(S\) of \(B\) lies in the closure of its neighboring elements in \(A\), by the fundamental circuit of each member with respect to \(A\). Since \(S\) is independent, the neighbor set has at least \(|S|\) elements. Label the matching so \(A-a_i+b_i\) is a basis. Choose \(i_0,r\) with \(b_{i_0}\in\operatorname{cl}(A-a_r)\) and choose an \(n\)-cycle \(\sigma\) with \(\sigma(i_0)=r\). The two indices are distinct by the matched basis property. Put
\[
H_i=\operatorname{cl}\big((A-\{a_i,a_{\sigma(i)}\})\cup\{b_i\}\big).
\]
Each \(H_i\) is a rank-\((n-1)\) flat missing \(a_{\sigma(i)}\) and containing all \(A\) except possibly \(a_i,a_{\sigma(i)}\). For \(i=i_0\), the missing incidence puts \(H_{i_0}\) inside \(\operatorname{cl}(A-a_{\sigma(i_0)})\); equal rank forces equality, so \(H_{i_0}\) also contains \(a_{i_0}\).

For a proper index subset \(I\), order the selected indices along each directed path of \(i\mapsto\sigma(i)\) on \(I\). When adding \(H_i\) to the intersection, \(a_{\sigma(i)}\) belonged to every earlier flat: the only other index whose flat may miss it is \(\sigma(i)\), which is later or absent. For the full index set start at \(i_0\), proceed around the cycle, and use \(a_{i_0}\in H_{i_0}\) for the last step. Thus the rank of \(\bigcap_{i\in I}H_i\) is at most \(n-|I|\) in all cases, including the full set. Since \(C\) is a basis, at least \(|I|\) members of \(C\) lie outside one or more of these flats. Hall's theorem matches \(C\) bijectively to the columns with its matched element outside \(H_i\). Use the same regular bipartite factorization for the \(A\)-slots. This proves the stated matroid subclass; the case where every fundamental incidence of both outlier bases is present is not addressed by this matroid argument.

## An orthonormal partial packing that cannot be frozen

**Proposition.** For \(n=3\) and every \(n\ge5\) there exist \(n\) real orthonormal input bases and \(n-2\) prescribed disjoint orthonormal transversal bases that cannot be completed by any two further transversal bases unless some of the prescribed choices change. The remaining vectors nevertheless partition into two bases when row labels are ignored.

Let \(H=\mathbf1^\perp\subset\mathbb R^4\). Use the normalized edge vectors \((e_i-e_j)/\sqrt2\) associated to the three opposite edge pairs of \(K_4\):
\[
(12,34),\qquad (13,24),\qquad (14,23).
\]
Each pair has an orthonormal completion \(h_1=(1,1,-1,-1)/2\), \(h_2=(1,-1,1,-1)/2\), \(h_3=(1,-1,-1,1)/2\), respectively. The \(h_i\) form an orthonormal basis of \(H\). At \(n=3\) put one pair and its \(h_i\) in input row \(i\), and freeze the transversal of all three \(h_i\). Among any complementary choices of one edge from each opposite pair, one triple is a triangle and the other a star: each triple consists of pairwise intersecting edges, and the two possibilities are complementary in \(K_4\). The triangle gives a column dependence, proving the obstruction. Without the row constraints the six vectors split into the paths with edges \(\{12,13,24\}\) and \(\{14,23,34\}\), which are bases.

For \(n=m+3\) work in \(H\oplus\mathbb R^m\). The first three rows use their same three \(H\)-vectors; the other \(m\) rows use \(h_1,h_2,h_3\); every row also has all \(m\) orthogonal coordinate vectors of \(\mathbb R^m\). Reserve the two edge-pair entries in each of the first three rows for last. For \(m\ge3\), use all three top \(h_i\) in one frozen column. In the other \(m\) frozen columns, put the lower rows' three \(H\)-axes in cyclic offsets \(0,1,2\) on the lower \(m\)-by-\(m\) block. This places each \(H\)-axis once per frozen column and once in each lower row. For \(m=2\), use three frozen columns and put a different top \(h_i\) in each; in the two lower rows place the other \(h\)-axes by the two cyclic shifts. In both constructions, three slots of every row and column (including the two reserved columns) are now assigned to \(H\). All other slots constitute an \(m\)-regular bipartite graph, which again factors into \(m\) perfect matchings for the orthogonal coordinate vectors. Freeze all but the reserved two columns. The top three residual vectors in one of those columns inevitably form a triangle. Ignoring labels once again splits the edges into two spanning paths and allocates one full \(\mathbb R^m\) coordinate basis to each.

A quantitative variant follows directly. If every labeled vector is perturbed by at most \(\eta\) in Euclidean norm and the same labels are frozen, every pair of proposed completions has one column matrix with smallest singular value at most \(\sqrt3\,\eta\). Use the unit coefficient vector supported on the three original triangle edges with cycle coefficients \(\pm1/\sqrt3\).

## Scope and provenance

The underlying \(K_4\) obstruction is already [Akrami–Liu–Raj–Végh, *Matroids are Equitable*, Example 4.3](https://doi.org/10.1007/s00493-026-00217-y): choosing one edge from each of their two opposite pairs forces choosing one from the third as well. The proposition places that known obstruction inside orthonormal original rows and \(n-2\) orthonormal frozen transversals; it does not refute Rota's conjecture. The positive statements are exact subclasses, not the full conjecture or an asymptotic packing improvement. Compare [Montgomery–Sauermann](https://arxiv.org/abs/2508.05601) for the full asymptotic packing and [Chow](https://timothychow.net/rotathree.pdf) for a different three-base formulation. No exhaustive priority claim is made.
