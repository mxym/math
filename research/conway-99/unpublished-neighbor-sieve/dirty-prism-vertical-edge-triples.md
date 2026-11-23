# Vertical-edge restrictions in the dirty triangular-prism root

Suppose a hypothetical Conway graph has a root whose dirty-axis graph is a triangular prism on six axes, with one saturated axis \(e\). This is the residual twelve-grid root with all wing sizes at most 18 after the [disjoint clean \(K_4,K_3\) theorem](clean-k4-k3-cross-edge.md). Name the prism's triples \(a_1,a_2,a_3\) and \(b_1,b_2,b_3\), and its vertical cells \(V_i=C_{a_i b_i}\). If \(m_i\) is the number of own edges in \(V_i\), then, **up to order**,
\[
(m_1,m_2,m_3)\in\{(1,1,1),(0,2,2),(1,1,2)\}.
\]
This restriction is rank-free, uses no short-field assumptions, and does not by itself rule out the whole prism profile; the [subsequent star-cap test](dirty-prism-star-cap.md) does.

Use the [established defect convention](triangle-wing-theta-paths.md#defects-and-short-chains): on an own cell a defect is the degree minus two, on a different cell sharing an axis it is the contact count, and on a disjoint cell it is the contact count minus one. In particular any off-cell value is at least minus one. For any centered \(-4\) field \(f\) vanishing on the first layer, \(\sum_{x\in C} f_x=-f\cdot v_C/7\) by pairing with the nine-site defect.

Let the top and bottom horizontal fields on the two pairs opposite index \(i\) be \(F_i,G_i\), and let the vertical field be \(h_i\). Their two degree-three sums are \(h_i+F_j+F_k=h_i+G_j+G_k=0\) for \(\{i,j,k\}=\{1,2,3\}\). Subtracting the three equations gives \(F_i=G_i\) for all \(i\). Each \(F_i\) repeats on two different own cells, so its own values are at least \(-1\) and those two dirty cells are matchings. Consequently
\[
 F_i^2=28,\qquad h_i=-F_j-F_k,\qquad F_j\cdot F_k=-7m_i .
\]
The last relation follows from \(h_i^2=14(4-m_i)\).

Every off-\(e\) clean cell is \(C_{a_i b_j}\) with \(i\ne j\). For each \(F_k\) it shares an axis with at least one of its two equal horizontal columns, so it has zero \(F_k\). In the six \(e\)-star clean cells, only \(F_i\) can be nonzero at \(C_{e a_i},C_{e b_i}\); these supports are pairwise disjoint between fields. On an \(F_i\)-horizontal cell the other values \(F_j,F_k\) are nonnegative by their shared axes and have sum at most one, since the disjoint field \(h_i=-F_j-F_k\) there is at least \(-1\). On \(V_i\), the other two values are nonnegative, have sum \(2-d_{V_i}\), and \(F_i\) lies in \(\{-1,0,1\}\): the lower bound is from its own horizontal columns, and the upper bound follows from \(h_j,h_k\ge-1\) (the vertical pairs are disjoint) and \(F_j,F_k\ge0\). In fact \(F_i=1\) forces \(F_j=F_k=0\) and thus own degree two. The sums on \(V_i\) are
\[
\sum_{V_i}F_i=m_i-M,\qquad
\sum_{V_i}F_j=\sum_{V_i}F_k=4-m_i,\qquad M=m_1+m_2+m_3,
\]
by the pairing formula and \(h_i=-F_j-F_k\).

For distinct indices define
\[
A_{ij}=\sum_{\substack{x\in V_i\\F_i(x)=-1}}F_j(x),\qquad
B_k=\sum_{x\in V_k}F_i(x)F_j(x)\quad(\{i,j,k\}=\{1,2,3\}).
\]
Here \(B_k\) counts isolates whose two non-own values are both \(1\): the two values are nonnegative and sum at most two. The horizontal contribution to \(F_i\cdot F_j\) is \(-4m_k\): on the two \(F_i\) cells, each contributes \(-\sum F_j=-m_k\), and similarly on the two \(F_j\) cells; on the two \(F_k\) cells the product of the other values is zero. There is no common clean support. The vertical contributions are \(-A_{ij},-A_{ji},B_k\); a row \(F_i=+1\) has both other fields zero. Thus
\[
 A_{ij}+A_{ji}=3m_k+B_k,\qquad
 M+2m_k+B_k\le8,
\]
using \(A_{ij}\le4-m_i\) and \(A_{ji}\le4-m_j\). In particular \(M\le4\), since \(M>4\) needs some \(m_k=2\).

## The small low-edge cases

When \(m_i=0\), the \(4-M\) rows of \(V_i\) with \(F_i=0\) have both remaining values 1: an isolated own vertex needs their sum to be 2, while each is at most 1 when \(F_i=0\) by the disjoint vertical fields. The other \(M\) rows have \(F_i=-1\). Thus \(A_{ij}=M\) for either \(j\ne i\), and \(B_i\ge4-M\). When \(m_i=1\), \(F_i\) is never positive (its own degree is at most 1), so exactly \(M-1\) rows have \(F_i=-1\).

* For \((0,0,0)\), all \(A\)'s vanish but all \(B\)'s are at least four. For \((0,0,1)\) or \((0,0,2)\), the pair of empty vertical cells has \(A_{ij}+A_{ji}=2M\) while the required value is at least \(3M\).
* For \((0,1,1)\) use \(i\) for the empty vertical cell and \(j,k\) for the others. Each of \(V_j,V_k\) has a single own negative row and at least one isolate with own field zero. Thus \(B_j,B_k\ge1\), while \(A_{ij}=A_{ik}=2\) and \(A_{ji},A_{ki}\le2\). The equations for the two pairs involving \(i\) force \(A_{ji}=A_{ki}=2\). In the sole own negative row of each of \(V_j,V_k\) the other non-\(i\) field must then be zero (the two non-own values sum at most two). Hence \(A_{jk}=A_{kj}=0\) even though \(B_i\ge2\), impossible.
* For \((0,1,2)\) set \(m_i=0,m_j=1,m_k=2\). The pair \(i,j\) has \(A_{ij}=3\), \(A_{ji}\le3\), so \(A_{ji}=3,\ B_k=0\). All \(F_i\)-mass in \(V_j\) is on the two own negative rows, so those rows must be the two isolates (an isolate with own zero would require \(F_i=1\)). On both remaining endpoints, \(F_j=F_i=0,\ F_k=1\). At the isolates their two \(F_i\) values total three and lie in \(\{0,1,2\}\), so they are \(1,2\). Thus \(A_{jk}=1\) and \(B_j=1\). The pair \(i,k\) now gives \(A_{ki}=1\), since \(A_{ik}=3\). On \(V_i\), the zero own row contributes one to \(B_i\), and the three negative rows have both other sums three, so the number of \(1+1\) rows there is either one or three; \(B_i\) is 2 or 4. From \(A_{jk}=1\) and \(A_{kj}\le2\) it follows that \(B_i=2,\ A_{kj}=1\). Thus both other fields contribute exactly one unit to the own negative rows in \(V_k\). If \(V_k\) is a matching, it has no center and only one own negative row, with non-own sum one, impossible. Otherwise it is a two-edge path and isolate. Since \(B_k=0\), the isolate puts both units into just one of the two other fields and has \(F_k=-1\), contradicting the separate totals one and one.

These exclusions leave exactly the three displayed triples.

## A literal twelve-site consequence

The cross-edge count between any two vertical cells \(V_i,V_j\) is \(M\): their axes are disjoint, and
\[
\sum_{x\in V_i}(1+h_j(x))
 =4-\sum_{x\in V_i}(F_i(x)+F_k(x))=M .
\]
Writing \(W=F_1+F_2+F_3\), a point \(x\in V_i\) has total degree \(4-2W(x)\) in \(V_1\cup V_2\cup V_3\), by summing the internal degree and its two disjoint-axis contact counts. Thus this twelve-set induces an even graph with exactly \(4M\) edges. The global field \(W\) has squared norm \(84-14M\), namely 42 or 28. None of these facts alone asserts realizability of any of the remaining triples.
