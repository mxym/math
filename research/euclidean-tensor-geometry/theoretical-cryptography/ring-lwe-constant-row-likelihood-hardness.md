# Fixed dyadic likelihood hardness with only two convolution shapes

For a prescribed worst-case optimization problem, the number of public ring rows can be six, independent of the dimension. A related coefficient-Hamming decision problem needs twelve rows in the construction below. Both results use the same two sparse convolution shapes and observations of constant bit precision. They do not concern rows or observations drawn from an average-case distribution.

## 1. Results and precise models

Set \(R_d=\mathbb F_3[X]/(X^d+1)\) at dimensions \(d=W^2\), with \(W\) a power of two and \(W\ge8\). For \(h\in\{1,W\}\) and \(0\le j<k\), let the public rows be
\[
a_{h,j}=X^j(1-X^h),\qquad
 k=3 \text{ or } 6.
\tag{1}
\]
These rows are fixed by \(d\) and independent of the input observation; they are distinct, weight-two units, and linearly independent over \(\mathbb F_3\).

1. For \(k=3\), fix any \(0<b<1\), define
   \[
   f_b(x)=\sum_{\ell\in\mathbb Z} b^{\ell^2} e^{2\pi i\ell x},
   \qquad h_b=\log f_b,
   \qquad
   L_b(s;y)=\sum_{h,j,i} h_b\bigl(y_{h,j,i}-(a_{h,j}s)_i/3\bigr),
   \]
   and take explicit observations in \((\tfrac16\mathbb Z/\mathbb Z)^{6d}\). Returning an exact maximizer over \(s\in R_d\) is NP-hard. There is a constant \(c_b>0\) for which returning an \(s\) with \(L_b(s;y)\ge\max L_b-c_b\sqrt d\) is also NP-hard.
2. For \(k=6\), take \(y\in\mathbb F_3^{12d}\) and the total coefficient-Hamming distance \(D(s;y)\) between \(y\) and the stacked products \(a_{h,j}s\). Deciding whether \(\min_s D(s;y)\le B\) for an integer \(B\) is NP-complete. For an absolute \(c>0\) it is NP-hard to distinguish \(\min D\le B\) from \(\min D\ge B+c\sqrt d\). The same construction makes finding an additive-\(c'\sqrt d\) minimizer NP-hard for some \(c'>0\).
3. Under the deterministic Exponential Time Hypothesis, neither of the exact tasks admits worst-case deterministic time \(\exp(o(\sqrt d))\) on this fixed family. This assertion uses the ordinary sparse-3-SAT consequence of ETH; it does not require a gap version of ETH.

Here NP-hardness of a search task means that a deterministic polynomial-time algorithm for it, followed by an explicit finite check of its returned label, would decide an NP-hard language. In particular, we do not put a comparison of arbitrary real Gaussian likelihoods into NP, and we do not need to compute \(b\), the real-valued optimum, or a likelihood threshold for the reduction.

## 2. Combinatorial packing into two translated rows

View the \(d\) coefficients as the grid coordinates \(i=x+Wy\), \(0\le x,y<W\). On an interior horizontal or vertical bond oriented toward larger coefficient index, the coefficient at its destination of \((1-X^h)s\) is the difference \(z=s_i-s_{i-h}\), for \(h=1\) or \(W\) respectively. Assign each such bond a type: equality, inequality, or inactive. At every index not representing a specified active bond (including all negacyclic and grid-boundary crossings) use the inactive type. There is at most one bond for each available \((h,i)\).

For each such \((h,i)\), set the observations for the unshifted products \((1-X^h)s\), one phase for each repetition \(j\), by the following table:
\[
\begin{array}{c|c|c}
\text{type}&k=3,\ \text{torus observations}&k=6,\ \mathbb F_3\text{ observations}\\ \hline
\text{inactive}&(0,1/3,2/3)&(0,1,2,0,1,2)\\
z=0&(0,0,0)&(0,0,0,0,0,0)\\
z\ne0&(1/2,1/2,1/2)&(1,1,1,2,2,2)
\end{array}
\tag{2}
\]
For actual row \(a_{h,j}\) apply the signed coefficient shift \(X^j\) to the \(j\)-th observation vector. The phase embedding \(z\mapsto z/3\pmod1\) is an additive homomorphism, and the wrapped density is even. Both objectives are therefore unchanged when the observations and predictions are shifted together.

For the wrapped model, the [Jacobi triple product](https://dlmf.nist.gov/20.5.E9) makes \(f_b>0\) and strictly decreasing as the circular distance from 0 increases on \([0,1/2]\). Indeed its \(x\)-dependent factors are \(1+2b^{2n-1}\cos(2\pi x)+b^{4n-2}\), all positive and strictly ordered by that distance. Partial product ratios are bounded below by the ratio of the first factors, and the product converges positively at both points. The inactive tuple in (2) is a permutation of itself under every translation by \(z/3\). The equality penalty relative to its local optimum is \(g_E=3[h_b(0)-h_b(1/3)]>0\), and the inequality penalty is \(g_I=3[h_b(1/6)-h_b(1/2)]>0\). A satisfied bond pays zero penalty. In the Hamming model the local optimum distances are respectively \(4,0,3\); penalties on violated equalities and inequalities are respectively \(6,3\). Thus with \(v(s)\) the number of violated active bonds,
\[
L_{\rm loc}-L_b(s;y)\ge \min(g_E,g_I)v(s),\qquad
D(s;y)-B_{\rm loc}\ge 3v(s).
\tag{3}
\]
Here \(L_{\rm loc}\) is the sum of the individual local maxima, and \(B_{\rm loc}\) is the integer sum of local minimum distances. In both inequalities the deficit vanishes exactly when all active bonds are satisfied. We never assume the local bounds are jointly attainable.

The binomials \(1-X^h\) are units: for \(t=d/h\), \((1-X^h)\sum_{\ell=0}^{t-1}X^{h\ell}=1-X^d=2\), a unit in characteristic 3. Monomial shifts preserve this. For linear independence note that each vertical row has a unique support point \(W+j\) outside the entire horizontal support. After removing vertical terms by their coefficients, the horizontal rows \(X^j-X^{j+1}\) are independent by triangularity. This also proves the asserted distinctness.

## 3. A fixed crossed-square tile, then a full grid

We use a fixed 3-color crossover, a classical ingredient of Fischer's construction in [Garey, Johnson and Stockmeyer, Theorem 2.2 and Fig. 2](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/JohnsonDavid2.pdf). The following explicit realization, with a separately checked edge list, makes the occurrence and cost accounting here completely finite. Index its 13 abstract vertices by these unscaled positions:
\[
(4,0),(2,2),(4,2),(6,2),(0,4),(2,4),(4,4),(6,4),(8,4),
(2,6),(4,6),(6,6),(4,8).
\]
Use the 24 undirected edges
\[
\begin{split}
&01,02,03,12,14,25,26,27,37,38,45,49,56,59,5\,10,\\
&67,6\,10,78,7\,10,8\,11,9\,12,10\,11,10\,12,11\,12 .
\end{split}
\]
In the ordered north/east/south/west ports \((0,8,12,4)\), the color profile is exactly \((a,b,a,b)\) for \(a,b\in\{0,1,2\}\). The number of extensions is 2 when \(a=b\), 1 otherwise. This can also be verified directly by checking the \(3^{13}\) assignments against the 24 listed edges, as the companion script does.

To realize it in the square \([-8,72]^2\) with midpoint ports, multiply the displayed vertex coordinates by 8 and use the integer perimeter of the radius-3 \(\ell_\infty\) square at each vertex as an equality cycle. A segment path is formed as follows. Choose the larger displacement coordinate as primary (use horizontal on ties). Advance it by one unit, then advance the other coordinate to the nearest integer value on the original segment at that primary coordinate; round halves toward \(+\infty\). Crop a trace from its last visit to its initial square to its first visit to the destination square, including both endpoints. Join its first bond by inequality and all other path bonds by equality. Also add four analogous outward traces to \((32,-8),(72,32),(32,72),(-8,32)\), using equalities on the entire outward path. For the listed coordinates the 28 cropped paths are pairwise vertex-disjoint and meet the equality squares only at their designated endpoints, once per endpoint. The 13 cycles are disjoint, and the only tile vertices on the boundary are the four outer ports. These are exact checks on integer paths of the displayed constant-size layout; the companion script enumerates them and the 692 labeled bonds, including exactly 24 inequalities. Each equality cycle has a common color, the single inequality per inter-cycle path enforces precisely the corresponding graph edge, and no interior has any additional incidence. Hence this nearest-neighbor tile has exactly the stated port relation.

Now start with any finite loopless graph of typed equalities and inequalities over three colors, with at least one edge; trivial edge-free inputs can be dispatched separately. Allow parallel edges as separate constraints. Let \(n\) be the number of vertices and \(m\) the number of constraints. Use an \(n\times m\) rectangle of cells as follows:

* Each vertex has a horizontal bus, with its color measured at the west end of its leftmost cell.
* Each original edge has a distinct column. Orient the edge from its earlier row to its later row. A vertical wire only occupies this column and runs from the earlier row to the later one. At the earlier endpoint the column joins its horizontal bus using equality. At the later endpoint it joins the other bus using the original edge type. These joins use an ordinary horizontal line through the cell, a perpendicular stem to its north or south port, and one bond of the stem of the indicated type. Other stem bonds are equalities.
* At rows strictly between the two endpoints use the crossed-square tile, whose horizontal and vertical transmissions are independent. In cells past either endpoint there is only the horizontal bus (a straight equality line).
* Neighboring cells have disjoint square vertex sets: translate physical tiles by 81 units in each row/column step, and use one equality bond between adjacent used ports. Place the resulting rectangle inside the grid with a one-site exterior margin and with the remaining bonds inactive.

The construction uses a square of side \(W\) equal to the least power of two at least \(81\max(n,m)+2\). It follows that \(d=O((n+m)^2)\). If the original graph is satisfiable, its vertex colors propagate along the buses and its earlier endpoint colors propagate down the wires; the independent-crossing property fills every interior. Conversely a fully satisfying assignment induces one color per bus and every original constraint holds between the anchor colors. This is a deterministic polynomial-size reduction.

We also need robustness to violations. Mark each cell having some violated active bond. It contains at most one bus and at most one wire, so mark each of those logical objects present in it. A violated inter-cell equality marks only the bus or wire it joins. At most \(v\) buses and \(v\) wires are marked when \(v\) active grid bonds fail. A logical edge without a marked endpoint bus or marked wire remains satisfied by the anchor colors: every traversed tile and connector on each required path is good. Thus at most
\[
(\Delta+1)v
\tag{4}
\]
logical edges can be violated by the anchor assignment, for maximum input degree \(\Delta\) including constraint multiplicities. We only need this charging estimate, not that every defect can be fixed independently. In the construction and estimate, an equality loop is never needed; input reductions below yield no inequality loops.

## 4. Exact, ETH and gap consequences

For exact NP-hardness use unrestricted graph 3-colorability and take every input edge as an inequality. For the Hamming decision input choose \(B=B_{\rm loc}\). Membership in NP uses a coefficient label and direct finite arithmetic. For an exact maximizer in the six-row case, checking whether it satisfies all typed grid bonds separates the yes/no instances by (3); this is not a transcendental numerical comparison.

For ETH, [Impagliazzo, Paturi and Zane's sparsification theorem](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturiZane_2001_jcss.pdf) implies the corresponding sparse-3-SAT lower bound. The [linear-size 3-SAT to 3-colorability construction in the previous routing note, §4](https://github.com/mxym/math/blob/8210047381b1be707dfcee19858e784db7e3ac14/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-fixed-routing-eth.md#4-quasilinear-dimension-and-eth) yields a graph with \(O(N)\) edges and vertices from a sparse formula with \(N\) variables. It is linear in the number of literal occurrences; the grid construction allows unbounded degree for the exact part. Thus \(d=O(N^2)\). Time \(\exp(o(\sqrt d))\) plus polynomial construction and verification would imply \(\exp(o(N))\) on sparse formulas, contrary to ETH.

For the additive claims, [Guruswami and Sinop, Theorem 2.1, Remark 2.6 and the proof's final completeness/soundness calculation](https://theoryofcomputing.org/articles/v009a011/v009a011.pdf) give NP-hardness of distinguishing 3-colorable graphs from graphs on which every coloring violates at least \(\delta m_0\) of their \(m_0\) edges, for a fixed \(\delta>0\). Use the unweighted version, allowing repeated edges to encode integer weights, and drop isolated vertices. We first make an equivalent bounded-degree typed instance without sacrificing a constant fraction of this gap:

* For a vertex with \(r\ge1\) incidences, create one copy per incidence, padded to \(\lceil\sqrt r\rceil^2\le4r\) copies. Give each incidence a distinct copy as its new endpoint. Use the constant-degree expander on the square number of copies described in [Lee, On expanders from the action of GL(2,Z), Theorem 1.2](https://arxiv.org/abs/1301.6296): four explicit undirected generator edges per vertex before identifying duplicates, thus degree at most 8 (counting multiplicities), and uniform edge expansion \(\kappa>0\) for sets of at most half the copies. Impose equality on these edges. Loops can be dropped, the one-copy case requires no equality, and parallel edges cause no problem.
* If \(V_E\) equality edges of these expanders fail, recolor each cluster uniformly to a most frequent color. Every nonchosen color class has size at most half the cluster. Its edge boundary is at least \(\kappa\) times its size, and a failed edge can occur at most twice in the sum of these boundaries. Thus at most \(2V_E/\kappa\) vertices are recolored. Each recolored vertex can affect at most one original inequality, because it was assigned at most one incidence. If \(V_I\) input inequalities on the copies failed, the rounded original graph has at most \(V_I+2V_E/\kappa\) violations.
* Consequently a no instance has \(V_I+V_E\ge \delta m_0/\max(1,2/\kappa)\), while a yes instance is still perfectly satisfiable. The typed graph has \(O(m_0)\) vertices and edges and maximum degree at most 9. In particular the grid dimension still satisfies \(\sqrt d=O(m_0)\).

By (4) a no instance now has \(v(s)\ge c_0\sqrt d\) for every label, for some absolute \(c_0>0\); a yes instance has \(v=0\) attainably. In (3) this gives the Hamming promise gap with \(B=B_{\rm loc}\) and, in a yes instance, forces a sufficiently accurate additive approximation to return a label with \(v<c_0\sqrt d/2\). In the wrapped case take \(c_b<c_0\min(g_E,g_I)/2\) and use this same integer test on \(v\). It can be implemented with a smaller fixed rational bound than \(c_0/2\); the proof need not compute Gaussian values. This also proves the Hamming additive search claim. The additive deficit is measured in the raw \(O(d)\)-coordinate objective. We do not claim constant fractional approximation hardness.

## 5. Comparison and limits

The [sparse fixed-design theorem](https://github.com/mxym/math/blob/305aab03fea43ba9748ff4a62badc6e76c8f466f/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-fixed-sparse-likelihood-hardness.md) and its [quasilinear-dimension improvement](https://github.com/mxym/math/blob/8210047381b1be707dfcee19858e784db7e3ac14/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-fixed-routing-eth.md) spend a growing number of public rows on their constraint slots. The tradeoff here is a quadratic dimension budget in exchange for only two row shapes and a constant number of public rows, while retaining an explicit absolute gap. The methods and the ETH exponents are not interchangeable.

As a coding problem the Hamming statement fixes a rank-one negacyclic code by dimension, and varies only its target and threshold. [Dominguez Fiallo, Freyre Arrozarena and Piñeiro, ePrint 2023/1064](https://eprint.iacr.org/2023/1064) study cyclic-block syndrome decoding with a variable parity-check matrix; their general statement does not assert this fixed rank-one family result. The classical [Ring-LWE definition and worst-case-to-average-case reduction](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) involve uniform public ring coefficients and a random noise experiment. Neither those distributional assumptions, average-case search hardness, efficient recovery methods, nor any scheme or deployment are covered here. The checker certifies the finite tile, signs and local penalties, not any real-noise experiment or a reusable optimization algorithm.
