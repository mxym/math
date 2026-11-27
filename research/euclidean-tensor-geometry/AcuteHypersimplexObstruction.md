# Hypersimplex vertices cannot be perturbed into an acute set

## Statement and status

Let \(n\ge5\) and \(2\le k\le n-2\). Label \(N=\binom nk\) points by the \(k\)-subsets \(S\subseteq[n]\), and let
\[
x_S=\mathbf 1_S\in \mathbb R^n,\qquad H_k=\{x:\mathbf 1^\top x=k\}.
\]
The hyperplane \(H_k\) is a Euclidean \((n-1)\)-space. There is **no acute configuration** of labelled points \(p_S\in H_k\) for which \(\max_S\|p_S-x_S\|_2\le5/(288\sqrt n)\). In the same neighborhoods, nonobtuse configurations are exactly Euclidean isometric images of the original 0/1 vertices with positive diagonal coordinate weights, as made precise below. For \((n,k)=(5,2)\) the stronger radius \(1/23\) holds in this normalization, where each base edge has length \(\sqrt2\). Thus the ten edge-midpoints of a regular 4-simplex (after rescaling) cannot be acutely perturbed even by arbitrary, not necessarily analytic or symmetric, perturbations.

This does not bound the size of an acute set in \(\mathbb R^4\): it excludes a local region only. Gerencsér–Harangi's [construction](https://arxiv.org/abs/1709.03411) gives nine points there, and Danzer–Grünbaum's nonobtuse theorem with its equality classification gives \(f(4)\le15\); see [the original paper](https://doi.org/10.1007/BF01193107) and [Harangi's account](https://doi.org/10.1137/100808095). Gerencsér–Harangi perturb a lower-dimensional hypercube by using an extra dimension; the theorem here concerns perturbations in the intrinsic affine dimension of the hypersimplex. A targeted search of primary literature and the public OpenAI mathematics overview did not locate this exact local obstruction; no priority claim is made.

## Four-point angle inequality

Suppose four distinct points \(a\pm u,b\pm v\) are part of an acute set, and \(h=a-b\). At the two points of the first pair, the endpoints of the second pair subtend two acute angles, hence
\[
\|h\|^2+\|u\|^2-\|v\|^2>2|h\cdot u|.
\]
Exchanging the pairs gives \(\|h\|^2+\|v\|^2-\|u\|^2>2|h\cdot v|\). Adding yields
\[
|h\cdot u|+|h\cdot v|<\|h\|^2.             \tag{1}
\]
In particular different pairs cannot have identical midpoints. If instead we use the pair *sums* and full diagonals, the same inequality holds, since both sides scale by four.

This also gives a separate local obstruction around a centrally symmetric template. For \(r\ge2\) disjoint pairs \(m_i\pm v_i\) in an acute set, put \(D_m=\max_{i,j}\|m_i-m_j\|\) and \(\alpha=\min_{\|w\|=1}\max_i|w\cdot v_i|\). For a diameter-realizing difference \(m_j-m_\ell\), apply (1) to comparisons with pair \(i\), then the triangle inequality, to obtain \(|(m_j-m_\ell)\cdot v_i|<2D_m^2\) for every \(i\), including \(i=j,\ell\) by (1) alone. Hence \(D_m>\alpha/2\). Whenever the original half-diagonals span the ambient space, \(\alpha>0\) and depends continuously on them; the original midpoint spread is zero, so no acute configurations converge to that template. For instance the eight vertices \((\pm1,\pm1,\pm1,0)\) and two opposite apices \((0,0,0,\pm\sqrt3)\) are nonobtuse, but cannot be acutely perturbed in \(\mathbb R^4\). In this example \(\alpha\) at the base equals \(\sqrt3/2\): for \(w=(w',w_4)\), the maximum equals \(\max(\|w'\|_1,\sqrt3\,|w_4|)\), minimized with \(w'\) on a coordinate axis.

## Hypersimplex comparisons

For any fixed label set \(R\) of size \(k-2\) and disjoint four-element set \(Q=\{a,b,c,d\}\), take the three pairings of \(Q\) into two edges. Pairing \(ab|cd\) uses the disjoint sites \(p_{R\cup\{a,b\}}\) and \(p_{R\cup\{c,d\}}\); define its diagonal \(W=p_{R\cup\{a,b\}}-p_{R\cup\{c,d\}}\) and pair sum \(U=p_{R\cup\{a,b\}}+p_{R\cup\{c,d\}}\). For every comparison between distinct pairings in this same octahedron, record \(\Delta=U-U'\) and the two scalar projections \(\Delta\cdot W_0,\Delta\cdot W'_0\), where the subscript zero means the original, unperturbed diagonal. Original pair-sum differences vanish. Let \(D=\max\|\Delta\|_2\), and \(B_*= \max \{|\Delta\cdot W_0|,|\Delta\cdot W'_0|\}\), maximizing over all such comparisons. At \(n=5,k=2\) there are five such octahedra, with three comparisons per octahedron: **15 vector differences and 30 scalar projections**.

For an acute configuration \(D>0\) by (1). If the maximal displacement is \(\varepsilon\), then \(D\le4\varepsilon\) and every diagonal changes in norm by at most \(2\varepsilon\). By (1) and Cauchy–Schwarz,
\[
 B_*\le D^2+2\varepsilon D\le6\varepsilon D.                 \tag{2}
\]

## Exact five-label linear identities

Use labels \(0,\ldots,4\) in this paragraph. The displacements \(X_{ij}:=p_{\{i,j\}}-x_{\{i,j\}}\) have zero coordinate sum in each row, so their first four coordinates are an independent parametrization. Let \(b_0,\ldots,b_{29}\) be the 30 signed scalar projections from the norm \(B_*\), ordered as follows: missing label \(0,\ldots,4\); for each missing label put the other four in increasing order \(a,b,c,d\), use pairings \(ab|cd,ac|bd,ad|bc\) in that order; take the three increasing pairing-index combinations lexicographically and for each use the first and then second pairing's diagonals, each oriented from the earlier listed edge to the later. Define \(\delta=X_{01}+X_{23}-X_{02}-X_{13}\), the first comparison on \(\{0,1,2,3\}\). Then the following integer identities hold:
\[
\begin{split}
10\delta_0={}&-b_7-b_8-b_{10}+b_{13}+b_{14}+b_{16}
        +2b_{24}+2b_{25}+2b_{27}-2b_{29},\\
10\delta_4={}&-2b_0+2b_2+b_4-b_5+2b_7+b_8-b_9+2b_{10}
      -2b_{13}-b_{14}+b_{15}-2b_{16}-b_{18}-b_{19}+2b_{21}-2b_{23}.
\end{split}
\]
The companion standard-library checker [verify-acute-hypersimplex-obstruction.py](verify-acute-hypersimplex-obstruction.py) generates the 30 projection rows in the 40 free variables, expands both identities, and compares every coefficient over the integers. It also verifies that the ten base sites themselves are nonobtuse, with 60 right angles among the 360 unordered endpoint choices at ten centers. These identities can alternatively be found by exact row elimination. By permutation of labels, the first identity controls any coordinate on the four labels of any comparison, and the second controls the missing coordinate. Signs of rows may change; the norm does not. The stabilizer of the two ordered pairings acts transitively on their four labels (the Klein four group). Thus every comparison obeys
\[
|\Delta_i|\le(7/5)B_* \quad (i\in Q),\qquad
|\Delta_i|\le(12/5)B_* \quad (i\notin Q).
\]
For five labels this implies \(D\le(\sqrt{340}/5)B_*\). Combined with (2) and \(D>0\), this is impossible as soon as \(\varepsilon\le 1/23\), since \(6\sqrt{340}/5<23\).

## Extension to all hypersimplices

First suppose \(k=2\) and \(n\ge5\). Fix a comparison with four labels \(Q\), and restrict all named points to any five labels \(T\supset Q\). Orthogonally project their displacements to the sum-zero subspace supported on \(T\), i.e. keep the five coordinates and subtract their mean. Every projected five-label scalar test is unchanged, because its unperturbed diagonal is supported on \(T\) and has coordinate sum zero. Hence the five-label identities control coordinates of the projected \(\Delta\) by \((7/5)B_*\) on \(Q\) and \((12/5)B_*\) elsewhere. For fixed \(a\in Q\) and any \(j\in[n]\), take \(T\) containing \(Q\cup\{j\}\) (and any fifth label when \(j\in Q\)). It follows that \(|\Delta_a-\Delta_j|\le (19/5)B_*\).

For \(3\le k\le n-3\), hold \(R\) fixed and repeat the argument on five labels among the free set \([n]\setminus R\): this handles \(j\notin R\). To cover \(j\in R\), take complements. The transformation \(p_S\mapsto \mathbf 1-p_S\) with reindexing by \(S^c\) preserves distances and all projection magnitudes and maps this octahedron to one whose fixed set is \(R'=[n]\setminus (R\cup Q)\) and whose free set contains \(Q\cup R\). Therefore the same bound holds for every \(j\). The case \(k=n-2\) is the complement of \(k=2\).

Since \(\sum_j\Delta_j=0\) in the original hyperplane, the coordinate-difference estimate gives \(|\Delta_a|\le(19/5)B_*\) for \(a\in Q\), then \(|\Delta_j|\le(38/5)B_*\) for every \(j\). Thus \(D\le(38\sqrt n/5)B_*\). With (2) this contradicts \(D>0\) for the claimed radius \(5/(288\sqrt n)\), since \(6\cdot38<288\). No smoothness of the perturbation, or restriction to points on a sphere, was used.


## Local classification of the nonobtuse configurations

For a merely nonobtuse configuration, the four-point inequalities and (2) hold without strictness. The radius just used still makes \(6\varepsilon\) times the applicable linear norm bound strictly less than 1, forcing \(D=0\) in the same neighborhood. Consequently every octahedron has all three pair sums equal.

Set \(d_{ij}(T)=p_{T\cup\{i\}}-p_{T\cup\{j\}}\) for each \((k-1)\)-subset \(T\) avoiding \(i,j\). If \(T\) changes by exchanging a single label \(l\) for \(m\), an octahedron on free labels \(i,j,l,m\) equates the two values. Since the Johnson graph of all such \(T\) is connected, the value \(d_{ij}\) is independent of \(T\). Choosing \(T\) also to avoid any third label \(\ell\) shows \(d_{ij}+d_{j\ell}=d_{i\ell}\), hence \(d_{ij}=a_i-a_j\) for suitable vectors \(a_i\). The vector \(p_S-\sum_{i\in S}a_i\) is therefore constant along each exchange, hence equals one common translation on the whole vertex set.

For four distinct labels \(i,j,l,m\), fix \(k-2\) other labels \(R\). The four sites indexed by \(R\cup\{i,l\}, R\cup\{j,l\}, R\cup\{i,m\}, R\cup\{j,m\}\) form a parallelogram, by the additive formula. Nonobtuseness at adjacent sites gives both signs of the same inner product, hence \((a_i-a_j)\cdot(a_l-a_m)=0\). Write \(q_{ij}=\|a_i-a_j\|^2\). Polarization shows that the three sums of opposite \(q_{ij}\) on every four labels are equal. Thus \(h_i=(q_{ij}+q_{i\ell}-q_{j\ell})/2\) is independent of the two other distinct labels \(j,\ell\): for pairs sharing an index this follows by the four-label equality, and the graph of pairs linked by a shared index is connected. Then \(q_{ij}=h_i+h_j\) by using a third label in both expressions. The original small perturbation yields
\[
|q_{ij}-2|\le 4\sqrt2\,\varepsilon+4\varepsilon^2
\]
by taking a common \(T\) and comparing \(d_{ij}\) with \(e_i-e_j\). Each \(h_i\) is positive, as the displayed bound is less than \(2/3\) for \(\varepsilon\le1/23\).

It follows that the induced metric on the sum-zero displacement space is the restriction of the diagonal positive quadratic form \(\sum_i h_i x_i^2\): both forms agree on the basis differences \(e_i-e_n\) and on all of their pairwise differences, so they agree everywhere by polarization. Equivalently there is a Euclidean isometry from the affine span of \((\sqrt{h_i}\,\mathbf 1_S(i))_{i=1}^n\) sending these weighted \(0/1\) sites to \(p_S\). Conversely each positive diagonal weighting gives a nonobtuse set: the coordinatewise products of the two emanating \(0/1\) differences at any site are nonnegative. This proves the local classification independently of any sphere hypothesis.
