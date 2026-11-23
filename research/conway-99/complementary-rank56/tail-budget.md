# Cross-eigenspace bounds from complementary norm-20 fields

Suppose \(A\) is an SRG\((99,14,1,2)\) adjacency matrix. Write \(F^+(a,t)\) for the number of integer labels \(p\) with
\[
Ap=3p+a\mathbf1,\qquad \sum_i p_i=9a,\qquad \sum_i p_i^2=t.
\]
Let \(x_j^+\) count vectors of squared norm \(2j\) in the scaled dual of the complementary rank-56 marked lattice. Let \(C_-(a,t)\) count old-sector labels \(b\) with \(Ab=-4b-2a\mathbf1\), \(b^2=t\), and zero seven-primary lattice class. The two lattices and the complementary binary-factor lifts are as in the [complementary rank-56 construction](README.md). The three grid-pair counts \(n_0,n_1,n_3\) count unordered distinct literal \(3\times3\) rook grids with the indicated intersection sizes. Put
\[
 M=F^+(2,20),\qquad E=C_-(1,51)-105336.
\]
Then
\[
\begin{aligned}
 n_1&\le M\le 3E,\\
 x_8^+&\ge2(n_0+n_1)+\max(0,\,2M-2E,\,4M-6E),\\
 x_9^+&\ge2n_0+4M .
\end{aligned}
\]
In particular \(x_8^+=2(n_0+n_1)\) implies \(C_-(1,51)\ge105336+M\). No automorphism or rank restriction is used. These inequalities do not settle the existence question.

## The forced cubic tail

For a label in \(F^+(2,20)\), the excess \(\sum_i p_i(p_i-1)=2\) leaves exactly one coefficient \(+2\) or exactly one coefficient \(-1\), with all other entries in \(\{0,1\}\). The lone negative would require neighbor sum \(-1\), impossible. Write
\[
p=2e_i+1_U+1_F,\qquad |U|=|F|=8,
\]
where \(U\) consists of the positive neighbors of \(i\), and \(F\) of the other positives. The equation at \(i\) gives precisely eight neighbors in \(U\). Each vertex of \(Z=N(i)\setminus U\) already sees weight two at \(i\) and cannot see another positive vertex. The seven matched pairs in \(N(i)\) therefore split into four pairs in \(U\) and three in \(Z\). Each \(u\in U\) has two neighbors in \(F\), since it sees weight two at \(i\), one at its mate, and needs total five. Each \(f\in F\) has exactly two neighbors in \(U\) (its two common neighbors with \(i\)) and exactly three in \(F\). Thus \(F\) is cubic.

Every vertex outside \(\{i\}\cup N(i)\) corresponds to its two neighbors in \(N(i)\), which belong to distinct mate pairs. Every such pair has precisely one exterior common neighbor. The exterior splits into \(24\) vertices of type \(UU\), \(48\) of type \(UZ\), and \(12\) of type \(ZZ\); \(F\subseteq UU\).

Put \(h=(A-3I)1_F\). Subtracting the contribution of \(2e_i+1_U\) from the affine equation gives
\[
h=0\text{ on }\{i\}\cup Z\cup UU,\quad
h=1\text{ on }UZ,\quad
h=2\text{ on }U\cup ZZ.
\]
In the subgraph induced by \(h=2\), \(U\) is a matching and there are no \(U\)--\(ZZ\) edges. Any alternative center for the same \(h\) must be in \(h^{-1}(0)\), with eight \(h=2\) neighbors inducing four mate edges. A vertex of \(Z\) has only four such neighbors, its four \(ZZ\) pair labels. A vertex of \(UU\) has two nonmated \(U\) anchors; neither can meet any of its other \(h=2\) neighbors, which lie in \(ZZ\). Hence only \(i\) is possible and \(U=N(i)\cap h^{-1}(2)\) is also determined.

For fixed \(h\), any \(UU\) vertex outside a tail \(F\) already has its full required positive mass two from \(U\), so it misses \(F\). Thus \(F\) is a union of components of the graph on \(UU\). It is genuinely a single component: a cubic component has at least four vertices, and the four-vertex case \(K_4\) is forbidden, so an eight-set cannot contain two cubic components. There are at most three tails for one \(h\), and different tails in that class are disjoint. Every ordered pair of distinct tails with the same \(h\) gives a distinct neutral \(+3\) eigenvector \(1_F-1_{F'}\) of squared norm sixteen.

## The common budget in the old sector

Let \(w(c)=\sum_i c_i u_i\), with \((u_i,u_j)\) given by \(3I-A+J/9\). The old affine evaluation of \(w(-1_F)\) is \(h-1\), with squared sum \(31+20=51\) and charge one. Its seven-class is zero: the raw \(u_i\) pair integrally with the old difference lattice, and \(9u_i\) belongs to that lattice, since both \(18u_i=\sum_{j\sim i}(u_i-u_j)\) and \(99u_i=\sum_j(u_i-u_j)\) do. Thus this is an actual mark counted by \(C_-(1,51)\).

These marks do not overlap the \(105336\) mandatory marks \(w(1_P-1_Q)\) coming from anticomplete signs: \(49896\) with \(P\) an edge and \(Q\) a singleton (72 choices per edge), and \(55440\) with \(P\) a triangle and \(Q\) an edge (240 choices per triangle). The latter count follows because the 60 sites anticomplete to a triangle are 8-regular there: every such site sees two neighbors in each of its three mutually disjoint 12-site wings by the two-walk counts. These mandatory marks are distinct: an equal-image balanced nonzero difference would have positive mass at most five and be a \(+3\) integral eigenvector. Such a vector requires mass at least six: a double entry would demand neighbor mass at least six on its own sign side, and a unit sign side must have minimum internal degree three. On at most five vertices this is impossible: a degree-four site has a matched four-vertex link with no remaining vertex to reach degree three; otherwise a nonempty cubic graph would have even order and at most four vertices, hence be a forbidden (K_4).

If a mandatory mark equaled a new one, \(k=1_P-1_Q+1_F\) would satisfy \(Ak=3k+\mathbf1\) and \(\sum k=9\). Any negative site needs at least two *other* negatives, impossible because \(|Q|\le2\). Any double site would be forbidden from having a zero neighbor, since a zero must see total one, impossible with nonnegative total nine. Thus \(k\) is the indicator of a rook grid: it is 4-regular internally and every outside site has one neighbor there, so all common-neighbor quotas for pairs of its sites are internal; the resulting SRG\((9,4,1,2)\) is the rook grid. Consequently \(Q\subset F\) is outside the grid, \(P\) is inside and disjoint from \(F\), and \(F=(\mathrm{grid}\setminus P)\cup Q\). Each \(q\in Q\) sees at most one vertex in the grid and at most one other in \(Q\), contradicting cubicity of \(F\). Equal new marks correspond exactly to equal \(h\). At most \(E\) classes are therefore available.

## Grid injections and shell arithmetic

Distinct grids meet in zero sites, one site, or a common line (triangle). Indeed two common nonadjacent sites would force both of their common neighbors to be in the intersection, since anything outside either grid has only one contact there. In a rook grid the resulting square closes to the whole grid by adjoining the caps of its edges, then adjoining the last site. Thus a proper intersection is a clique; a common edge forces the third point of its line.

Two grids meeting once give the label \(1_Q+1_R\in F^+(2,20)\). This identifies their doubled site and union. A third grid in the union would meet each original grid in at most three sites, impossible; hence \(n_1\le M\). The same pairs give \(2n_1\) distinct signed differences of neutral norm sixteen, each sign inducing fourteen edges and identifying its parent grid. These do not overlap the equal-\(h\) tail differences, which have twelve edges per sign. Disjoint grid pairs give \(n_0\) distinct charge-two unit 18-sets by taking unions, and \(2n_0\) distinct unit neutral norm-eighteen differences.

The complementary binary-factor lifts give
\[
x_8^+=N_{16}^++2F^+(2,18),\qquad
x_9^+=N_{18}^++4F^+(1,15)+2F^+(2,20).
\]
The possible extra charge-one term \((1,13)\) at the first shell is absent: its excess is four, so there are at most two negatives, and any negative would require at least two *other* negative neighbors. Two doubles would then remain, but a double cannot neighbor any zero by the charge-one equation, and the total positive support is smaller than the degree. The shell table follows by testing the two binary-factor integral evaluations \(p,q\) in
\[
 2j=t+\frac{7(6p^2-2pq+2q^2)-9a^2}{11},\qquad
 a\equiv-p+2q\pmod{11},\qquad t\ge9|a|,\quad |a|\le5.
\]
Neutral norms below twelve vanish. Every nonunit neutral eigenvector of norm eighteen has a unique exceptional entry after choosing its orientation: if \(b_i\ge2\), subtract \(d_i=(4I+A)e_i\), which has charge two and squared norm 30. Then \(b-d_i\) has charge \(-2\), norm \(48-14b_i\); the absolute-sum bound forces \(b_i=2\), and the result is the negative of an \(F^+(2,20)\) label. Conversely the \(p-d_i\) at the doubled site of such a label has its unique exceptional entry \(-2\), and taking both signs recovers exactly the nonunit part. Hence \(N_{18}^+\ge2n_0+2M\), giving the claimed bound on \(x_9^+\). If \(m\) is the number of tails for each old mark, then \(0\le m\le3\), the \(m\) sum to \(M\), and the old classes give at most \(E\) buckets. The equal-tail budget is \(\sum m(m-1)\); using \(m(m-1)\ge0,\,2m-2,\,4m-6\) proves the claimed \(x_8^+\) bound.

## Two further restrictions on the grid overlap geometry

For each grid \(Q\), write \(d_Q\) for its number of disjoint partners and \(\ell_Q\) for its number of line-intersecting partners. Then
\[
 \sum_Q d_Q\ell_Q\le F^+(1,21)+F^+(1,19)+12F^+(1,15).
\]
For each of the counted triples \((Q,R,T)\) let \(R\) be disjoint from \(Q\) and \(T\) meet \(Q\) in a line. The charge-one label \(1_{Q\cup R}-1_T\) has norm \(27-2k\), where \(k=|T\cap(Q\cup R)|\in\{3,4,6\}\). At \(k=3,4\) the negative sites identify \(T\) uniquely, since there are at least five; the label then determines the union and its unordered disjoint component grids. Precisely one meets \(T\) in a line, so the counted triple is unique. At \(k=6\) the three negative sites form a triangle: each needs neighbor sum \(-2\), and there are only two other negatives. At most six grids contain that triangle (a second root axis at a fixed vertex of the triangle, one of six, determines the grid). Once \(T\) is specified the union and pair are determined, with at most two orders. This gives the factor twelve.

Let \(D\) and \(L\) be the \(0\)-\(1\) adjacency matrices for disjointness and line intersection of any actual grid family. Then
\[
 \operatorname{rank}_{\mathbf F_2} D\le54,\qquad
 \operatorname{rank}_{\mathbf F_7}(I+4J-D+2L)\le54-r,
\]
where \(r=\operatorname{rank}_{\mathbf F_7}(2A-J+I)\). For the first, \(A\) is symmetric idempotent modulo two, with rank 54 by its characteristic polynomial. Each grid indicator \(q\) satisfies \((A+I)q=\mathbf1\) modulo two, so \(q+\mathbf1\) lies in the image. Their Gram is exactly \(D\), because all nondisjoint intersections and all diagonals are odd. For the second, lift each charge-one grid field using the same auxiliary binary evaluation \((p,q)=(-1,0)\). The lifted pairings \(7(v_Q,v_R)\) equal \(|Q\cap R|+3\), since the centered graph contribution is \(|Q\cap R|-9/11\) and the binary contribution is \(42/11\). Reduced modulo seven these are pairings in the actual \(54-r\) dimensional seven-discriminant module, giving the bound. Their classes are all distinct because a difference has scaled squared norm \(18,16,\) or \(12\), none divisible by seven. These rank restrictions concern whole configurations of actual grids, not merely the counts \(n_i\).

## A local four-cycle term

At a graph vertex \(i\), form the seven-vertex graph \(\Gamma_i\) whose vertices are the mate-pair axes in \(N(i)\), with an edge when those axes lie in a rook grid through \(i\). A pair of axes determines at most one grid: its four opposite corners must be the second common neighbors of the four choices of one vertex from each axis. Then
\[
x_8^+\ \ge\ 2(n_0+n_1)+2\sum_i \# C_4(\Gamma_i),
\]
where cycles are unoriented and need not be induced.

Indeed, a four-cycle offers two matchings of its four axes. Each matching gives a pair of grids through \(i\) meeting only at \(i\): a common line through \(i\) would make them use a common axis. It produces a label \(2e_i+1_U+1_F\) as above. The two matchings use the same \(U\), hence have the same \(h=(A-3I)1_F\), but they have different tails, since their doubled labels determine the two grids uniquely. The resulting distinct equal-\(h\) tails give two signed neutral norm-sixteen differences, with twelve edges on each sign side, not the fourteen edges from a one-point grid pair. Conversely the signed tail difference recovers its two disjoint tails, then their common \(h\), their common \(i,U\), and both grid pairs. Their four \(\Gamma_i\) edges recover the original cycle; thus different cycles give different marked differences. This four-cycle lower bound and the earlier class-multiplicity lower bound refer to the same extra shell contribution and must not be added without further disjointness.
