# Antipodal five-grid core: only three panel-edge portraits

Assume the 27-site core consists of three disjoint rook grids, with two additional rook grids along corresponding perpendicular lines through their centers. Index the three bases by the same center, four arm, and four diagonal labels. The antipodal case means that the matchings between bases preserve the center and arm labels and swap the diagonals with their opposites. Every exterior contact word then uses either one center and two diagonals (C), or one arm of each axis and one diagonal (AB), by one-domination of the five grids. This configuration is not excluded below; the restrictions do not assume a particular AB contact table or any rank.

All three inter-grid matches are antipodal on the four diagonal labels, and preserve the five central/arm labels. Write the binary diagonal coordinates relative to the two fixed crossing axes. Antipodal adds (1,1), so its two panels are the two parity classes. Let F_i be the four diagonal sites in base i, and let C_i be the eight C-word sites adjacent to central triangle vertex i. A C-word between two diagonal bases uses either the same labels or antipodal labels: for adjacent displacement in the diagonal square, the two known within-base paths already fill both common-neighbor slots; for diagonal displacement equal or antipodal there is exactly one exterior slot (one third-base common neighbor or an actual matching adjacency, respectively). Thus the two diagonal contacts of any C word lie in one common panel. Using that panel sign divides the 24 C sites into \(12+12\), four on each side in each physical wing. Every AB word has the sign of its unique diagonal contact. There are 16 AB words with their diagonal in each base (eight of each sign).

The C sites form the remaining cubic triangle wing after its two true six-prisms. Every C site has exactly one C neighbor in each physical wing, plus eight AB neighbors. An AB site has four C neighbors, two in its diagonally contacted base and one in each arm base. Let \(m\) count C edges crossing the sign panels, \(t(y)\) be their degree at \(y\in C\), \(q_i\) count such mate edges inside \(C_i\), and \(q=\sum q_i\). Let \(k(z)\) count neighbors of \(z\in AB\) in its own sign panel among C.

## Cut norm and exact ticket floor

Take the signed diagonal test \(f=\sum f_i\), where \(f_i\) is ±1 on the four diagonal sites of base i by panel sign and zero elsewhere. Each diagonal site has two same-panel diagonal neighbors in the other bases and two opposite-panel neighbors in its own base. Thus \(Af\) vanishes on the 27-site core, is twice the panel sign on C, and is the panel sign on AB. Since \(f\) is centered, \(A^2f=12f-Af\). Evaluated at \(y\in C\) of sign s, this gives
\[
 2s(3-2t(y))+\sum_{z\in N(y)\cap AB}\operatorname{sgn}(z)=-2s .
\]
Its eight AB neighbors therefore contain exactly \(2t(y)\) of its own panel. Summing yields \(\sum_{z\in AB}k(z)=4m\).

Put \(a=1_{C_+}+2\,1_T\), where \(T\) is the central triangle; \(C_+\) has four sites in each physical wing. For \(G=3I-A+J/9\), the field \(Ga\) vanishes on \(T\) and the arms, is signed of absolute value \(t(y)\) on C, equals −2 or +2 on a positive or negative diagonal site (all four C neighbors are in its own panel), and has absolute value \(|2-k(z)|\) on AB. Also \(a^TGa=m\) and \(G^2=7G\). Therefore
\[
 7m=48+\sum_{y\in C}t(y)^2+\sum_{z\in AB}(2-k(z))^2,
 \qquad \sum_Ct=2m.
\]
Real Cauchy first gives \(16\le m\le30\). In the interval \(16\le m\le24\), integer convexity gives \(\sum_C t^2\ge6m-48\) and \(\sum_{AB}(2-k)^2\ge96-4m\), hence \(m\ge20\) after evenness. For \(24\le m\le30\) the corresponding bounds are \(10m-144\) and \(4m-96\), hence \(m\le26\) after evenness. Evenness follows for each of the six matchings individually because the two sides of every physical wing have equal panel counts.

For a fixed physical i, among the 16 cross-panel pairs in \(C_i\), exactly \(q_i\) are mates. Each of the other pairs has its unique additional common neighbor besides center i in the far layer, and it is not a diagonal site because diagonal sites see only one panel of C. It must therefore be an AB word with diagonal role i; conversely such words do have exactly two contacts in \(C_i\). These \(16-q_i\) distinct literal tickets each contribute one same-panel incidence.

To count those incidences at a specific \(y\in C_i\) of sign s, use \(A^2f_i=-Af_i+12f_i\). Here \(Af_i(y)=0\). Its two diagonal contacts in the other bases each contribute s (the matching to base i preserves parity). Its two other-physical C neighbors contribute their signs, and the four AB neighbors of diagonal role i contribute their signs. There are indeed four such neighbors: y has eight AB neighbors, one for each of the four arm labels in its own base by the common-neighbor equation with that arm (their one inner common neighbor is its own center). These four are the AB neighbors with an arm role in its base; all the other four have diagonal role i. The \(A^2f_i\) equation now says the number of those four matching y's panel sign equals the number of its two transverse C neighbors that **differ** in sign. Therefore
\[
 2(m-q)\ge\sum_i(16-q_i)=48-q,\qquad 2m\ge48+q.
\]
In particular the following three necessary portraits exhaust the possibilities:
- \(m=24,q=0\): all 24 transverse edges switch sign, and all 12 mates preserve it.
- \(m=26,q=2\): all 24 transverse edges switch sign; exactly two own-wing mate edges switch, in one physical wing.
- \(m=26,q=4\): exactly two transverse edges preserve sign, in the same inter-wing matching (evenness); its two physical wings each have two switching mates, and the third has zero. The per-physical ticket floor forces this distribution, since the two relevant wings each lose two required transversal incidences.

In the first portrait the mates are actually determined by the contact words: in one panel of \(C_i\) a mate must differ in both binary contact labels (otherwise the center and an additional diagonal would both cap its edge). The two four-site panels therefore have their canonical opposite pairs. There are no C triangles, because the transversals switch sign and a within-wing mate edge already has its unique cap at the center. In the second portrait the two same-panel AB tickets left in its affected physical wing must be assigned the same AB sign: exactly one contributes both matches and the other zero. The aligned ticket cannot join the opposite-word pair \((d,d),(\bar d,\bar d)\), since their same-panel diagonal-label demands are disjoint by the common-neighbor counts with \(F_i\).

## An exact complete frame in the first portrait

Write \(\phi_i\) for the signed panel vector on C_i. On AB, let \(t_i\) be the sign restricted to diagonal role i, and \(Q_i(z)=\sum_{y\in N(z)\cap C_i}\phi_i(y)\). Every AB word of diagonal role i then has \(Q_i=0\) (its two C_i sites are different-panel tickets), and its other two \(Q\) values are ±1. Use columns \(f,\phi,t,Q\), each a triple, and the \(3\times3\) all-ones matrix J in the following display:
\[
 Af=f(J-3I)+\phi(J-I)+t,\qquad
 A\phi=2f(J-I)+\phi(2I-J)+Q .
\]
Each block is literal: same-physical C mates preserve sign, transverse C neighbors switch, and each F site sees two C sites of its own sign in each other physical wing. The six-dimensional near span is invariant under the compression of A to non-AB sites. Write its operator \(M\). On the common three-coordinate constant direction and on its sum-zero directions the two matrices of \(M\) are respectively
\[
 \begin{pmatrix}0&4\\2&-1\end{pmatrix},
 \qquad
 \begin{pmatrix}-3&-2\\-1&2\end{pmatrix},
\]
each satisfying \(M^2+M=8I\).

Apply \(A^2+A=12I+2J\) to this centered six-space and project onto near versus AB. The exterior map has Gram \(4I\) on the six-space, so the six columns \(t_i,Q_i\) are mutually orthogonal with squared norms 16 and 32 respectively. The AB-induced adjacency acts on their span by \(-I-M\) via that map. In particular, at an AB word of diagonal role k and panel sign s, putting \(h=Q_0+Q_1+Q_2\) at that word, the graph's AB neighbor sums are exactly
\[
 \sum_{z\sim y,\ z\in AB_i}t_i(z)
       =2[i=k]s-s-h+Q_i(y),\qquad
 \sum_{z\sim y,\ z\in AB}Q_i(z)
       =h-3Q_i(y)-2[i\ne k]s .
\]
There are three AB neighbors of its own diagonal role and two of each other role, by the exact arm marginal counts (subtract from seven AB neighbors the counts having an A or B arm in the specified base).

Also \(Q_i\) sums to zero over the four AB words at any fixed diagonal site in another base. To see this, decompose that diagonal site indicator in the near space into its projection to the invariant six-span (a multiple of \(f_k\)) and its orthogonal complement. Their exterior images are orthogonal by the same polynomial identity and symmetry of the compressed operator. Its full exterior image is the literal contact indicator. Orthogonality of \(Q_i\) with \(t_k\) completes the claim. Thus on each 16-word AB diagonal group the three bits \((t_k,Q_i,Q_j)\) are balanced and pairwise orthogonal. Their eight sign-pattern populations are \(2+\epsilon_k t_kQ_iQ_j\) with integer \(|\epsilon_k|\le2\).

These are necessary graph-level restrictions. They do not exclude any of the three portraits or yield a realization.

## The finite sign-type check at m=24 and individual diagonal labels

The eight sign types in each of three AB diagonal groups are a 24-class partition. Let e(x,y) count unordered graph edges between two types, with a column used twice for degree sums when both endpoints are of the same type. For each source type and each diagonal group, impose its exact group degree (3 to its own and 2 to each other), exact signed sum of the \(t\) column, and exact neighbor sum of each \(Q\) column as above. The target is multiplied by the population \(2+\epsilon_k t_kQ_iQ_j\) of the source type.

Discard a type-pair edge column if a vanishing type is present or a same-type edge would need two distinct vertices of a singleton type. Also discard it if either endpoint cannot accept the other by an extreme sum: if \(|B t_i(y)|\) equals the known number of AB neighbors in diagonal group i, every such neighbor has that sign; if \(|B Q_i(y)|\) equals the known number of neighbors outside diagonal group i, they all have that Q sign. No actual edge is lost by these tests. The resulting exact necessary system is affine in nonnegative edge counts; no adjacency graph is posited.

Permuting the physical axes permutes the three \(\epsilon\)'s, and switching all the panel signs negates them. Sort the three and identify the triple with the sorted simultaneous negation. This gives 19 orbits of \([-2,2]^3\). In [the exact certificate](antipodal_sign_type_certificate.js) each of the 18 nonzero cases has an integer vector y with \(A^Ty\le0\) and \(b^Ty>0\). Its only program operations are small integer matrix generation and BigInt verification; no LP solver is used for replay. Thus **all three \(\epsilon_i=0\)** and every sign type has population exactly two. The zero case genuinely survives this quotient even with \(e(x,y)\) bounded by the product of distinct-type populations or the binomial of same-type population, as checked by the nonnegative denominator-four control in the file. This is not an exterior realization.

In fact the four AB words adjacent to **every individual diagonal label d** realize the four values of the other two Q signs once each. Fix a base k and panel s. The four AB words for each of the two individual labels d and its antipode have both Q signs balanced by the exact diagonal margins. Hence their sign-pair distributions across the two labels are either both flat, or complementary polarized: one label contains twice each of the same-sign pairs while the other contains twice each of the mixed pairs. 

At each diagonal vertex d, its neighborhood induces a matching. The four within-base core neighbors mate inside their two known grid triangles. Its two cross-base diagonal mates pair with the two corresponding C-word rung caps among its four C neighbors. The remaining two C neighbors (the equal-label words in the other two physical wings) have its own panel sign, so are nonadjacent since all transverse C edges switch panel. Each must pair with an AB neighbor. Consequently exactly one edge is present among the four AB neighbors with label d.

In a putative polarized split call a word all-aligned if both of its Q signs equal s, fully-opposed if neither does, and mixed otherwise. There are two of each kind of the first label's all-aligned and fully-opposed types; the other label contains the four mixed words. The frame requires three neighbors of the same t sign in their own diagonal group for a fully-opposed word, one for an all-aligned word, and two for a mixed word. A mixed word has an extreme Q sum on its aligned coordinate, so cannot meet an all-aligned word of the same t sign in that diagonal group. Summing the two-neighbor requirement of the four mixed words, their sole within-label edge supplies two incidences, so they use six edges to the other label, all to the two fully-opposed words. Each fully-opposed word consequently sees three of the four mixed ones. They share at least two of those plus the literal diagonal site d, contradicting the common-neighbor bound. Only flat remains.

Finally, the sole AB edge in the four-word block at d is incident with its fully-opposed word: neither of that word's non-diagonal physical C-neighbor signs agrees with its diagonal, so it cannot mate with either equal-label C neighbor of d in the neighborhood matching. The remaining constraints between different labels still permit local controls; this is not a closure of m=24.
