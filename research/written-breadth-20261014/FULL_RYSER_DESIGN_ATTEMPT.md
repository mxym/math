# Ryser's complete design-minimum conjecture: actual binary witness attempt

14 October2026, Asia/Shanghai. Internal agent /root/written_breadth. Active ordinary breadth research, not a new theorem or publication.

## R0. Whole target and clock

Active stage starts at2026-10-13 21:10:15 UTC, after the bounded full-Chollet Gaussian-replacement stage. Service reviews/interruption time is excluded; after45–90 effective minutes without a substantial complete solution, preserve and autonomously change target.

Let Lambda_v^k be ALL v-by-v binary matrices with every row and column sum k. If the class contains symmetric(v,k,lambda) configurations, Ryser's conjecture asserts that at least one configuration attains the global minimum permanent on Lambda_v^k. A configuration means
\[
 AA^T=(k-\lambda)I+\lambda J,\qquad0<\lambda<k<v.
\]
The target is the complete assertion for every eligible(v,k), not a partial positive result at v13. A legal binary matrix whose permanent is strictly below EVERY configuration at its pair is a full counterexample. A matrix below only one nonminimal configuration is not.

## R1. Fresh primary status and first exact negative route

The current primary author report (read14 October2026) lists the full design-minimum conjecture as open and credits all eligible v<=12 cases. Its first remaining pairs are(13,4) and(13,9); configurations at each pair are unique up to row/column permutations: PG(2,3) and its complement, with reported permanents3852 and64803969. These counts will be independently recomputed. Uniqueness will be treated as a precisely matched disclosed classification input, and independently justified through the order-three affine-plane/orthogonal-Latin-square reduction before using it in any negative claim.

The same report already gives exact strict one/two-switch local bounds at v13 and searches through designs of order21. Those existing positive/local results are not re-counted. The proposed discovery instead uses nonlocal actual regular binary starts and alternating-cycle trades, with exact integer permanent/cofactor evaluation. Every absent violation is only finite discovery evidence, not a proof. The budget is bounded.

The 1960 original survey was located by DOI10.1090/S0002-9904-1960-10494-6, but the guessed direct publisher PDF was inaccessible in the browser. The actual whole statement was read in the primary author-maintained Minc entry; the original PDF will be fetched by a supported primary route if needed. No unseen original proof is claimed.

Primary report: https://yair-lavi.com/mincs-list/conjecture-5/index.html .
It explicitly states SOME configuration, not every configuration or unique minimization. This is distinct from Ryser's odd-order Latin-square transversal conjecture and from the Ryser–Woodall lambda-design generation conjecture.

## R2. Required counterexample verification

Any potential witness must have exact0/1 entries, exact row/column margins, and a strict integer permanent below the least configuration permanent. Two independently structured exact calculations (subset matching DP and inclusion–exclusion/Ryser) will check its permanent and the configuration baseline. All finite count recurrences and the configuration classification argument must be written out in an ordinary complete proof. No float solver status, incomplete configuration catalog, or sampled absence statement is an acceptance criterion.

No new Lean module/audit, agent spawn, push, publication, importance score or full-problem claim is authorized by this exploration record.

## R3. Complete ordinary justification of the unique configuration baseline

For a(13,4,1) configuration, any two row-lines meet in exactly one column-point. Each line has4 points and each point lies on4 lines. No pair of points can lie on two lines, since those two lines would meet in at least two points. There are13 binomial(4,2)=78 line-contained point pairs, exactly binomial(13,2)=78, so every point pair lies on one line. Thus the incidence structure is a projective plane of order3.

Choose one line as infinity and remove its4 points. The remaining9 affine points lie in four parallel classes, each partitioning them into three lines of three points. Pick two classes as rows/columns of a3-by-3 array. The other two classes give two orthogonal Latin squares of order3: every line meets each row and each column once, and lines of different classes meet in exactly one affine point.

Relabel rows, columns and symbols of the first Latin square so its first row and column are0,1,2. Its second row is forced to be1,2,0 (the alternative repeats2 in its third column), and the last row is forced; it is L(i,j)=i+j over F3. Relabel only the second square's symbols to make its first row0,1,2. Its second row starts either1 or2. The Latin constraints force M(i,j)=i+j or M(i,j)=j-i. The first is not orthogonal to L; the second is, because(i+j,j-i) is invertible over F3. Thus the complete affine plane is unique up to relabeling, and completing its four infinity points proves the projective plane is PG(2,3), uniquely up to incidence isomorphism. Every configuration at(13,4) therefore has the same permanent.

For a(13,9,6) configuration A, B=J-A has row/column sums4 and
\[
 BB^T=13J-9J-9J+(3I+6J)=3I+J.
\]
Hence its complement is precisely the same unique plane, so configurations at(13,9) are likewise unique. This is the known order-three classification, written out for counterexample completeness; no novelty is claimed for it.

The exact model is generated by the13 one-dimensional subspaces of F3^3, represented by nonzero triples with first nonzero coordinate1. Use the same representatives for line functionals, with incidence dot-product0 modulo3. Every line/point has degree4 and distinct lines meet once, by elementary linear algebra over F3.

The saved baseline verifier computes per PG(2,3)=3852 and per(complement)=64803969 by two independent exact methods:
\[
 d(0)=1,\quad d(S\cup\{j\})\mathrel{+}=d(S)A_{|S|+1,j}
\]
over increasing assigned-column subsets, and
\[
 \operatorname{per}A=\sum_{S\subset[v]}(-1)^{v-|S|}
       \prod_i\sum_{j\in S}A_{ij}.
\]
The first counts partial matchings; the second is inclusion–exclusion on missing columns in all row choices. These finite count identities do not replace any universal positive proof. They supply the complete all-configuration baseline that a strict actual witness would have to beat.
