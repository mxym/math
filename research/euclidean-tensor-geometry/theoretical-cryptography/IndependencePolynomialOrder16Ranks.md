# Which independence numbers occur in order-16 nonunimodal examples?

**Results.** A 16-vertex simple graph with a nonunimodal independence polynomial has independence number \(5,6,\) or \(7\), and each occurs for a connected graph. The minimum orders at independence numbers \(6,7,8\) are respectively **16, 16, 17**, also for connected graphs. This complements the [order-15 uniqueness and fixed-rank results](IndependencePolynomialOrder15Uniqueness.md). It is a classification of the possible independence *numbers* at order 16, not of all the order-16 graphs.

A general companion result gives the exact largest possible difference between the edge and triangle counts at fixed graph order and clique number, with equality characterization when there are at least four vertices outside a maximum clique. It gives a sharp threshold for a particular kind of nonunimodality at every independence number at least eight.

Work in the complement \(H\), with clique counts \(f_j=f_j(H)\), including \(f_0=1\), and write \(r=\omega(H)\), \(n=f_1\). These are the original graph's independence-polynomial coefficients. A failure of weak unimodality is a strict drop followed by a strict rise.

## 1. Sharp bound for an edge-to-triangle drop

Write \(q=n-r\) and choose a maximum clique \(K\). Let \(U\) be the remaining \(q\) vertices, with \(e\) edges, \(t\) triangles, and cross degrees \(d_u=|N(u)\cap K|\). Ignoring triangles with two vertices in \(U\) gives
\[
f_2-f_3\le \binom r2-\binom r3+(e-t)+
                 \sum_{u\in U}\left(d_u-\binom{d_u}{2}\right).
\]
The summands are at most one. Deleting at most one edge per triangle in \(U\) gives a triangle-free graph with at least \(e-t\) edges, so Mantel's theorem yields
\[
f_2-f_3\le \binom r2-\binom r3+\lfloor q^2/4\rfloor+q.
\tag{1}
\]
For any \(r\ge2\) this is attained: take \(H[U]\) complete balanced bipartite and attach each vertex in one part to a single fixed member of \(K\), and each in the other part to a different fixed member of \(K\). There are no triangles outside \(K\) or meeting both \(K\) and \(U\). The clique number stays exactly \(r\).

For \(q\ge4\), equality in (1) also has a precise description for a chosen maximum clique \(K\). The triangle-free graph obtained by deletion must attain Mantel's bound and hence must be complete balanced bipartite. To recall its equality argument: the neighbors of a maximum-degree vertex of degree \(\Delta\) form an independent set. Summing degrees over the other vertices gives an upper bound \(\Delta(q-\Delta)\) on edges; equality forces the other vertices to be independent too and all cross edges present, with part sizes as balanced as possible. In particular each part has size at least two when \(q\ge4\). In \(H[U]\), each added back edge is internal to one of these parts and belongs to at least two triangles with the third vertex in the other part. These triangles are disjoint as collections for the different added edges, since each has exactly one such internal edge. But the number of deleted edges equals \(t\) in the equality case, so \(t\ge2t\), forcing \(t=0\). Thus \(H[U]\) was already complete balanced bipartite. Equality also requires \(d_u=1\) or \(2\) for all \(u\), and no triangle using two outside vertices. The latter says that the unions of the \(K\)-neighborhoods of the two bipartition classes are disjoint. Conversely these conditions attain (1).

For every \(r\ge8\), the least \(q\) allowing \(f_2>f_3\) is consequently the least integer satisfying
\[
\lfloor q^2/4\rfloor+q>\binom r3-\binom r2.
\]
The attaining construction then also has \(f_4=\binom r4>\binom r3=f_3\), making this a sharp threshold for the specific valley \(f_2>f_3<f_4\). It need not give the minimum order for *all* valley shapes at higher ranks. For \(r=8\), the least \(q\) is nine. At that \(q\), the right side of (1) is one, so the equality description classifies all 17-vertex \(r=8\) examples with \(f_2>f_3\). They all do have the following rise: \(f_3\le56+9=65\), and \(f_4=70\) because no clique of size at least four can meet the outside set under the equality conditions.

## 2. Signed clique-count bounds

We use the classical linear-objective version of [Zykov symmetrization](https://m.mathnet.ru/php/archive.phtml?jrnid=sm&option_lang=eng&paperid=5974&wshow=paper), used for signed clique-count combinations by [Bollobás](https://doi.org/10.1017/S0305004100052063); see also [Liu–Pikhurko–Sharifzadeh–Staden](https://doi.org/10.1112/jlms.12777), §1. The application here is to a valley certificate, not a new symmetrization theorem.

For fixed \(n\) and \(\omega(H)\le r\), any linear combination of clique counts, even with negative coefficients, is bounded above by its largest value on complete multipartite graphs with at most \(r\) parts. To see this directly, partition vertices into classes of equal open neighborhoods (false twins). Each class is independent and any two classes have all or no edges between them. Given two nonadjacent classes, a clique includes at most one vertex from their union. The contribution per vertex to the objective is constant within each class. Replace all vertices of the lower-contribution class by twins of the higher-contribution class; no clique size increases, no existing class splits, and the two classes merge. The objective does not decrease, with this statement holding for either sign of any coefficient. Repeating gives a complete multipartite graph.

For part sizes \(a_1,\ldots,a_s\), the clique counts are the coefficients of \(\prod_i(1+a_i x)\). The companion code lists all sorted positive integer partitions of the indicated order into at most the indicated number of parts and multiplies these linear polynomials by integer updates. It gives three inequalities:

| Order | Clique number at most | Quantity bounded above | Maximum on complete multipartite graphs |
|---|---:|---|---:|
| 16 | 8 | \(7168f_3-2968f_4+663f_5\) | \(1075200\) (186 partitions) |
| 7 | 7 | \(f_2+f_3-f_4\) | \(30\) (15 partitions) |
| 16 | 11 | \(379f_4-236f_5+62f_6\) | \(117963\) (219 partitions) |

No linear optimizer or numerical tolerance enters the check of these bounds. The maxima bound the displayed quantities on the entire respective clique-bounded graph classes by symmetrization.

## 3. Close the order-16 cases

Run the exact colored-colex, Moon–Moser and maximum-clique recurrence of the [order-15 companion proof](IndependencePolynomialOrder15Uniqueness.md) at \(n=16\). This is a necessary-conditions envelope, as before. The companion code recomputes the table:

| \(r\) | Possible source ranks \(j\) of the first rise after a drop | Needed lower bound on \(f_j\) |
|---:|---|---:|
| 5 | 2 | not needed |
| 6 | 2 or 3 | not needed |
| 7 | 3 | not needed |
| 8 | 4 | \(220\) |
| 9 | 4 | \(175\) |
| 11 | 5 | \(637\) |

No other \(r\) survives the envelope. We now eliminate \(8,9,11\).

**Clique number eight.** There is no drop before \(f_3\): \(f_2\ge28>16\), and (1) shows \(f_2-f_3\le-4\) at \(q=8\). The candidate first rise \(f_5>f_4\) therefore requires \(f_3>f_4\). The first signed bound would then have left side at least
\[
(7168-2968+663)f_4+7168+663\ge 4863\cdot220+7831=1077691>1075200.
\]
This case in fact does not need the full numerical recurrence: the exact four-to-five colored-colex upper bound already requires \(f_4\ge220\) for a rise, and at ranks \(j=5,6,7\) every colored \(j\)-face on the sixteen labels can extend in at most \(2(8-j)\le j+1\) ways. Counting extensions and using the same colored colex bound rules out any subsequent rise there.

**Clique number nine.** Again \(f_2>16\) and (1) gives \(f_3>f_2\). Hence \(f_5>f_4\) would require \(f_3>f_4\). Fix a nine-clique \(K\); its outside set \(U\) has seven vertices. For a clique \(S\) in \(H[U]\) let \(d(S)\) be its number of common neighbors in \(K\). Its contribution to \(f_3-f_4\) is
\(\binom{d(S)}{3-|S|}-\binom{d(S)}{4-|S|}\), with zero for negative ranks. For \(|S|=1,2,3,4\), this is at most \(2,1,1,-1\), respectively. Let \(L\) be the sum of the deficits below these maxima for the outside cliques of sizes one, two and three. It is a nonnegative integer. Then
\[
f_3-f_4=-42+14+f_2(H[U])+f_3(H[U])-f_4(H[U])-L\le2-L
\]
by the second signed bound. If \(f_3>f_4\), we must have \(L\le1\). In particular:
- A singleton has \(d(S)\le4\), because all \(d\ge5\) give deficit at least two. Its contribution to \(f_5\) is at most one.
- An edge has \(d(S)\le3\), since \(d\ge4\) gives deficit at least three, and at most one edge can have \(d(S)=3\). Only such an edge gives a contribution to \(f_5\) (one).
- A triple has deficit \(d(S)\), so the sum of \(d(S)\) over the outside triples is at most one. In particular triples give no contribution to \(f_5\), and any outside four-clique has zero common neighbors in \(K\), since otherwise all four of its triples would have a common neighbor.

Consequently \(f_5\le\binom95+7+1+\binom75=155<175\le f_4\), a contradiction.

**Clique number eleven.** The fixed eleven-clique alone gives \(f_3\ge165>\binom{16}2\), and \(f_2\ge55>16\). The same calculation of contributions to \(f_3-f_4\), now on five outside vertices, gives
\[
f_3-f_4\le \binom{11}3-\binom{11}4+2\cdot5+\binom52+\binom53=-135.
\]
Thus the only possible drop before the candidate first rise \(f_6>f_5\) is \(f_4>f_5\). The last signed bound would then have left side at least
\[
(379-236+62)f_5+379+62\ge205\cdot637+441>117963,
\]
again impossible.

## 4. Connected witnesses and the minima

At \(r=5\), add one more isolate to the complement-side order-15 witness. At \(r=6\), take \(H=K_6\) together with ten isolates; this is precisely the [Levit–Mandrescu order-16 threshold example](https://arxiv.org/abs/1007.0880), with clique-count vector \((1,16,15,20,15,6,1)\). In both the original graph is connected.

For \(r=7\), place \(K_{4,5}\) next to a \(K_7\). Designate distinct \(z,w\in K_7\), and a special vertex \(x\) on the side of size four. Make \(x\) adjacent to \(K_7\setminus\{z\}\); attach each of the other three vertices on that side just to \(w\), and the five on the other side just to \(z\). There are no triangles with two outside vertices: the \(K_7\)-neighborhoods of the endpoints of any outside edge are disjoint. All cliques of size at least three are either entirely in \(K_7\), or consist of \(x\) plus vertices of \(K_7\setminus\{z\}\). The vector is \((1,16,55,50,55,36,13,2)\). Its complement is connected: the two outside parts become cliques, any vertex in \(K_7\setminus\{z,w\}\) has neighbors in both, and \(z,w\) each has a neighbor in an outside part.

At \(r=8\) the construction in §1 at \(q=9\) gives \((1,17,57,56,70,56,28,8,1)\), again with connected complement. Connectivity follows as the two outside parts become cliques, the unused \(K_8\)-vertices are adjacent in the complement to both parts, and the two used anchors each meet one outside part.

The earlier result uniquely specifies the order-15 example, with \(r=5\), and there are no smaller examples. Thus \(r=6,7\) both have minimum order 16. Since this note also excludes \(r=8\) at order 16, its minimum order is 17. The connected witnesses realize all three minima.

Run `python3 verify_independence_polynomial_order16_ranks.py` from the directory containing both checker files. It imports the preceding checker for the colored-colex recurrence, verifies the partition bounds using only integers, and checks the witness coefficients and connectedness directly. This is a check of exact integer inequalities, not a Lean or floating-point certification.
