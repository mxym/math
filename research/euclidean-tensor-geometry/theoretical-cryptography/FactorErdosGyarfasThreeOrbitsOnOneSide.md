# Three abelian orbits on one side of a bipartition

Let G be a **nonempty** finite simple bipartite graph of minimum degree at least three. Suppose a free abelian action preserves both parts and has at most three orbits on one of them. If G has no simple cycle of length 4, 8 or 16, the action has exactly three orbits on each part, the quotient is the simple K3,3, and G is cubic. Every component is a connected regular abelian K3,3 cover. The established rooted theorem and fixed-base census imply a 32-cycle through every vertex and minimum order 798, with exactly three nonisomorphic graphs at equality. The number of orbits on the other part is unrestricted.

## Four matching paths

Write the acting group as \(A\) and use additive coordinates. Freeness identifies every orbit with \(A\); an edge orbit between distinct fibers is a matching \(g\mapsto g+t\) for a fixed \(t\in A\). Two matchings on the same quotient pair have different offsets because the graph is simple.

Suppose two outer layers U,V have four length-two translation paths between them. The four intermediate layers may be distinct. Alternatively, precisely one pair may share an intermediate layer, provided the two paths use the same matching from that intermediate layer to V and different matchings to U. Compress the paths to matchings with offsets a,b,c,d from U to V. In the shared case label the paths sharing a middle layer by a,c.

If two compressed offsets are equal, their paths cannot be the shared pair, since the original parallel matchings are distinct. Thus the two original paths have distinct middle layers and close a simple 4-cycle. Assume all offsets are distinct. Write x=a-b and y=c-d. If x=y, the compressed word a,b,d,c is a simple square, starting at U at sheet zero and alternating forward and backward. If x=-y, use a,b,c,d. In both cases, its two V visits use respectively the unordered pairs {a,b} and {c,d}. Otherwise use the compressed length-eight word
```
a b c d b a d c
```
with alternating signs. The U sheets are 0,x,x+y,y, distinct because x,y are nonzero and x≠±y. The V sheets are a,a-b+c,a+c-d,c. Their six pair differences, up to a sign, are \(b-c,d-c,a-c,d-b,a-b,a-d\), all nonzero. In the two square cases the two U sheets are \(0,x\), and the two V sheets are \(a,x+d=c\) if \(x=y\), or \(a,x+c=d\) if \(x=-y\); the two V sheets are distinct in both cases. For the length-eight word the pairs used at V are {a,b}, {c,d}, {b,a} and {d,c}.

Expand the compressed square or length-eight cycle. In the shared middle fiber, all visits via either a or c use the same V matching, so each middle vertex determines its V vertex regardless of which of those path types was used. The two path types at the same V visit belong to one of the pairs {a,b}, {c,d}, not {a,c}, so no global repeat in that shared fiber is possible. In every other middle fiber, the same injectivity argument applies to a single path type. This excludes collisions even for torsion labels. The expanded cycle is simple and has length 8 or 16. This argument also proves the case of four distinct middle layers, so any translation subgraph over K2,4 has a short cycle.

## Reduce the number of layers on the other side

The [existing local reductions](FactorErdosGyarfasGeneralSixOrbitClassification.md#1-all-reduced-six-layer-templates) give a cycle of length 4, 8 or 16 if a quotient pair has three matchings, or if two doubled quotient pairs meet the same layer. Otherwise multiplicities are at most two and doubled pairs are disjoint. With one layer on the small side, the other side cannot meet minimum degree three. With two, each opposite layer would need a doubled pair, so there are at most two opposite layers and the existing six-orbit theorem applies.

With three layers on the small side, let k count opposite layers. At most three columns have a zero, because such a column must have a double, and doubled pairs are disjoint. For k≥6 the two rows with fewest zeros have at most two zeros together, so share at least four positive columns. The four-path lemma applies. For k=5 the two least-zero rows have at most one zero together unless the three zero counts are (1,1,1). The at-most-one case again gives four positive columns. In the exceptional case the three nonfull columns exhaust the double budget, and every row has one zero and one double. Removing a full column leaves a valid 3-by-4 quotient.

For k=4, any full column with a double can be capped by deleting one matching. If there is such a double, at most two columns are nonfull, since each of these requires a double of its own, and there are at most three doubles. If two zeros occur in the same row, the other two rows share all four columns and force a short cycle. Otherwise every row has at least three positive entries. Hence capping preserves minimum degree three in the only case still under consideration. If no full column has a double, capping is unnecessary.

## The six 3-by-4 types

After capping, columns are all ones or permutations of (0,1,2). Doubled rows are distinct. With two nonfull columns, the zero rows must be distinct because the same zero row would have degree two. The two sets of rows occupied by zeros and doubles either coincide or intersect in one row, giving two types. With three nonfull columns, each row is doubled once. The zeros either occupy all rows or have multiplicities (2,1,0), since a row cannot be zero in its own doubled column. There is just one type in each case. Along with zero and one nonfull column, this gives the six rows of the table.

| Row strings | Labeled count | Short-cycle step |
| --- | --- | --- |
| 1111 / 1111 / 1111 | 1 | Two rows share all four columns. |
| 0111 / 1111 / 2111 | 24 | The second and third rows share all four columns. |
| 0111 / 1112 / 2110 | 72 | Use the second and third rows. The first column gives two paths sharing the single matching to the second row, and the second and third columns give one path each. Apply the shared-middle lemma. |
| 0112 / 1111 / 2110 | 36 | Remove the second column. The remaining 3-by-3 quotient has minimum degree three and doubled pairs. |
| 0012 / 1210 / 2111 | 144 | Remove the first column. The remaining 3-by-3 quotient has minimum degree three and doubled pairs. |
| 0112 / 1120 / 2101 | 48 | Remove the second column. The remaining 3-by-3 quotient has minimum degree three and doubled pairs. |

In the last three cases the general six-orbit classification forces 4, 8 or 16 because the quotient is different from simple K3,3. This completes k=4, and with the preceding reductions establishes the theorem.

Once the quotient is simple \(K_{3,3}\), switch the labels on a spanning tree to zero. The subgroup generated by the remaining labels acts freely and transitively on each fiber of a connected component. Each component is thus a connected regular abelian cover of \(K_{3,3}\). The established [rooted result](FactorErdosGyarfasK33Rooted.md) and [census](FactorErdosGyarfasFixedBaseMinima.md) give a \(32\)-cycle through each vertex, at least 798 vertices per component, and exactly three graphs at equality. The same three witnesses are admissible here; there are no new minimal examples being claimed.

## A general incidence bound and a four-row reduction

Let \(m\) and \(n\) be the two part sizes of the quotient; the following argument doesn't require \(m\le n\). Let \(d\le m\) count doubled columns and write \(s_j\) for the number of positive rows in column \(j\). For a row pair, a **common column** is one with a positive entry in each. Every pair has at most three common columns by the four-path lemma with distinct middle fibers. Call a pair *marked* if in at least one common column one of its rows has a double. A marked pair can have at most two common columns: otherwise the doubled column provides two paths sharing their single matching toward the other row, and two other common columns provide the remaining paths. Each doubled column marks at least one pair since \(s_j\ge2\). A given pair can be marked at most twice, since doubled rows are distinct. If \(D\) is the set of marked pairs, this gives
\[
 |D|\ge \lceil d/2\rceil,\qquad
 3n-2d+|D|\le \sum_j\binom{s_j}{2}+|D|\le 3\binom m2 .
\]
For the lower bound an ordinary column has \(s_j\ge3\), and a doubled column has \(s_j\ge2\). Therefore \(n\le\binom m2+\lfloor m/2\rfloor\).

In fact, **for \(m=4\), one has \(n\le6\)**. We exclude \(n=7,8\), the only larger possibilities under the last bound. First, two doubled columns of support exactly the same two rows are impossible, since their doubled rows must be different. Those two rows and those two columns by themselves give a four-layer graph of minimum degree three (each layer is incident to one single and one double). This graph must have a short dyadic cycle by the earlier at-most-six-orbit theorem. We refer to the forbidden configuration as a mirror.

If \(n=8\), the displayed incidence bounds force \(d=4, |D|=2\), every doubled column to have support two, and every ordinary column to have support three. Indeed \(24-2d+\lceil d/2\rceil>18\) for \(d\le3\); at \(d=4\), there is equality throughout. Four double columns on only two support pairs force a mirror.

Now let \(n=7\). A doubled column with support at least three adds at least two incidences above \(3n-2d\), and an ordinary column of support four adds three. We use
\(21-2d+|D|\le18\), with those additions when applicable. If \(d\le1\), this fails already; if \(d=2\), equality would require a mirror with \(|D|=1\), all doubles of support two. The remaining cases are:

* **\(d=3\).** Any larger doubled support gives \(21-6+2+|D|\ge19\). The three double columns thus have support two, their pairs differ by the mirror exclusion, and \(|D|=3\). Each of four ordinary columns has three positive rows, and each marked pair has at most one ordinary occurrence. If every chosen triple contains a marked pair, there are at least four marked ordinary incidences, but at most three are permitted. Otherwise one triple contains no marked pair. The three marked pairs must form a star at the omitted row. The other three triple types each use two edges of this star, and any two occurrences of these other types share a star edge. At most one such occurrence is allowed, so at least three ordinary columns use the star-free triple. Every fourth three-row support intersects this repeated three-row support in at least two rows. Their pair thus occurs at least four times, a contradiction.
* **\(d=4\).** Here \(|D|\ge3\): if two marked pairs cover all four doubled rows, they are disjoint and all doubled columns have two-row support, so there is a mirror. The incidence bound now permits at most one large doubled support and no full ordinary column. If all doubled columns have support two, \(|D|=4\), and every ordinary triple contains a marked pair. Two equal triples are forbidden because each marked pair can have just one ordinary occurrence. The three distinct triples use \(9\) incidences, of which at most \(4\) are unmarked (there are two unmarked pairs, and a pair is in just two of the four triple types). Thus there are at least \(5\) marked ordinary incidences, more than the allowed \(4\). Finally, if one doubled column has larger support, it has support exactly three and \(|D|=3\). The remaining three doubled columns have support two and determine all three distinct marked pairs. Say the large column has rows \(A,B,C\) with \(B\) doubled, and call the fourth row \(E\). The marked pairs \(AB,BC\) each occur in a small doubled column as well as the large one, so no ordinary column may contain either. The only possible ordinary support triple is \(ACE\). But \(AC\) then occurs in three ordinary columns and the large doubled column, again four times.

This establishes the four-row bound without an assumption on the group order or a computer search. It does **not** classify the surviving cases \(m=4,n\le6\).

## Scope, priority, and verification

The earlier [general six-orbit classification](FactorErdosGyarfasGeneralSixOrbitClassification.md) applies without the part-preserving or bipartite hypothesis, but with at most six orbits in total. Here the part-preserving hypothesis is essential to the argument, and there is no limit on the number of orbits on the opposite part as an input condition. In particular this covers the part-preserving bipartite seven-orbit case. The present result is not the unrestricted Erdős–Gyárfás conjecture. Related results on bounded-order graphs and general minimal counterexamples by [Tranquilli](https://arxiv.org/abs/2608.02675) and [Ducoffe–Dumitru](https://arxiv.org/abs/2609.28594) have different hypotheses. Our literature and repository search did not locate a prior proof under the one-sided orbit hypothesis; this is not a priority guarantee.

The four-path idea and the original three-row proof were contributed by the independent Dreamer research pass; the audit redid the cap and collision arguments and supplied the sharper incidence calculation and four-row reduction. Run:

- `node verify_erdos_gyarfas_three_on_one_side.mjs`: exact \(325\) labeled capped arrays and \(366{,}320\) shared-path cyclic label cases. This builds the specified words explicitly.
- `node verify_erdos_gyarfas_three_on_one_side_independent.mjs`: independently generates quotient column multisets, recovers all six capped sizes and the \(24\) necessary seven-column templates in two row-permutation classes (each contains a mirror), and finds short cycles by literal graph search on \(3{,}247\) small abelian translation graphs without assuming the displayed words. Finite cases are cross-checks, not the all-group proof.
