# Packing good norm-16 triples by their common cube

If no integral neutral field has squared norm 20, then the graph-wide oriented count satisfies **N16 ≤ 6,496**, with no symmetry or Seidel-rank assumption. At Seidel rank 36 the same oriented count would be **at least 6,880** if the selected unit types were contained in **{016,024,127,228,337}**. Thus that five-type containment and every subcase are impossible, not rank 36 itself.

## Triple geometry

Use the [norm-16 packing and overlap theorem](../norm16-packing.md). Each oriented field has independent eight-element signs inducing a 4-regular bipartite support. Fix a positive root o and three actual independent negative neighbors T. The fourth negative neighbor x must be chosen from eight sites. Each x specifies at most one field. Every far site is indexed by its two neighbors of o: an unordered nonmate pair in the fourteen-site neighborhood. Each such pair has a unique second common neighbor beyond o, and every far site occurs exactly once.

Let m≤8 count the fields at (o,T) and let g be the good ones: all three far centers indexed by the pairs of T are positive. In an arbitrary field each of the three parents has three more positive neighbors; the seven far positives meet T at most twice each. If z are indexed by pairs of T, then exactly z−2 miss T, whence z=2 or 3. Likewise the four negative parents T∪{x} send twelve incidences to the seven far positives; at least five of their six pair centers must be positive. Therefore at least two of the four three-parent subchoices are good (all four if all six centers are positive).

For two fields at the rooted triple, their dot is at least five: they match at the three given negatives, o, and at least z+z'−3 common pair centers. A positive of one field that is negative in the other misses T, so the number of opposite signs is at most (z−2)+(z'−2). Thus the difference has squared norm at most 22, and is signed-unit; the fields have no opposite-sign overlaps. The [overlap theorem](../norm16-packing.md#a-bound-on-the-overlap-of-two-norm-sixteen-vectors) states that if either same-sign intersection is at least four then both are exactly four, and that dot seven is impossible. In particular two good fields share exactly four positives and four negatives. A good and a bad field have dot at least six (o and two centers plus the three parents). If N20=0 then dot six is excluded by their difference and dot seven by the overlap theorem, so their dot is eight and both intersections again have size four. This is the only use of N20=0.

### Four good fields force a cube

In each good field the positive centers A,B,C of the three pairs of T each have two negative neighbors in T, and two further ones. Its fourth root parent x cannot see any of A,B,C: o and each center already share two parents. The six further incidences of A,B,C thus fall on four negative sites other than T∪{x}. They consume at least two common-neighbor-pair slots of A,B,C. Each pair already has one common negative in T and at most one outside T. If the three possible outside witnesses were distinct (or some nonexistent), each field would select at least two of at most three sites, while any two fields can share at most one outside-T negative. There are at most three such fields. Consequently if g≥4 the three pair witnesses all coincide: an outside site shared by two different pairs sees all three centers. Every good field must use that same negative site. Together with T and the four fixed positives {o,A,B,C} it gives an induced 3-cube Q, with its stated signs.

Every good field contains exactly four more sites of each sign, outside Q. Each cube vertex needs one further neighbor of the opposite sign. Two same-sign cube sites already have their two common neighbors in Q, so these eight new sites match bijectively with Q, each seeing just its one cube mate. The remaining support induces a 3-regular bipartite graph on four plus four sites, necessarily a second 3-cube. These complementary cubes of different good fields are disjoint, by the exact (4,4) overlap and absence of opposite signs.

Each outside site meets Q at most once on either shore. There are 20 double contacts: each of the twelve cube edges needs one cap and each of the four opposite-parity antipodes two witnesses; none lie inside Q. The number of singleton contacts is therefore 8(14−3)−2·20=48. Each complementary cube uses eight different singletons, so g≤6.

### Bad fields cannot fill the remaining choices

Given g≥4 good fields and a bad field, the bad field uses precisely three positives of Q. Its five remaining positives include exactly one in each good complement, by the (4,4) good/bad overlap. Hence g≤5 if any bad field exists. If z is the bad field's fourth root parent, then it necessarily uses all three far sites indexed by {a,z}, a∈T: at least five of the six full-parent pair centers are positive, and one T-pair center is missing. These three sites are outside Q. At least g−2 of them must be in the union of the g good complements, since only 5−g of its five non-Q positives can lie elsewhere.

In any one good complement there are precisely three positive sites meeting T, one matched to each of the three negative parents. If x is the good field's fourth root parent, it uses at least two of the three pair centers {a,x}, a∈T, by the same five-of-six condition. Thus all but at most one of these three complementary positives have their second parent equal to x. In particular that good complement supplies at most one required {a,z} across **all** bad fields: their fourth parents z are distinct and never x. If b=m−g is the number of bad fields, this proves b(g−2)≤g. For g=4 or 5 this gives m≤6; for g=6 there is no bad field. Thus g≥4 always implies m≤6.

We have 2g+3m≤30: use m≤6,g≤m or else m≤8,g≤3. There are 99·C(7,3)·8=27,720 possible rooted independent triples. Each oriented field appears 8·4=32 times and is good at least 8·2=16 times. Summing gives 128N16≤831,600, so N16≤6,496.

## Matching native rank-36 lower bound

The [exact verifier](norm16_good_triple_cube.py) checks the following two coordinate identities in the [rank-36 Fourier and fixed-extension dictionary](rank36_four_hit_sets.py); no new numerical program is needed. N16,N18,N20 count both orientations, the remaining U are signed-unit counts with positive charge (or both orientations if neutral). Each displayed population equals 2402 times its corresponding normalized unit column. The only potentially negative term in the certificate is a multiple of the **graph-wide** N14, zero by the [rank-36 Fano exclusion](../rank36-no-fano.md). Other terms are explicit nonnegative raw counts, S, or the original nonnegative coefficient slacks Y1, Y2, Y3 named in the native checker.

```
18292 N16 + 4707 N18 + 678 N20 + 117 U026
 +1090 U121 + 428 U125 + 60 U226 + 448 U230 ≥ 125821140.
3312 N16 + 687 N18 + 7 U026 + 56 U125 ≥ 4747792.
```

The second additionally uses the established [G121 ≤ 29,372 graph bound](u226-global-pressure.md). On the displayed five-type containment all columns in the first row except N16 vanish. Thus N16≥6,880 by integrality and antipodal parity, contradicting the graph-side 6,496. More generally if just N20=0, the other six terms left after removing N16 sum to at least 6,996,308. The second inequality separately forbids the simultaneous absence of N16,N18,U026,U125, irrespective of the eight other selected types.
