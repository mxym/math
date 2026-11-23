# Anticomplete connected cubic supports are normalized-shadow classes

Let G be a hypothetical SRG(99,14,1,2), and let P and N be disjoint anticomplete induced subgraphs of minimum degree at least three. By [the anticomplete-shore theorem](anticomplete-cubic-shores.md), both are cubic. If their orders are da,db with gcd(a,b)=1, their common exterior height h is nonnegative integer with (A−3I)1_P=a h, (A−3I)1_N=b h, and Σh=11d, Σh²=2d². In these formulas h is zero on P∪N. In particular gcd(|P|,|N|)=d≥6, since Σh²≥Σh and d is even. The same argument also proves the following precise class and shell consequences.

## Connected supports and unique wing classes

For any connected induced cubic support C, define its normalized shadow

    σ_C = (A−3I)1_C / |C|.

This has value zero on C and on vertices anticomplete to C, and positive normalized contact count elsewhere.

Two distinct connected induced cubic sets C,D are disjoint and anticomplete if and only if σ_C=σ_D. One implication follows because the centered difference |D|1_C−|C|1_D has Rayleigh quotient 3 and is therefore a +3 eigenvector. For the converse, suppose the normalized shadows agree. If C intersects D but has a site x outside D, then σ_C(x)=0 gives σ_D(x)=0, so x has no neighbour in D. Thus there is no edge between C∖D and C∩D, contrary to the connectedness of C. The same argument with C,D exchanged excludes strict containment. Distinct sets with equal normalized shadow are therefore disjoint, and the outside-shadow identity then makes them anticomplete, rather than merely overlapping with few edges.

This partitions the connected induced cubic supports into classes of pairwise anticomplete supports. For fixed C, the remaining members of its class are exactly the cubic connected components of its literal anticomplete region: if a cubic connected D in that region is anticomplete to C, their shadow identity shows that every point of the region outside D also has no contact into D. Conversely any cubic component in the region is anticomplete to C.

If C is a component of a triangle wing W(T), of size 6k, its shadow is 2k/|C| on the three sites of T, k/|C| on the sixty sites beyond T and W(T), and zero on W(T). This follows from equal color size and balanced far contacts on each wing component. Its maximum recovers T uniquely, and the whole normalized-shadow class consists exactly of the connected components of W(T). Conversely all components of W(T) have this same shadow. In particular no connected cubic support belongs as a wing component to two different triangles.

## Allowed large classes

For any class with at least two members, its total number of vertices is at most 36 by taking one member and the anticomplete union of the others. Every member has even order at least six. The following useful restrictions are necessary, not assertions that these size profiles occur.

* In a class containing a six-site member, that member is an induced prism. Every other size is a multiple of six by the gcd bound. If the total reaches 24, the other members have total size 18, 24 or 30, and their union forces the class to be a literal triangle wing by the [cubic 18](prism-anticomplete-cubic18.md), [cubic 24](prism-anticomplete-cubic24.md), or [anticomplete 6+30](anticomplete-cubic-shores.md) theorem. Its whole class then has total size exactly 36. Thus a non-wing class containing a prism has total at most 18.
* No anticomplete pair of sizes (8,24) is possible. Here d=8, so the height on the 67 outside vertices would need Σh=88 and Σh²=128. But for nonnegative integer h, 2·1_{h>0}≥3h−h². Summing requires at least (264−128)/2=68 positive-height sites.
* In a class without a prism that has at least three members, the only possible size multisets are (8,8,8), (10,10,10), (12,12,12). If its smallest order is eight, the total cap and the gcd bound leave partner order eight or sixteen after dropping (8,24). A partner of sixteen and a third member would force an 8+24 anticomplete pair (only total 32 is possible in that mixed case), and four eights would force the same forbidden split. For a smallest order ten, the only partners permitted are ten or twenty, but twenty with two other members of order at least ten exceeds 36. If its smallest order is at least twelve, having at least three members forces exactly three twelves by the total cap. Thus every non-wing class of at least three members has precisely three, all of one order among 6,8,10,12; the only prism-containing such possibility is (6,6,6).

## Exact anticomplete-shell counts

Let N^+_(2s,anti) count oriented integral neutral +3 fields with b_i∈{−1,0,1}, both sign shores of size s, and no edge between those shores. The support equation gives that both shores are cubic. All their connected components are pairwise anticomplete, including components on the same side, and hence lie in one common normalized-shadow class. Conversely any two disjoint unions of components of one class with union sizes s yield such a field by the centered Rayleigh argument. The two literal shores recover the class and the unions, so this is an exact bijection, with both signs counted by taking ordered pairs.

For a triangle T let D_s(T) count unordered pairs of disjoint unions of its wing components each of size s. Let C^nw_(r_1,...,r_m) count non-wing normalized-shadow classes with exactly those member orders. Two useful specializations are

    N^+_(24,anti) = 2 Σ_T D_12(T) + 2 C^nw_(12,12) + 6 C^nw_(12,12,12);
    N^+_(36,anti) = 2 Σ_T D_18(T) + 2 C^nw_(18,18).

Indeed, a disconnected 12-shore consists of two prisms, so choosing one of them and taking the other plus the opposing 12-shore gives prism+18, a triangle wing by the theorem. A disconnected 18-shore could have component orders 6+12,6+6+6, or 8+10; the 8+10 possibility is excluded by the gcd bound against the opposing 18-shore, and a prism case is a triangle wing. Thus in the non-wing part both shores in either count are connected. A non-wing class containing two twelves has no prism, and any third partner must also be twelve by the classification and size bound. A class containing two eighteens has no third member. The coefficients 2 and 6 simply count oriented pairs of literal components.

These identities count the anticomplete signed-unit subset of the true +3 shells, not all their vectors; neither identity asserts nonemptiness of any class.
