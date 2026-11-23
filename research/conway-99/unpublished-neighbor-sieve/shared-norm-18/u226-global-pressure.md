# Graph-wide norm-18 pressure without a support-size assumption

At rank 36, **at least one of neutral norm 20, unit (1,27), unit neutral norm 26, and unit (1,25) must occur**. More quantitatively, if N20 and U127 are both absent, then the actual positive-charge U125 count and oriented unit neutral U026 count satisfy
```
U026 + U125 ≥ 65,240 .
```
The other eight selected types are not assumed absent. At rank38, on the six-type superset {018,024,226,228,230,337}, the **same oriented neutral norm18 count** appearing in the geometric upper obeys **10,447≤N18≤16,166**. This is a partial, not contradictory, two-sided count.

In the standard folded, true-unit coordinates V of the [fixed-extension harmonic system](higher-moments.md), write F=W014, M=W222 and S=W123−99−7F. The [exact row-span checker](u226_global_pressure.py) verifies in the full native cone, without imposing any vanishing,
```
6V018 + 5V016 + V020 + V026 + 17V121 + V125 + V127 + 9V226
 = 291 + 16F + 2S + 5M + 3V228 + V337.
```
Equivalently the constant and extra (1,23) terms on the right are 93+2W014+2W123+5W222. All terms on its displayed right are nonnegative. Average over maximal extensions first: for these nonisotropic selected V, their actual graph counts are p times the resulting means, p=7^((44−r)/2)+1.

If U127=0, the [norm-16 injection](exclusion.md) gives N16=0. The [positive-pair](u226-positive-pair.md) and [midpoint bound](u226-pair-midpoint.md) give G226≤4158: at most one occupied field per unordered nonedge. If N20 is absent as well, the [rooted norm-18 bound](panel-heights.md) gives N18≤16166. Therefore the true graph populations satisfy
```
U026 + 17G121 + U125 ≥ 291p − 9·4158 − 6·16166 .
```
For rank38 on the stated six-type support, U026,G121,U125 are also absent, so retain the N18 term instead of bounding it: 6N18≥291·344−9·4158=62682.

To get the stronger rank36 statement, we need a graph-wide upper on G121. Recall [the proven rooted-wing uniqueness](affine-triples.md): for a charge-one cost-21 label the unique positive edge pq determines two 12-wings; its negatives choose one of the two alternating colors of each cycle of the union of the p-wing mates, q-wing mates and the cross matching. The full label is then determined by this coloring. Each cycle length is a multiple of four: its edges alternate between within-wing mates and cross edges, and the number of cross edges is even. With j four-cycles, the remaining components have length ≥8, so at most j+floor((6−j)/2) components in total. For j=0,…,6 the resulting number of colorings is at most 8+28j/3. Each four-cycle together with p,q yields a genuine induced triangular prism whose rung is pq: the two mate edges complete the end triangles, and the two cross edges are the remaining rungs. Conversely each prism is counted at each of its three rungs. Thus Σ_{pq}j=3P and
```
G121 ≤ 8·693 +28P ≤ 29,372
```
by the [global prism cap P≤851](../../rook-array-exclusion/triangle-pair-packing.md). Subtracting 17·29372 at p=2402 gives the claimed 65,240 lower bound. Among other consequences, a putative rank36 graph cannot have its selected support contained in the seven types {018,024,121,226,228,230,337}. This does not exclude rank36 or any particular unrestricted graph.

The [disjoint transfer inequality](u226-disjoint-transfers.md) also yields a weighted rank-36 floor when U127 is present, assuming N16 and N20 vanish.

**Sharpening on the smaller support.** The [norm-18 identity independent of the norm-24 and (2,26) counts](norm18-u226-lower.md) raises the rank-38 oriented lower bound to 12,040 when only the three types {018,024,226} are allowed. The upper on those same markings is still 16,166. The wider six-type lower bound in this note is unchanged.
