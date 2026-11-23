# Two fields on one positive diagonal force a norm-16 field

This sharpens [the positive-pair classification](u226-positive-pair.md). In one maximal determinant-49 extension, if eligible N16 is absent then **at most one** c=0 field of charge 2, cost 26 has a given positive pair p,q. With both U127 and N16 absent graph-wide there are therefore **at most 4158 positive-charge U226 fields** in the whole graph: one per unordered nonedge. The diagonal involution in the linked note pairs these fields, but gives no further factor of two in this upper bound.

Let Z={z,w} denote the two (zero-valued) common neighbors of p,q and let Q={p,q,z,w}, an induced square. Its four edges have distinct triangle caps, and these are the only exterior sites meeting two or more corners (opposite corners already share their two other square corners). Each corner has ten pure neighbors touching that corner only. The linked classification shows exactly where a c=0 field b lives: it is +1 on p,q, −1 on all four caps (the hub mates of z,w), −1 on six of the ten pure neighbors at each p,q, and −1 on four of the ten pure neighbors at each z,w. It is zero elsewhere.

Write D_Q=Σ_{i∈Q}d_i. It takes value +1 on the corners, −2 on the four caps, −1 on the forty pure sites, zero elsewhere. Then f_b=2b−D_Q is a genuine neutral −4 eigenfield, equal to ±1 throughout the *same* 44 sites (corners and pure neighbors) for every such b, zero elsewhere. In particular ||f_b||²=44 and f_b(p)=f_b(q)=+1. On the p- and q-pure neighbors its +1 sites are exactly the four-sets U,V of the linked classification.

For two different b,b′ with the same positive pair let d=|U∩U′|=|V∩V′|≤3. The linked partial-bijection proof gives ||b−b′||²=32−8d. Since the parities of f_b and f_b′ agree at every site, their midpoint a=(f_b+f_b′)/2=b+b′−D_Q is an **integral eligible neutral** eigenfield. By the parallelogram identity,
```
||a||² + ||b−b′||² = 44,    hence ||a||²=12+8d.
```
At d=0 this nonzero field would have forbidden norm12. At d=1 its norm is 20. Its signs are unit, with +1 at p,q and at the common point of the two U's and that of the two V's. Thus its positive side spans at least two distinct edges, one at each hub. But the [neutral edge-switch identity](../edge-switches.md) gives 5e≤d₀²−19d₀+99 for a signed-unit neutral field with d₀ positives, e its number of positive edges. At norm20, d₀=10 and so e≤1. At d=3 the difference would have forbidden norm8. Therefore d=2 is compulsory and b−b′ is itself a genuine eligible signed-unit norm16 field (the midpoint has norm28). The assertion follows; this does not by itself exclude any support or rank.

**Rank-38 application.** For the remaining selected support {018,024,226}, the [certified lower bound](u226-rank38-forcing.md) forces at least 363 distinct marked squares and an edge shared by at least three of them. These bounds do not by themselves exclude that support.

**Unconditional strengthening.** The [height-two edge bound](norm16-height-two-edge.md) also rules out the norm-16 difference constructed here. Therefore a positive pair supports at most one c=0 field even when norm-16 fields are present elsewhere. The other U226 subtypes are not covered.

**Global use.** The [signed population identity](u226-global-pressure.md), combined with the 4,158 cap when U127 is absent and a sharper prism bound for U121, gives a rank-36 four-family hit without a support-size restriction. The [disjoint transfer bound](u226-disjoint-transfers.md) applies even when U127 is present.
