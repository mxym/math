# At least 238 true neutral norm-28 fields in each maximal extension

For a fixed maximal determinant-49 extension H, let Z be the number of oriented **neutral norm-28** graph-coordinate fields whose eligible residue in the anisotropic residual plane is zero. Then
```
Z = 238 + 10 W014 + 72 W016 + 40 W018 + 16 W020 + 8 W022
        + 32 W121 + 8 W222 + 32 W226 + 8 W228
        + 16 W333 + 8 W335 + 8 W444 + 6 S.
```
Here the W counts are those of the [common higher moment dictionary](higher-moments.md), and S=W123−99−7W014≥0 counts the extra signed-unit charge-one cost-23 graph fields. All terms displayed on the right are nonnegative. In particular Z≥238+5N18(H), where N18(H)=8W018 is the eligible oriented norm-18 population. No positive charge of either sign is being counted in Z. The [short exact checker](neutral_norm28_identity.py) regenerates the harmonic rows and verifies equality by rational reduction. It imposes neither a rank-specific formula nor vanishing of any selected type.

The scope differs from the [two-type signed-coclique scalar bridge](norm22-johnson-positive-mass.md): no Hoffman coclique, support assumptions, or unique compatible coclique are needed. It also differs from the original norm-four scalar mass. In the fixed extension, the integral primal norm-four coefficient Y2 splits as Z+2W339: the other summands are charge ±3, of raw graph cost 39, not neutral. At rank 42 that is also the original determinant-49 lattice's coefficient. The existing scalar expression Y2=1000−8W014+200W016+88W018+64W020+24W022+48W333+8W024+16W335 already yields Y2≥968. The new bound is on the *separated actual neutral summand*, not a stronger total norm-four bound.

Averaging over maximal H gives the same identity in the folded mean coordinates. Nonzero isotropic classes of the original discriminant space enter a fraction 1/p of maximal subgroups, p=7^((44−r)/2)+1. Thus the mean of Z is Z0+(N28(graph)−Z0)/p, where Z0 counts original seven-class-zero neutral norm-28 fields. In particular at rank 42 Z is exactly the graph-wide oriented N28. None of these lower bounds alone implies a nonzero norm-18 population.
