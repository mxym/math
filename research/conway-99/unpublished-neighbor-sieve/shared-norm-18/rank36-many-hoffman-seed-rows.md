# Rank 36: the neutral quartet with both (2,30) and (3,37) allowed

At mod-seven Seidel rank 36 assume the graph's selected unit support is contained in `{(0,18),(0,20),(0,24),(0,26),(2,30),(3,37)}`. The native graph-side marks simultaneously require at least **23 original Hoffman cocliques** and at least **27,820 oriented neutral norm-18 fields**. The [many-Hoffman empty-seed inequality](hoffman-vacant-n18-seeds.md) gives at most 26,600 of the same fields on this face, a contradiction. This excludes the entire six-type support and all its subsets; it does not exclude rank 36.

Write `M=C(2,22)` for the literal *original zero-class* (not averaged) charge-two cost-22 fields, which are negatives of 22-coclique indicators. Write `N=2402 W(0,18)` for the graph-wide oriented count. In this notation the two exact native inequalities are

```
786085623260 M >= 17318541628620
33025763694 N >= 918715744277044.
```

The [paired verifier](rank36_many_hoffman_seed_rows.py) reuses the integer [original-site mark chart](original_site_populations.py) and checks both identities in its exact 21-dimensional quotient. The ordinary marked/compatibility/nonnegativity rows have the original meanings; `root` is zero by the rank-36 no-Fano theorem; `444` and `SC('u',(3,37))` are nonnegative mass, not exclusions. `nest` is the graph-wide upper `29842-N`, valid when N16 and U127 vanish. The second certificate also uses the [original-class Sidon tangent](rank36_four_hit_sets.py) at t=34, exactly
`9Y2+18C014-(369+10t)M+(5t^2-4158)>=0` with `Y2=C028+2C339`. Only N16,U121,U125,U127,U226,U228 may be set to zero. In particular no alleged original `Y2>=968` is used, neither U230 nor U337 has been set to zero, and all vector counts refer to the indicated sectors.

Take ceilings, and use antipodal parity for N. For the many-Hoffman comparison, original C has discriminant class zero and is compatible with every neutral field; absence of U226 forces each N18 perpendicular to each such C. Any two original Hoffman cocliques intersect in 1 or 8: original compatibility gives intersection congruent to 1 modulo 7, and intersection 15 would give a forbidden neutral norm-14 field. Thus the stated graph-side inequality for M>=23 applies using precisely the required assumptions.

Adding this six-type containment exclusion to the [previous 29 seed conditions](rank36-joint-seed-hits.md) leaves **20** size-five supports passing those necessary tests, down from 22. The removed five-type supports are the neutral quartet with either U230 or U337 added. This does not certify that any remaining support occurs or exclude larger supports.
