# Ranks 40 and 42 exclude the three-neutral support {020,024,026}

Assume that the only permitted selected unit types are neutral costs 20,24,26. The [original large-Hoffman bound](hoffman-fano-large-family.md) supplies at least 78 original zero-seven-class Hoffman 22-cocliques at each of ranks 40,42. Fix any maximal determinant-49 seven-extension H. Its full eligible family has size M=W222 at least 78. Use all M actual members in this one H, not a mean of products over extensions. We prove this is impossible. Other supports and the unrestricted problem are not thereby excluded.

## Count incidences of cost 39

Write c_D=−1_D, d_x=(3I−A)e_x. A true charge-a cost-t field b has sum −11a, squared norm t and Ab=−4b−2a·1. For fixed D write K_at[d] for the one-angle H-eligible population with b·c_D=d, using the usual orbit-folded mass for that shell. W is its marginal. Types 123,222,339,014 have isotropic seven norm, so these particular W/K are actual H-eligible counts with no factor of eight. Addition by c_D permutes eligibility and preserves the residual seven-class: it is trivial in the final anisotropic plane. In particular the map b↦g=b+c_D is a bijection from K123[−3] to the cost-39 charge-three fields at angle 19. Each D has K123[−3]≥22 by the 22 distinct site fields d_x, x∈D. Denote mean over D by a bar.

In counting these incidences set aside two disjoint actual families. First, the 231 distinct triangle fields g=Σ_{x∈T}d_x have angle 12−7|D∩T|≤12, since d_x·c_D=4−7·1_D(x). They have no incidence. Their three +1 sites recover the triangle, and they all have zero seven-class. Second, a field with +2 at x has no further exceptional sites since Σg_i(g_i+1)=6. Its fourteen neighbors must all be −1 by the field equation, so subtracting d_x gives c_E for an eligible 22-coclique E with x∈E. Conversely these 22M fields g=d_x+c_E are distinct by their +2 site and its inverse. An extreme angle gives |D∩E|+4−7·1_D(x)=19. Besides the generating D=E, this requires |D∩E|=15 and x∈E\D. A directed pair E,D meeting in 15 maps injectively to the oriented Fano difference (the sign supports determine the two exclusive parts, and the 15 vertices outside both sign supports seeing neither sign determine the common part). Thus there are at most 7W014 extra incidences from this family.

Every other g has at most four incidences. Distinct eligible cocliques meet in 1,8 or 15. Two at angle 19 cannot meet in one because g−c_C−c_D would have charge −1 and cost 39+44−76+2=9. A 15-pair has no third common 8-neighbor: by the [Fano endpoint intersection table](../../marked-coset-shells/README.md) every third compatible coclique meets each endpoint in one. Consequently five extreme cocliques would meet pairwise in eight.

For such five, put k_i equal to the number containing i. Then Σk=110, Σk²=270, k·g=−95, g·1=−33, g²=39. Subtraction of the real projection onto 1,g gives the exact identity
```
Σ_i [k_i − (5/12)(1−5g_i)]² = 105/4.
```
The cost budget six shows that after removing the +2 family a −3 could only coexist with no positives, contradicting Ag=6 at that site. At least two −2 could coexist with at most one positive, contradicting Ag=2 at a −2. Thus either g has three +1,36 negative units,60 zeros or it has two +1,one −2,33 negative units,63 zeros. In the first case just taking the closest nonnegative integer at each coordinate gives at least 3·25/9+36/4+60·25/144=111/4>105/4. In the second, every one of the five cocliques contains the double: g−c_D has charge one cost23 and cannot have a −2 (at such a site adding d_i gives charge two cost22 with a positive entry, impossible). The coordinate minima with k=5 at the double are 2·25/9+25/144+33/4+63·25/144=299/12, leaving only 4/3 slack. A positive-site hit costs at least (1+5/3)^2−(5/3)^2=13/3 extra, so there are none. Each member thus meets 17 singly negative sites and the double, leaving four zero sites. On zero sites an integer occupancy k costs k²−5k/6≥k/6 above the baseline; the 20 hits cost at least 20/6, a contradiction.

Summing now gives the necessary graph inequality
```
M (mean K123[−3] − 22) ≤ 4(W339 − 231 − 22M) + 7W014.        (1)
```

## An exact, single-H angular identity

At each eligible D, the [standalone verifier](three_neutral_hoffman.py), standard Python only, proves the equality
```
9(78 K123[−3] − 4 W339 + 56 M − 7 W014) − 952
 = 590 K444[9] + 172 K333[12] + 426 K333[5]
   + 484 K335[12] + 230 K335[5] + 112 K232[8] + 224 K232[1]
   + 702 K123[11] + 306 K014[7] + 153 K014[0].                  (2)
```
No angular population on the right is assigned a value. All are nonnegative in the usual fixed-H, anti-isometry-averaged K normalization, i.e. eligible counts divided by eight at nonisotropic norms only. No graph automorphism is used.

For reproducibility, (2) is a linear combination of thirteen of the [rank-48 quadratic equations](../short-shell-moments.md) for the four determinant-49 gluings. At each gluing every harmonic quadratic has total on norm four plus 48 times its total on norm two equal to zero (the weight-26 cusp relation). Ten equations are on or traced over the four-space as in the original proof. The remaining three use h=(0,0,0,0),(1,2,3,1),(1,−1,1,−2) at the third shift: the test vector is v=63 y_D+3 h in the orthogonal graph and auxiliary spaces. Here y_D is the graph realization of the centered negative indicator c_D (the negative of the conventional positive-indicator mark divided as in the coclique correspondence), of squared norm 22/9. Thus v²=9702+9hᵗBh and the graph part of its pairing with b is 9d−22a. With the auxiliary projection covector g equal to three times its integral pairings, use 48(9d−22a+g·h)^2−v²||x||². The usual four-dimensional projection bounds by Cauchy are exhaustive. Negation doubles fields of positive charge, never the uncharged shell, and reversal of b and hence of its angular sign is accounted for in canonicalizing b to its negative. No mean over Hoffman directions is taken until (2) is proved at each D.

The graph-side atom cuts use d≡4a (mod 7) and centered Cauchy (9d−22a)²≤154(9t−11a²). An eligible 20- or 22-neutral field has angle zero: ±7 would produce forbidden raw G228 or G230 respectively under a coclique shift; larger absolute multiples either violate Cauchy or give a still shorter impossible charge-two field. Types 016,018,121,226,228,230,337 vanish in full; raw 125,127 additionally vanish by the exact site subtractions from 016 and from 018/226. The permitted 026 equals its unit count (its only nonunits need 121), but is not set to zero. Raw 123 and 014 remain unrestricted. The verifier joins only physically equal atoms: shift by jc_D, then add a constant to fold to charge in [−4,4], and optionally negate. Before folding the cost is t+22j²+2jd and the angle d+22j. All these shifts preserve the residual norm class and normalization. The centered cost numerator changes by 154j²+2j(9d−22a), so the checked integer interval [−6,6] finds the global minimum representative for every input at norm at most four. An impossible translate in that interval discards an impossible atom; no converse assumption is needed. The rational row multipliers and literal coefficient comparison are in the verifier.

Finally average (2) over the M eligible D and put
```
G = 4(W339 − 231 − 22M) + 7W014 − 78(mean K123[−3] − 22).
```
Since M≥78 and every K123[−3]≥22, (1) requires G≥0. But (2) implies
```
G ≤ −16288/9 − 32(M−78) < 0.
```
This closes the stated three-type face in both ranks without an integer program or candidate-graph enumeration.

The [four-type extension](three-neutral-plus-u125.md) permits arbitrary unit charge-one cost-25 markings, without weakening the contradiction at either rank.
