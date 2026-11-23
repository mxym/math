# Rank 38: twenty-seven necessary hit sets and fifteen three-type candidates

For a Conway 99 graph of Seidel rank 38, at most 15 of the 220 possible positive three-type supports remain. This is not a rank exclusion. The previous [three-label panel analysis](panel-heights.md) already requires at least three short types at this rank. The fifteen sets below all have exact nonnegative rational controls of the stated stronger finite theta/packing system and strictly positive coordinates of precisely those types. Such controls are neither graphs nor actual lattices.

Use the [native verifier](rank38_three_hit_sets.py), [integer duals](rank38-three-hit-sets.json) and [rational controls](rank38-three-controls.json). From this directory run `python rank38_three_hit_sets.py` with python-flint. There is no LP solver in the verification.

## Higher-shell gluing for the original rank-38 lattice

Use the unrestricted coordinates, raw/selected distinction, packing inequalities and coclique/Fano tangents in [the rank-36 hit-set construction](rank36-four-hit-sets.md). At rank 38 the scale factor is **p=344** and the determinant of the original rank-44 lattice is 7⁶. Its primal Fricke scale is therefore **7⁸**, not 7⁷. No rank-36-specific scalar inequality is imposed. The determinant-49 extension pair uses the same scalar coefficients as before.

For j=15,…,20 the raw norm-2j labelings and the charge-three norm-(2j+11) labelings both occur in the sixty variables of the harmonic system. Since 7 does not divide j, both evaluations have nonzero residual quadratic value. The incidence probability for a global label to occur in a random maximal-extension residual class of its norm, including the per-eight normalization, gives

    X_j = p (W_(0,2j) + 2 W_(3,2j+11)).

This is the same class-counting rule as for j=8,…,13; the factor 2 is for charges +3 and −3, not two copies of a signed neutral field. For j=14,21, a label has isotropic seven-class. Every zero class lies in every extension; an isotropic nonzero class has incidence probability 1/p. The terminal discriminant plane is anisotropic, so this rule exhausts the possibilities. The original zero class count is exactly the primal coefficient Y_(j/7), including all charges permitted in that shell. Thus

    X_j + (p−1) Y_(j/7) = p (W_(0,2j) + 2W_(3,2j+11)).

All these original X and Y are evaluated by the fifteen-dimensional Fourier basis, not taken as new independent variables. The verifier adds these eight physical equalities to the original 39-row-rank system. Its new rank is 41 on 63 homogeneous variables. No claim is needed that each of the eight equations independently increases rank.

## The graph rows

The conditional prerequisites are exactly as in the [rank-36 file](rank36-four-hit-sets.md) and are checked separately for every dual. There are five additional raw, *isotropic* marked-population lower bounds. W236≥693 is the ordinary edge mark; W042≥8316 is the ordered-nonedge neutral difference; W353≥8316 is the three-positive path mark; W460≥8316 is the four-positive paw mark. The counts of the respective configurations are 693, 99·84, 99·(91−7) and 231·3·12. Distinct markings in each of the three small positive-set families cannot coincide: their differences would be balanced integer +3 eigenvectors of positive mass at most four, below the mass-six minimum. The nonedge marks have unique +3 and −3 coordinate locations. Their indicated charges and squared costs follow from the [mark dictionary](../../rank-34-short-support/README.md). All five types of bound concern genuine zero-class or compatible graph fields, so they occur in every applicable extension without a factor p or an eightfold division. Finally,
    
    W339 ≥ 231 + 22M + S,

by the [disjoint mark construction](coclique-sidon-cut.md) in each extension: one field for each triangle, twenty-two fields per compatible coclique, and one per remaining unit (1,23) field by its negative-edge switch. Among these five additional inequalities only this last one is needed by the stored exclusion duals.

## Exact coverage and the surviving relaxation

Each of the 27 listed sets must meet the true unit support, irrespective of its size: the verifier independently reduces each positive linear combination to a strictly negative multiple of W000=1 under precisely the zero hypotheses listed. No listed hit set contains another listed set. The counts of candidate supports by size 0,…,12 are:

| Test | Remaining support counts |
|---|---|
| All 27 hit sets | 0, 0, 0, 16, 161, 505, 790, 760, 492, 220, 66, 12, 1 |
| Also require [N16>0 ⇒ U(1,27)>0](exclusion.md) | 0, 0, 0, 15, 136, 388, 584, 561, 373, 175, 56, 11, 1 |

At cardinalities four and above these figures describe just the hit-set and support-implication filter. At cardinality three the exact 136-row relaxation has strictly positive rational controls on all remaining cases. With 26 denoting the **unit** neutral norm-26 type and with e.g. 125 denoting U(1,25), they are:
```
16 18 127       18 20 24        18 20 125
18 24 26        18 24 121       18 24 125
18 24 127       18 24 226       18 121 125
18 125 127      18 125 230      20 24 26
24 26 230       26 125 230      26 228 230
```
For each control the verifier requires the declared denominator positive, W000=1, and nonnegativity of all raw counts, selected unit counts, unconditionally imposed slacks, and relevant conditional slacks. Its exact positive support must be the listed triple. These checks do not impose integrality of a real graph or prove that any of the fifteen candidates is realizable.
