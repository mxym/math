# Two rank-36 families fail the same oriented norm-18 comparison

The [star bound](norm18-dot8-star.md) applies to the actual graph-wide N18 whenever N16=0. Two independently checkable lower bounds at rank 36 both exceed its 55,666 ceiling. In both rows every type not specifically absent is left unrestricted.

| absent selected unit types | graph-wide oriented N18 required |
|---|---:|
| 016, U026, U125, U230, U337 | ≥62,042 |
| 016, 024, U026, U127, U228, U230, U337 | ≥55,852 |

The first excludes the entire seven-type family {018,020,024,121,127,226,228}, the second the five-type family {018,020,121,125,226}, and all their subsets. These are not a full rank exclusion. In particular they remove two of the [seven surviving minimum-size rank-36 candidates](norm18-rank36-rootless-mark.md), {018,020,024,121} and {018,020,121,125}.

After these two exclusions only five size-four supports survive the accumulated necessary tests:
`{018,020,024,026}`, `{018,020,026,125}`, `{016,018,024,127}`, `{016,018,125,127}`, and `{018,020,125,127}`. This is a statement about the four-type filter, not about all supports at rank 36.

Both identities use [the native 205-column original/extension chart](original-site-populations.md), with p=2402 and graph-wide unit counts pV for the selected twelve nonisotropic types. The [standalone verifier](norm18_rank36_dot8_star.py) gives every integer coefficient and checks that the claimed residuals reduce to zero using the common rational equations. There are no fitted floating inequalities. In this notation S=W123−99−7W014 is the nonnegative compatible extra-mark count. The first identity retains
```
12N18 + U026 +14N16 + U337 +2U125 +2U230
 = 744492 + N20 +4 G022 +5 G228 +2 G335
   +2402S +14 G014 +33614 C014 +9(29372−G121).
```
Here G denotes graph-wide raw counts, C original-zero counts; charge-three G335 is counted once for positive charge. For the last term use the [positive-edge switch bound](u226-global-pressure.md) G121≤5,544+28P≤29,372, with the published P≤851. The first face therefore gives N18≥62,041, rounded up to an even 62,042 because N18 includes antipodes.

For the second face the checker gives, after the stated absences,
```
20726484 (N18−55666) ≥ 3846719880.
```
Its positive right-side remainder uses only four nonnegative raw populations; a compatible-minus-original coclique count W222−C222; the extra marks S; nonnegative G014 and C014; one nonnegative compatible-minus-original site slot; the original edge-mark histogram 99 C_(2,36,−2)≥693; and one nonnegative original site slot. Since 185·20726484<3846719880<186·20726484, antipodal rounding yields the second line. Neither identity needs to substitute a vanishing norm-14 count. Run `python norm18_rank36_dot8_star.py` beside the existing native chart sources with SymPy and python-flint.
