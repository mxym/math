# A five-family necessary hit at ranks 40 and 42

At either rank, at least one selected unit type from
`{018, 127, 228, 230, 337}` occurs. Equivalently, even allowing all of `020,024,026,121,125,226` simultaneously is impossible in the absence of those five. The remaining named type 016 is automatically absent because every neutral cost-16 field yields a true unit (1,27) field; see [the site subtractions](../short-shell-moments.md) and [norm-18 exclusion](exclusion.md). This does not exclude either rank itself.

Assume the five named types absent and fix an individual maximal determinant-49 extension H. The [large-family theorem](hoffman-fano-large-family.md) supplies at least 78 **original** 22-cocliques, thus M≥78 eligible ones in every H. The rank-42 hypotheses require 016 absent, as just proved. We use the notation and graph inequality (1) of [the true Hoffman incidence proof](three-neutral-hoffman.md). For each actual eligible D, K_at[d] is its own angular histogram, W_at its H-marginal; M=W222. Both are divided by eight at nonisotropic terminal norms only. Neutral 20,22 are perpendicular to D since charge-two 228,230 vanish in full. The full 228, 230 and 337 vanish because these shells are already unit by the [short-shell classification](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units), regardless of the new permitted types. Raw 123, 125 and 026 are unrestricted; in particular raw 026 need not be its unit count. Raw 127 is **not** set to zero: its exact full residual marginal is W127 = 2W226 + 9W018 + U127 = 2W226. A −2 gives the charge-two predecessor when shifting at its unique exceptional site, and either positive site of each cost-26 predecessor produces one image; a +2 gives the neutral cost-18 predecessor with nine lifts. These same-site translations preserve the seven residue, and the two nonisotropic shells on the surviving term have identical normalization. This is one marginal identity, never asserted angle-wise.

The [standalone verifier](high_rank_five_hit.py) uses the same ten auxiliary quadratic row indices as before and three mixed true-D quadratic rows (now h=0, (1,0,0,0), (0,1,0,0)); it combines them with that single marginal identity. The shifted atoms and their finite normalization are unchanged. Exact coefficient comparison gives
```
3(78 K123[-3] - 4 W339 + 74 M - 7 W014) - 3302
 = 178 K444[9] + 62 K333[12] + 117 K333[5] + 140 K335[12] + 76 K335[5]
   + 12 K222[8] + 766 K226[8] + 20 K232[8] + 64 K232[1] + 288 K121[4]
   + 240 K123[11] + 165 K125[11] + 174 K125[4] + 207 K125[-3]
   + 152 K127[11] + 283 K127[4] + 438 K127[-3]
   + 354 K014[7] + 105 K014[0] + 3 K028[-7].
```
All twenty terms are nonnegative. Average over eligible D **in this H**. Since each K123[-3]≥22, the incidence inequality demands G=4(W339−231−22M)+7W014−78(mean K123[-3]−22)≥0. But the identity shows G≤−4202/3−14(M−78)<0. No root/Fano bound or assumption that a negative residual class vanishes on every individual H is used.

Only ranks 40 and 42 are concluded from this argument.
