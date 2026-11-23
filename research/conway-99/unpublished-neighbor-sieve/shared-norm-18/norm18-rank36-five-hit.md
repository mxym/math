# A five-type must-hit at Seidel rank 36

At rank 36 at least one of the five selected signed-unit graph types
```
(0,16), (0,20), (0,24), (2,28), (3,37)
```
must occur. Equivalently the selected support cannot be contained in the complementary seven types. In particular the former four-type scalar control `{018,026,125,230}` does not extend to an actual graph. This is not a rank-36 or Conway-graph nonexistence result.

Assume these five types absent. The neutral norms 16, 20, and 24 are always signed units; absence is of the full graph populations. Use the [rank-36 native chart](rank36_four_hit_sets.py), in which `2402 D[0,18]` counts the actual **oriented** graph norm-18 fields N. The eight nonnegative rows in the [integer identity verifier](norm18_rank36_five_hit.py) are three raw shell counts, the scalar abundances `Y1` and `Y3` (already normalized as nonnegative in the native chart), its original-compatible coclique moment row `('Ct',34)`, its graph overlap row `('G',15000)`, and its conditional Fano bound `no20/24` (applicable by the two absent neutral shells). The latter is 112 minus the graph-wide N14. No rank-42 identities or recently tightened rank-36 Fano bound are used.

In exact rational coordinates the verifier checks that
```
8,429,899,495 N − 104,248,536,974,733
```
equals a strictly positive integer combination of those eight rows, plus a linear combination of the twelve selected unit-count rows. Only `016`, `228` and `337` have negative coefficients in this last combination, and these are absent; in particular the `121`, `127` and `226` rows are retained with positive coefficients, not set to zero. Thus N>12,366, or N≥12,368 since both orientations are counted.

On the other hand the [triangle-free graph at each four-parent norm-18 seed](norm18-triple-remaining-bridges.md#unconditional-capacity-and-scalar-pressure) gives 9N≤110,880 when N16=N20=0, that is, N≤12,320. Both bounds apply to the very same graph count without orbit, residue or orientation factors. This contradiction proves the stated hit.
