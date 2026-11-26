# Match the deletion budget, or turn it into structure

This is an executable prototype of a proof rule, not a general solver, originality claim, or theorem release. The rule abstracts a step used in the [unrestricted three-uniform internal sunflower proof](../../research/euclidean-tensor-geometry/InternalSunflowersTriplesUnrestricted.md).

**Input.** Each owner has a list of weighted buckets, each indexed by a color. A color is sampled globally with marginal probability \(p\); the same sampled color can activate buckets at many owners. After any number of deletions, an owner may be removed permanently when fewer than \(m\) of its colors remain. We want a loss budget that does not depend on the order of future deletions.

**The new move.** Use original weights, not the distribution after earlier repairs. Write \(E\) for total original weight and \(H_K\) for the sum of the \(K\) largest original bucket weights at each owner. In every sample, the total charged at any owner deleted once under this rule is bounded by its \(m\) largest sampled original buckets. The contribution from the deterministic top \(K\) has expectation at most \(pH_K\); each remaining bucket weighs at most that owner's total weight divided by \(K\). Thus the expected total charge is at most
\[
p H_K+(m/K)E.
\]
No independence across owners or across buckets of the same color is needed for this inequality. Non-increasing supports and charging each owner at most once are essential.

For \(K=\lceil 2m/(p\epsilon)\rceil\), either \(H_K\le\epsilon E/2\), which certifies expected adaptive loss at most \(\epsilon pE\), or keeping only those top \(K\) buckets retains more than \(\epsilon E/2\) and produces a bounded-support host. The second branch is not a failed estimate: it supplies a new structural hypothesis. In the sunflower proof bounded-support sides can then be locked to one sampled color and removed from the list of adaptive deletion constraints; the proof checks all domain-specific pair and witness costs separately.

## Run and falsify it

Inputs are `buckets` of [owner string, color string, positive integer or rational string], plus \(m\), \(p\), and \(\epsilon\). The command `plan` gives exact rational bounds and returns the actual restricted host when appropriate. `materialize` acts on a concrete weighted matrix (owner = row, color = column). In the diffuse branch it keeps **exactly** \(p\) times the number of columns, then discards rows with fewer than \(m\) surviving columns. It chooses the fixed-size sample by conditional expectation, evaluating the remaining hypergeometric tails exactly. This needs integral sample size and is bounded to small instances. The certificate-only branch has no such restriction.

```sh
python3 soft_core.py materialize diffuse.json > cert.json
python3 soft_core.py verify diffuse.json cert.json
python3 soft_core.py materialize concentrated.json
python3 -m unittest -v
```

The diffuse example keeps 18 of 24 columns and retains mass 36 after cleanup. The concentrated example retains mass 115 while imposing at most 16 colors per row. Tests compare exact expectations with exhaustive enumeration, check a shared-color example, and test the adaptive charge inequality against every substate of a sample. The weighted-matrix cleanup demonstration is a second setting, not a claim that this one primitive solves arbitrary matrix problems.

**Boundary.** This rule bounds only the named cleanup cost. It does not certify conflict removal, adequate final witnesses, or that repeated structural restrictions preserve other hypotheses. If deletions redistribute weight or a deleted owner can return, the proof does not apply as stated. Broad usefulness remains a research question; a second substantive theorem, not a second toy demo, would be evidence.
