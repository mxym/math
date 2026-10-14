# Sharp logarithmic APPT cutoff hierarchy and fixed-local entropy phases

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID0009-0000-3864-3536. No external funding. OpenAI AI assistants assisted.
Copyright2026 Yongxian Zhang; all rights reserved for original material.

[Complete ordinary proof](PAPER.md) · [Prepared obligations](THEOREM_MAP.md) ·
[Literature scope](LITERATURE.md) · [Internal complete read](MANUSCRIPT_REVIEW.json).

Fix any integer ℓ≥3 and put q_ℓ=(ℓ+1)/(ℓ−1). The sharp leading
coefficient of the dimension-only eventual APPT pole guarantee for the
class of actual bipartite pairs with both local dimensions at leastℓ is

    κ_ℓ=1/log[3(ℓ−1)/(ℓ+1)].

For **every c>κ_ℓ**, all sufficiently large D=mn, all ℓ≤m≤n and
**all real α≥c logD+1** have exact APPT and ASEP minimum Rényi entropy

    [α log(D+2)−log(3^α+D−1)]/(α−1),

with precisely the equality states (I+2vv*)/(D+2). The dimension threshold
depends only on fixed ℓ,c and is uniform over m,n,α. Actual ℓ⊗n APPT
projection states beat the pole at α=c logD for every0<c<κ_ℓ and all
large n. The necessity is along D=ℓn and is APPT-only; no competing ASEP
status or lower cutoff for every separate admissible D is asserted.

In particular κ_3=1/log(3/2) is sharp for the full nonqubit class.
The [previous explicit finite band](../appt-nonqubit-log-band-20261014/README.md)
α≥32logD+1 remains available for every D≥9. The present theorem sharpens
its leading coefficient asymptotically, with no explicit D0 or finite
critical-window formula. Fixed-ℓ coefficients decrease to1/log3; joint
growing-ℓ uniformity is not claimed. Qubit–qudit has the separately proved
linear cutoff scale.

There is also a complete **fixed-local APPT growing-order phase**. For
every fixed m≥3, n→∞ and α→∞ with α/logD→c in [0,∞],

    logD−min S_α→max{log[(m+1)/(m−1)],log3−1/c}.

At c=0 the second term is−∞; at c=∞ it is log3. Every such sequence,
including the critical c=κ_m, is covered. This is an APPT entropy-limit
theorem, without a subcritical ASEP phase or optimizer classification.

The proof uses genuine convex averages of APPT orbit points and actual
Schmidt partial-transpose tests. A finite number of exceptional eigenvalues
are separated from the bulk. The two-head test bounds their near-pole
squared deviations by a constant times the peak deficit, independently
of D. Continuous-order Taylor estimates and decreasing exponential bounds
then prove the complete eventual order band. Exact integer-rank projection
families give the lower bounds.

## Supporting verification

One standard-library checker evaluates18 physical cap controls,84 exact
two-head identity points and an actual3⊗3 negative PPT control with
expectation−1/108. The negative control passes the old linear outer and
second-eigenvalue bounds; it protects the additional physical input.
Separately,144 finite real-order band cases and60 fixed-local moment/phase
cases are evaluated at110 decimal digits. These are diagnostics; the
complete dimension/order statements are the ordinary written proofs.

```bash
python3 check_sharp.py --out DIAGNOSTICS_LOCAL.json
python3 check_sources.py
```

Windows ordinary/optimized and WSL runs passed using the same implementation,
with results compared in [the record](DIAGNOSTIC_COMPARISON.json). The
independent internal assistant read the complete240-line manuscript/map;
[its review](MANUSCRIPT_REVIEW.json) binds actual read ranges and source
bytes. Older249/471/558-line reads retain their old scopes. This remains
the same APPT direction, with no new major-conjecture count, complete Lean,
enlarged audit, external human peer review or verified historical priority.
[Source bindings](SOURCE_HASHES.json) record the packet. No new Release,
DOI, submission or external message is included.
