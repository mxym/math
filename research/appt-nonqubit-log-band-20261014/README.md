# Nonqubit APPT pole optimization at logarithmic order

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536. No external funding. OpenAI AI assistants assisted.
Copyright 2026 Yongxian Zhang; all rights reserved for original material.

[Complete ordinary proof](PAPER.md) · [Prepared theorem map](THEOREM_MAP.md) ·
[Primary literature and input scope](LITERATURE.md) ·
[Independent internal read](MANUSCRIPT_REVIEW.json).

For **every actual 3≤m≤n, D=mn≥9, and real α≥32log D+1**, the minimum
Rényi entropy over the all-global-unitary APPT set and over the absolutely
separable (ASEP) set is exactly

    [α log(D+2)−log(3^α+D−1)]/(α−1).

All equality states are precisely (I+2vv*)/(D+2), for arbitrary unit v.
The constant32 is sufficient and is not asserted optimal. The proof covers
the continuous order band, including arbitrarily small distances from the
maximum eigenvalue. A necessary second-eigenvalue gap comes from a genuine
convex average of APPT orbit points and an explicit rational3⊗3 PPT witness.
Trace and the three-smallest-eigenvalue constraint then bound every tail
deviation and its variance; the near-cap and far-cap power comparisons
are strict on their full stated ranges.

The dimension-only eventual **APPT** pole cutoff in this class has order
Θ(log D). Actual3⊗n states (I+P)/(D+rankP), with rankP=floor(D/α), beat
the pole at α=c log D for every fixed0<c<1/log(3/2) and all sufficiently
large n. Their APPT property holds for every global unitary by a complete
Schmidt negative-trace estimate. Their ASEP status is not claimed: this
does not prove a matching ASEP cutoff lower bound.
The upper bound is uniform over all nonqubit pairs; the necessary scale
is witnessed along3⊗n and does not assert a lower cutoff for every D or
every fixed local-dimension partition.

Together with the [exact qubit cutoff](../appt-log-order-phase-20261014/SHARP_POLE_PHASE.md),
this gives different scales for actual APPT spectra: Θ(D) for qubit–qudit
and Θ(log D) uniformly for the class with both local dimensions at least3.
The logarithmic theorem cannot be applied to qubits. An actual2⊗2048
APPT rank-two competitor at α=300, above32log4096+1, has moment ratio
strictly greater than105/82 relative to the pole. This exact control
protects the local-dimension hypothesis.

This is a complete ordinary proof in the stated band and another result
in the same APPT direction. No exact subcritical minimum, sharp logarithmic
coefficient, general APPT=ASEP theorem, additional major-conjecture solution,
complete Lean, historical-first certification or external human peer-review
status is asserted. Known rank-two constraints, maximum eigenvalue and
white-noise separability endpoint remain credited inputs.

## Supporting checks

The standard-library checker verifies10 displayed exact scalar certificates,
8 actual second-eigenvalue PPT controls and the finite qubit restriction
control. It separately evaluates40 real-order scalar cases,504 spectra in
the necessary relaxation and20 actual3⊗n lower-scale moment formulas at
210 decimal digits. Relaxation spectra are not asserted APPT; finite
diagnostics are not universal proofs.

```bash
python3 check_nonqubit.py --out DIAGNOSTICS_LOCAL.json
python3 check_sources.py
```

Windows ordinary/optimized and WSL runs passed with one shared implementation;
their correspondence is recorded in [the comparison](DIAGNOSTIC_COMPARISON.json).
The [internal review](MANUSCRIPT_REVIEW.json) records the complete249-line
manuscript/map read and the exact final source bytes. This is assistant
review. [Source bindings](SOURCE_HASHES.json) preserve the packet and disclosed
inputs. Older Lean sources, builds, audit roots and kernel coverage are
unchanged. No new Release, DOI, submission or external message is included.
