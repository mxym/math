# Global-unitary entanglement extraction: capacity and exact strong-converse exponents

**Complete written analytic argument for the explicitly stated two-stage task. Not Lean-formalized, not externally peer reviewed, and not a solution of ordinary mixed-state LOCC distillation.**

Given any state on $\mathbb C^m\otimes\mathbb C^n$, first allow a global unitary on its existing k-copy space, with no additional ancilla before that unitary. Then allow deterministic local product channels (LO), LOCC, or completely PPT channels. The output fidelity is the overlap with the normalized maximally entangled target projector, not its square root.

For every fixed $2\le m\le n$ and every spectrum $p$, including zeros, all three extraction capacities coincide:

\[
 C_{\mathrm{LO}}=C_{\mathrm{LOCC}}=C_{\mathrm{cPPT}}
 =\min\{\log m,\tfrac12[\log(mn)-H(p)]\}.
\]

The [complete proof](PROOF.md) also determines the exact target-fidelity exponent at every rate $R\ge0$, **for all three operation classes**. With $A=\log m$, $L=\log(mn)$ and $c_R=L-2\min(R,A)$,

\[
 \mathcal E(R)=(R-A)_++\max_{1\le\alpha\le2}
 \frac{\alpha-1}{\alpha}(S_\alpha(p)-c_R).
\]

The value at alpha=1 is zero. Below capacity deterministic local product channels attain fidelity tending to one; above capacity even completely PPT fidelity vanishes exponentially. LO, LOCC and cPPT have the **same entire strong-converse exponent**, not just the same capacity. The initial global unitary is an explicit resource and cannot be omitted from this statement.

## Deterministic one-shot construction

For ordered spectrum lambda on a times b dimensions, let N=ab, let L_r be its largest-r eigenvalue sum, and set

\[
 T_K=\max_r\min\{1,a/K,\sqrt{N/r}/K\}L_r.
\]

The finite-dimensional theorem is

\[
 T_K/4\le f^{\mathrm{LO}}\le f^{\mathrm{LOCC}}\le f^{\mathrm{cPPT}}\le H_NT_K.
\]

Its lower bound is deterministic. Choose a Bell dimension d about half of `min(a,K,sqrt(N/r))`; at least r orthogonal Bell-coded vectors fit in product garbage-coordinate blocks. A global unitary puts the r largest eigenvalues on them. Local Kraus maps discard the labels and map each good vector to the same embedded d-dimensional maximally entangled state, whose target-K overlap is d/K. All leftover coordinates have explicit Kraus branches; there is no postselection.

The upper bound uses the Rains fidelity effect M: `0<=M<=I`, `-I/K<=M^Gamma<=I/K`, so `Tr M^2<=N/K^2` and `||M||<=min(1,a/K)`. The construction matches that spectral envelope within logarithmic factors. Spectral types and an exact escort calculation then prove the full exponent. **No matrix concentration theorem or random projector is needed for this strengthened argument.**

## Relation to earlier work

In balanced dimensions the faithful capacity is `log d - H(p)/2`, while the preceding logarithmic-negativity rate is `log d - S_2(p)/2`. They differ strictly when the positive eigenvalues are unequal. Thus the negativity rate is not mislabeled as a faithful extraction yield. For target rates at least log m, the new common fidelity exponent equals R minus that negativity rate.

The Rains SDP is credited and its elementary proof is included. Lami's recent quadratic converse already yields the half-entropy-deficit upper bound by choosing a maximally mixed auxiliary state; that prior converse is **not** claimed as new. The addition here is the matching spectrum-optimized local achievability and the exact all-rate common exponent. The fixed-input distillation problems in that literature are distinct.

Read the [signed manuscript](main.pdf) or its [standalone LaTeX](main.tex). The proof and literature boundary are also readable in `PROOF.md` and `RESEARCH_LOG.md`.

## Reproduce ancillary checks

```sh
python3 verify_sources.py
python3 check.py --report verification/exact-checks.json
python3 -O test_checker.py --report verification/source-mutations.json
```

Only Python's standard library is required for the checks. They cover six full rational Choi/PPT-Choi matrices, deterministic local extraction of 25 Bell-coded inputs in eight systems, exact integer packing cases including nondivisible dimensions, three symbolic escort identities, and inherited exact type counts. Seven mutated checker programs must fail with specific mathematical diagnostics; unchanged programs must pass normally and with assertions disabled. These are ancillary finite checks, **not certification of the unbounded analytic proof**.

Rebuild the manuscript with `python3 build_manuscript.py` using Pandoc and pdfLaTeX, or compile `main.tex` directly twice. `SOURCE_HASHES.json` binds the exact proof, manuscript, and testing sources.

The old immutable qutrit proof/preprint and companion negativity preprint are unchanged. Standard fixed-input LOCC distillation, the optimal below-capacity error exponent, finite-copy APPT purity, APPT=AS, and efficient global implementations remain separate questions. No arXiv submission, DOI, exhaustive priority certification, or new complete-Lean Release is asserted for this work.
