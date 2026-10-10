# Global-unitary entanglement extraction: capacity and exact PPT fidelity exponent

**Complete written analytic argument for the explicitly stated two-stage task. Not Lean-formalized, not externally peer reviewed, and not a solution of ordinary mixed-state LOCC distillation.**

Given an arbitrary state on $\mathbb C^m\otimes\mathbb C^n$, first allow a global unitary on its k-copy system, without ancillas before that unitary; then allow local channels, LOCC, or a completely PPT channel to extract a maximally entangled target. The output fidelity is the overlap with its normalized target projector, not the square root of that overlap.

For every fixed $2\le m\le n$ and every spectrum $p$, including zeros, the three capacities coincide:

\[
 C_{\mathrm{LO}}=C_{\mathrm{LOCC}}=C_{\mathrm{cPPT}}
 =\min\{\log m,\tfrac12[\log(mn)-H(p)]\}.
\]

The [complete proof](PROOF.md) also determines the exact cPPT target-fidelity exponent at **every** target rate $R\ge0$. With $A=\log m$, $L=\log(mn)$ and $c_R=L-2\min(R,A)$,

\[
 \mathcal E(R)=(R-A)_++\max_{1\le\alpha\le2}
 \frac{\alpha-1}{\alpha}(S_\alpha(p)-c_R).
\]

The value at alpha=1 is zero. Above capacity the fidelity vanishes exponentially. For LO/LOCC the capacity is exact and this is a converse exponent, but a matching LOCC exponent is **not** claimed. The cPPT condition means complete positivity of both the channel and its partial-transpose conjugate, not merely preservation of the set of PPT states.

## Relation to the preceding negativity theorem

In balanced dimensions the faithful extraction capacity is `log d - H(p)/2`, while the earlier optimal logarithmic-negativity growth rate is `log d - S_2(p)/2`. They are strictly different whenever the positive eigenvalues are unequal. Thus the previous negativity rate is not misrepresented as a local distillation yield. At target rates at least log m, the new exact cPPT fidelity exponent is R minus that negativity rate.

The work extends the companion Bell-projection mechanism, and explicitly credits the older Rains SDP and Tropp concentration inequality. Lami's recent quadratic converse already yields the half-entropy-deficit bound with a maximally mixed auxiliary state; that prior converse is credited, not claimed as new. Here a direct finite-block derivation is matched by local achievability and the exact spectrum-optimized cPPT exponent. The finite one-shot fidelity is approximated within logarithmic factors by a weighted spectral-prefix envelope. Exact type and escort arguments determine the asymptotic exponent; pure-subspace packing proves capacity achievability by local product channels after the global unitary.

Read the [signed analytic manuscript](main.pdf) or its [standalone LaTeX source](main.tex). The proof and external-input boundary are also readable in `PROOF.md`.

## Checks and reproduction

```sh
python3 check.py --report verification/exact-checks.json
python3 -O test_checker.py --report verification/source-mutations.json
```

Source integrity is checked by `python3 verify_sources.py`. The manuscript can be rebuilt with `python3 build_manuscript.py` using Pandoc and pdfLaTeX; `main.tex` also compiles directly with two pdfLaTeX passes.

Only Python's standard library is required for the checks. The checks include full rational Choi matrices of six channels and their partial-transpose conjugates, local Kraus completeness with nondivisible dimensions, deterministic extraction of eleven Bell-coded states across five systems, symbolic escort identities, and the inherited exact cyclotomic Bell/type checks. Five mutated source programs are rejected with specific mathematical diagnostics, and positive checks also run with assertions disabled.

These calculations are finite ancillary checks, **not proof of the unrestricted analytic theorem**. No new Lean certification is claimed. External inputs and novelty limits are detailed in `RESEARCH_LOG.md`; all mathematical steps for the new task are written in `PROOF.md`.

The old immutable qutrit proof/preprint and the companion negativity preprint are not modified. Finite-copy APPT purity, APPT=AS, exact LOCC fidelity exponents, efficient implementations, and optimal below-capacity error exponents remain separate unresolved questions in this work.
