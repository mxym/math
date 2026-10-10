# APPT purity in arbitrary local dimensions: rigorous spectral reductions

**Research continuation; not a solution of the full arbitrary-dimension purity
conjecture, and not a new Lean release.** The previous qutrit theorem is complete
and published separately. This directory records new analytic proofs and exact
algebra checks for the next problem.

The target is the arbitrary-dimension maximal-purity conjecture of Ahiable,
Kothakonda and Winter, arXiv:2608.03390v1, Conjecture 6.7. Set

\[
D=mn,\qquad t=\left\lceil\frac{(m-1)n}{2}\right\rceil,\qquad
M_{m,n}=\max\left\{\frac{D+8}{(D+2)^2},
\frac{D(m-1)^2+4mt}{[D(m-1)+2t]^2}\right\}.
\]

## Proved here

For every pair of integers **3 <= m <= n**:

1. The maximum purity over all actual APPT density matrices with **at most two
   distinct eigenvalues** is exactly `M_{m,n}`. The proof covers every possible
   multiplicity, including zero eigenvalues. Among these spectra, only the
   rank-one spike and the balanced two-level family can attain the maximum;
   the appropriate family is selected by the displayed maximum.
2. Every APPT state whose least eigenvalue has multiplicity at least `D-m+1`
   has purity at most `(D+8)/(D+2)^2`. This permits more than two distinct
   eigenvalues; equality requires the rank-one-spike spectrum.
3. In every dimension **2 <= m <= n**, the entire Gershgorin inner polytope
   from the same paper consists of **absolutely separable** spectra. This is a
   consequence of its vertex structure, an explicit pure-state white-noise
   decomposition, the Gurvits--Barnum separable ball, and the spectral-ratio
   criterion of Kondra et al., arXiv:2605.29197v1, Supplemental Lemma 2.
   The external separability criteria are stated explicitly; they are not
   replaced by finite tests or claimed as new results.

Complete arguments are in [PROOF.md](PROOF.md). These are written mathematical
proofs, **not Lean-formalized proofs**. The exact checker verifies supporting
polynomial identities, the sign certificate, discrete endpoint arithmetic,
phase-character identities, and a deliberate corrupted-certificate rejection.
It does not certify the quantum arguments or the full conjecture by itself.

## What is not proved

No proof is given that a global APPT purity maximizer in dimensions `m >= 4`
has at most two distinct eigenvalues. That would be an essential additional
reduction, not something implied by convexity. The state-level equality
`APPT = absolutely separable` is also not established.

Any counterexample to the conjectured purity upper bound must now have at
least three eigenvalues and least-eigenvalue multiplicity at most `D-m`.
Uniform-Schmidt-rank necessary inequalities alone cannot close this gap:
Section 7 supplies the exact non-APPT relaxation witness
`(3,2,1,...,1)/(D+3)` and its negative quadratic-form certificate.

The next target remains the **unrestricted** arbitrary-dimension problem,
not more finite numerical examples. The immediate unresolved cases are
multi-level outer spectra, beginning with `m=4`. See
[RESEARCH_LOG.md](RESEARCH_LOG.md) for candidate selection, limitations of
numerical searches, and criteria for reassessing the direction.

## Reproduce the auxiliary exact checks

Only Python's standard library is required:

```sh
python3 check.py --report verification/exact-checks.json
python3 check.py --self-test
```

The symbolic checks are identities for indeterminates. The finite enumeration
is an additional regression test, not a proof for unbounded dimensions.
`SOURCE_HASHES.json` pins the research sources. The original qutrit proof and
preprint releases are not modified by this work.

## Publication and attribution

The completed qutrit proof is in `formalizations/appt-qutrit-purity/`, immutable
release `appt-qutrit-purity-complete-v1`. Its preprint is publicly archived at
DOI **10.5281/zenodo.23269470**, with immutable GitHub manuscript release
`appt-qutrit-purity-preprint-v1`. These existing publications do not yet contain
the new arbitrary-dimension results in this directory. No arXiv posting,
peer review, or historical priority is asserted for this continuation.

The formula and the two candidate spectra are those of Ahiable--Kothakonda--
Winter; the new work here is the upper-bound argument on the stated classes
and the containment deduction. Literature checks did not establish a prior
arbitrary-dimension two-eigenvalue purity proof, but they are not an exhaustive
priority certification. Work was carried out with AI assistance and is recorded
for independent mathematical review before any additional preprint submission.
