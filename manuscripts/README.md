# Complete research manuscripts

This directory consolidates four research lines into five readable papers.
It adds complete proof chains, precise formalization boundaries, reproducible
builds and current verification records. It does not count repackaged results
as additional independent research breakthroughs or issue new preprint numbers.
The historical proof packages and their seals remain unchanged.

| Paper | Main established result | Proof coverage |
| --- | --- | --- |
| [Sharp simplex stability](sharp-simplex-stability/README.md) | Every prescribed maximum simplex; sharp exponent `1/(d-1)`; coefficient at most `4096 d^2`; exact truncation obstruction | Complete written proof; full Lean of the earlier upper bound and truncation obstruction, not the improved coefficient |
| [Continuum power avoidance](continuum-power-avoidance/README.md) | One large closed periodic set for each prescribed countable bounded-log-gap family, avoiding all nonzero power germs with power-controlled remainders | Complete written proof and full Lean of the main endpoint |
| [Fractional cover spectrum](fractional-cover-spectrum/README.md) | Entire finite-ratio limiting frontier, integer-boundary near-design characterization, fixed and diverging matching spectrum | Complete written proof, classical design/cover inputs, partial Lean |
| [Permanent--determinant norms](complex-permanent-pencil/README.md) | Exact complex three-row pencil; sharp four-row tradeoff and real pencil; equality, deficits and exact tensor amplification | Complete Hermitian and Laplace proofs with exact identities |
| [Orbital atom stability](orbital-atom-stability/README.md) | Universal finite-action duality; all-degree two-subset law; three-subset classification through 120 and sharp `18/n` asymptotic; all-rank transfer and four-subset degrees 11--50 | Complete analytic proofs and exhaustive rational certificates in the stated finite ranges |

These are AI-assisted manuscripts. Proof inspection, formal verification and
arithmetic checking have different scopes, documented in [REVIEW.md](REVIEW.md)
and [the verification guide](../verification/finalization/README.md). No external
human referee review or literature-wide priority certification is asserted.
PDFs and editable sources are supplied for circulation; journal submission,
authorship metadata and independent human peer review have not been performed.

## Reproduce

From the repository root, with Python 3:

```sh
python3 -B manuscripts/assemble.py
python3 -B verification/finalization/replay_finite.py --output /tmp/new-finite-run
python3 -B verification/finalization/check_replay_guards.py
python3 -B manuscripts/build.py --output /tmp/new-pdf-run
```

Output directories must be new. The symbolic asymptotic replay requires SymPy
1.14 or a compatible version; other checkers use Python's standard library.
The PDF builder needs pandoc, a working TeX
Live installation, `pdflatex`, `pdfinfo` and `pdftotext`. It builds in a temporary
directory with shell escape disabled. It can bootstrap a missing pdfLaTeX
format from the installed TeX Live sources without changing the system.

Lean instructions, exact pins and target names are in the individual guides.
Use Lean **4.34.1**, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Do not run `lake update` to
substitute newer dependencies for the published lockfiles.

[SOURCE_PINS.json](SOURCE_PINS.json) binds all historical proof/checker inputs
to the integration snapshot recorded there. Work began at
`636541e97501f50c187f49eb7a19245965d5502e` and incorporated related parallel
updates through `bddf3ac` before the manuscript scope was frozen.
[SOURCES.md](SOURCES.md) explains the assembly and editorial changes.
[PRIOR_WORK.md](PRIOR_WORK.md) gives the limited literature comparison.
The new manuscript files have a separate integrity inventory; neither inventory
is mathematical evidence by itself.

If parallel work changes an ancestor path later, the historical input reader
retrieves its exact SHA-checked blob from the recorded commit using local Git.
It never accepts the changed file as the older proof. A source zip without Git
must contain the pinned ancestor inputs; otherwise use a full Git checkout.

Open-question descriptions in these papers belong to the frozen integration
snapshot. Subsequent parallel work has already added an all-fixed-rank
Chebyshev theorem and further even-row transfers to the parent notes. Those
later claims are preserved in their original packages and are outside this
five-paper proof audit; the older conjecture wording is not a statement of
their current repository status.
