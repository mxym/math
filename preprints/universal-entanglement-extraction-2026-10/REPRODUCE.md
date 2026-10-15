# Reproduce the submission package

The archive preserves repository-relative paths. Extract it into a new directory;
no existing working tree needs to be reset or cleaned. From the extracted root:

```bash
python3 preprints/universal-entanglement-extraction-2026-10/verify_package.py
python3 research/submission-protocol-depth-20261016/verify_sources.py
python3 research/submission-protocol-depth-20261016/check.py
python3 research/submission-protocol-depth-20261016/check_rank_polynomial.py
python3 research/submission-protocol-depth-20261016/check_pure_circuit.py
```

The diagnostic scripts use only the Python standard library. They check finite
identities and regressions; they are not proofs of all asymptotic theorems. They
write diagnostic reports (the rank/circuit scripts replace the extracted copies
of their recorded reports), so run them in the new extraction after the initial
integrity check; keep the distributed archive unchanged.

To rebuild the paper, use Python 3 and a TeX installation providing `pdflatex`,
Latin Modern, amsmath/amsthm, mathtools, mathrsfs, microtype, booktabs, array,
hyperref and bookmark, plus Poppler `pdfinfo` and `pdffonts`:

```bash
python3 preprints/universal-entanglement-extraction-2026-10/build_manuscript.py
```

The builder performs three passes and reports overfull boxes and unresolved
references. It fixes the timestamp. A different TeX distribution can still yield
a different PDF hash; the distributed PDF and literal TeX are independently
bound. Compilation is not mathematical proof verification.

Install Lean via elan. Both formal packages pin **Lean 4.34.1** and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; Lake manifests pin transitive
dependencies. Internet access is needed to obtain those external dependencies.
Their caches are not included in this archive. In each of the following package
directories, run the three commands:

```bash
lake exe cache get
python3 reproduce.py --check-only
python3 reproduce.py --fresh
```

1. `formalizations/spectral-extraction-core`
2. `formalizations/spectral-extraction-local-cap`

Run the packages sequentially in an isolated extracted tree: `--fresh` removes
and rebuilds only the checkout's own specified Lake output directories, including
imported repository packages. It does not alter sources or external caches. The
fresh build reuses pinned external dependency artifacts; it is not a source
recompilation of all Mathlib. Relevant proof closures are separately replayed in
an empty trust-zero kernel. The tests replace proof bodies while retaining the
original theorem types and require the kernel to reject those forgeries.

The new independent run records are under
`verification/universal-extraction-submission-20261016/independent-lean/`.
The first independent bootstrap timed out while fetching Mathlib; its actual
failure is preserved. After fixing dependency-cache links, both isolated fresh
builds and kernel audits passed. The two author's earlier successful runs remain
separate evidence in the original package directories.

The written review is independent internal AI review. It checks the bound
manuscript and its mathematical proof chain but is not an external human referee
report, exhaustive novelty certificate, or a new full-manuscript Lean audit.
