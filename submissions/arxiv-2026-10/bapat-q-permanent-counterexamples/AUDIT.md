# Manuscript revision and reproducibility audit

**PASS for the stated scope.** Revised manuscript: 14 pages, Yongxian Zhang.
Primary AI assistant review, without subagents or external human referees.

## Mathematical and editorial scope

The two main conclusions retain the original fixed-row inversion-weighted
q-permanent on [-1,1]. The complex theorem specifies all 200 rows, the
positive-definite rational perturbation, q0 and its strict gap. The real
theorem establishes a finite integer symmetric positive-definite matrix and
two rational interior parameters, without extracting its entries or order.

The revised introduction explains that 200 is the certified witness order,
not a minimal dimension. Exact checking, rather than discovery optimization,
is the proof of that witness. The real limiting argument chooses a finite
base size m first and a finite repetition count L second; its Gram order is
N=(m+4)L. Rational approximation, positive diagonal perturbation and integer
scaling preserve a strict inequality. No effective convergence threshold or
numerical dimension is inferred from the complex certificate.

A new written corollary appends identity blocks to obtain a specified complex
counterexample for every N>=200 and clears denominators by positive integer
scaling. Block preservation, inversion counts and homogeneous scaling are
proved in the text. It is an elementary consequence, not a newly replayed
Lean all-N theorem. No minimum order, real rank-two final matrix or entrywise
positivity is claimed.

## Fixed Lean evidence

- `BapatExplicit.explicit_rational_counterexample`, fixed source
  `6aa1adcc7897635b4ab2c82b0ae22c23106f91e6`: 30 roots with a
  22,812-declaration dependency closure; later finite-input continuation
  covers 928 owned declarations and its separate 22,371-declaration closure.
- `BapatRealExistence.exists_integer_real_symmetric_counterexample`, fixed
  source `6ff60a4bad0bd78925f29faf8e3b252aa8b3e455`: 67 modules, 776
  owned declarations and 54,739 transitive dependencies in the recorded
  empty-kernel replay.

The earlier successful kernel executions supply this evidence. This revision
**did not rerun Lean**. `qa/SOURCE_AUDIT.json` retains the prior checksum and
source-signature audit; its 242-file check is not relabeled as a fresh check
in this editorial round. The only permitted logical axioms in the fixed
records are `propext`, `Classical.choice` and `Quot.sound`. Earlier timeouts
remain distinct from later successful runs. The real proof's nonconstructive
choice does not extract a numerical witness.

## Fresh checks in this revision

The distributed source ZIP was independently extracted and compiled three
times with shell escape disabled. Source, ZIP and PDF hashes are recorded
in [qa/BUILD_REPORT.json](qa/BUILD_REPORT.json). All 200 table entries match
the public CSV. References and bibliography keys resolve, every font is
embedded, no Type 3 bitmap font is used, and final warning diagnostics pass.

The two different exact integer algorithms were rerun successfully, including
all 19,900 pair deletions. Both reject optimized Python execution and a false
rank-one input. These establish the finite complex certificate, not the real
analytic limit. Their execution outputs and controls are in `qa/`.

All 14 pages were rendered at 85 dpi. Contact sheets were inspected for
formula width, clipping, overlap, table continuation and bibliography flow.
An initially isolated writing-declaration page and a spilled final bibliography
entry were repaired by normal flow and bibliography spacing. No shrinking
of the mathematical proof or witness table was needed. Final rendering and
contact-sheet hashes are in [qa/VISUAL_RECORD.json](qa/VISUAL_RECORD.json).
This is layout inspection, not a character-by-character formula proof audit.

Original Bapat DOI metadata identifies its title as *Research problem*;
the descriptive problem phrase is now distinguished from that catalog title.
The paper retains Mitchell, Bapat–Lal and Lal and distinguishes Bapat–Sunder.
Selected fresh Crossref lookups and the Mitchell rate-limit are recorded in
[the whole-collection audit](../../../reviews/manuscript-quality-2026-10-08/README.md).
The earlier source-access screen remains in `RELATED_WORK_AUDIT.md`; this
round does not assert newly obtained full text of all historical sources or
exhaustive novelty verification.

Funding and AI research methods are disclosed separately from the AI writing
declaration. Author metadata agrees with the confirmed profile. The source
ZIP includes no private paths, preview PDF, credentials or Lean build debris.

## Reproduction

From the repository root:

```sh
python3 -B submissions/arxiv-2026-10/build_bapat.py --output /tmp/bapat-fresh
python3 -B submissions/arxiv-2026-10/bapat-q-permanent-counterexamples/check_package.py
```

The output directory for the builder must not already exist. Follow the
fixed Lean packages' own commands for a new kernel replay. Platform LaTeX
versions may change page breaks; inspect the platform's generated preview
when submitting. This audit is not journal acceptance, external professional
review, or a historical-priority certification.
