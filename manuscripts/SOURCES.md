# Source and editorial map

Initial snapshot: `636541e97501f50c187f49eb7a19245965d5502e` of
`https://github.com/mxym/math`. Every included historical file is listed with
SHA-256 in [SOURCE_PINS.json](SOURCE_PINS.json). The source papers remain the
research record of when each theorem was established; this consolidation does
not restart their disclosure dates or imply new priority.

Related parallel work was incorporated through commit `bddf3ac` during
finalization. The full integration commit is in SOURCE_PINS.json. New unrelated
packages retain their separate original publications. The three-subset
extension, sharp asymptotic, all-rank transfer and four-row permanent results
are credited as parallel antecedents, not discoveries of this finalization task.

| New manuscript | Historical proof sources | Editorial work |
| --- | --- | --- |
| Sharp simplex | `notes/quadratic-dimensional-simplex-stability`, `notes/simplex-truncation-stability`, the two full simplex Lean releases | A continuous proof from the invariant definition through weighted anchors, intrinsic projection conversion, every-maximum retention and sharpness; direct facet derivation of the cone normalization; elementary proof of the `4096 d^2` coefficient; complete truncation appendix |
| Continuum avoidance | `notes/continuum-power-avoidance-unified`, geometric and remainder formalizations | Full traditional proof and correspondence retained; correct public project locations; current reproducible formal-evidence description; breakable declaration identifiers |
| Fractional spectrum | `notes/sharp-fractional-cover-frontier`, `notes/fractional-design-stability`, `notes/fractional-matching-spectrum` | All three full proofs in one paper; namespaced theorem/equation references; unified hypotheses and classical-input map |
| Permanent norms | `notes/complex-permanent-determinant/PAPER.md`, `notes/four-row-permanent-tradeoff/PAPER.md` and their checkers | Full three-row pencil and four-row tradeoff proofs retained; distinct coefficient and parity-law scopes; links repaired |
| Orbital atom stability | Sections 15--23 of `notes/sharp-robust-permanent/paper.md`, `notes/johnson-short-cycle-spectrum/README.md`, fixed JSON and checkers | Latest proven extensions combined; complete four-subset table through 50; missing Section 8 references removed; equation tags repaired |

`assemble.py` checks historical pins before generating the four derivative
papers and the simplex truncation appendix. It does not generate the newly
edited main simplex proof. It does not refresh trusted hashes. The derivative
sources, PDFs, documentation and verification tools are individually included
in the new manuscript inventory.

`historical.py` checks current bytes first. When an ancestor has evolved, it
reads the exact blob at the recorded integration commit and checks the same
published SHA-256. Finite replays materialize only those pinned inputs in their
temporary packages, so later added files cannot alter a sealed inventory.
This preserves reproduction without freezing unrelated parallel development.

Two reproduction repairs are deliberately outside the sealed packages:

1. `verification/finalization/replay_continuum.py` repairs Lean `import all`
   parsing on a cache miss. The original verifier is pinned; all of its source,
   toolchain, ownership, axioms and kernel checks remain active.
2. `verification/finalization/strict_checker.py` explicitly compiles historical
   checkers with `optimize=0`. Their assertions remain proof obligations even
   under an optimized launcher. An isolated unoptimized child also preserves
   assertions in imported helpers. False entrypoint/imported assertions and a
   corrupted rational primal--dual objective are rejected by negative controls.

Assembly is editorial consolidation. The substantive mathematical claims are
attributed to their original research packages. The latest finite three-subset
classification incorporates parallel work through degree 120; it is not claimed
as work newly discovered during this finalization.
