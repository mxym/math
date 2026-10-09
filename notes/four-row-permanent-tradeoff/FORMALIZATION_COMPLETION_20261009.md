# Lean completion supplement, 9 October 2026

The complete inequality **and every equality case** in Theorem 1 now have
an original-object Lean proof in
[the new standalone package](../../formalizations/four-row-complete-equality/README.md).
Its [proof correspondence](../../formalizations/four-row-complete-equality/FORMALIZATION_MAP.md)
and [detailed alternative equality argument](../../formalizations/four-row-complete-equality/PROOF_SUPPLEMENT.md)
explain how the logical gap from pairwise saturation to the full matrix
classification is discharged inside Lean.

The final theorem quantifies over actual complex 4x4 matrices and every real
c>=0. It includes zero rows and uses Mathlib's permanent and determinant and
the usual Euclidean row norms. The rank-one class is defined by actual
nonzero outer-product factors with equal column moduli; the monomial class
is defined by an actual column permutation and singleton row supports.
Neither class is defined by assuming the target equality.

The current run freshly compiled all 12 modules and replayed the complete
112-root closure of 15,593 declarations in an empty Lean kernel. Only
`propext`, `Classical.choice`, and `Quot.sound` occur as axioms. A separate
fresh Lake build also passed. The source and full logs, including two
rejected omitted-hypothesis/incorrect-weight controls, are published there.
The six v1 mathematical modules are retained byte-for-byte; 39 new theorems
in five new mathematical modules establish the equality classification.

This supplement updates the manuscript's **formalization coverage**, not its
mathematical statement or historical priority. The original frozen proof
package and its historical audit remain unchanged. The all-n rectangular,
quantitative-deficit, convex-power and tensorization statements remain
outside this new certificate. The old statement of whole-paper incompleteness
therefore remains correct; Theorem 1 itself is now completely formalized.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding; AI-assisted research.
Original new material: all rights reserved, subject to existing licenses and
third-party notices. Formal verification is not external peer review.
