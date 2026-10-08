# The exact norm of the complex three-row permanent-determinant pencil

[Paper](paper.pdf) · [LaTeX](paper.tex) · [Upload source ZIP](paper-source.zip)

Author: Yongxian Zhang (张永贤); ORCID https://orcid.org/0009-0000-3864-3536.
School of Computer Science and Engineering, South China University of Technology.
Correspondence: mxymmxym1@gmail.com. No external funding. AI-assisted research.

## Complete principal formal scope

Exact best constant for every complex coefficient and every actual Mathlib 3-by-3 complex matrix, including zero rows. The coefficient lens is a corollary. The full equality classification and tensorization in the parent manuscript are outside this paper.

- `ComplexPencilFull.sharp_full_pencil_norm_iff`
- `ComplexPencilFull.matrix_squared_norm_iff`

[Complete native matrix proof and reproduction instructions](../../../notes/complex-permanent-determinant/formal/README.md).
Proof snapshot: `02af7db99db789fecb0d5f5f8f37b1a4e40762a0`. Lean 4.34.1; pinned Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The squared equivalence is fully kernel-checked; taking nonnegative square roots gives the displayed unsquared formula. This package has source compilation and standard-axiom audit evidence, not a claimed new empty-kernel replay.
The printed result includes all complex parameters and zero rows. The separately written equality classification is omitted.

Run `pdflatex -interaction=nonstopmode -halt-on-error paper.tex` twice. `check_full_norm.py` verifies the exact polynomial identities over rational interpolation grids, with the degree bounds supplied in the proof. The checker alone is not the matrix-norm proof.

Existing licenses and third-party notices remain in force; unlicensed original material remains all rights reserved. No external human peer review, acceptance or worldwide priority is asserted.
