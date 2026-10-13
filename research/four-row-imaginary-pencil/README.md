# Complete sharp imaginary-axis four-row pencil norm

**Yongxian Zhang (张永贤)** · School of Computer Science and Engineering,
South China University of Technology · mxymmxym1@gmail.com ·
ORCID 0009-0000-3864-3536.

[Complete written proof](PAPER.md) · [Complete equality proof](EQUALITY.md) ·
[Theorem/verification map](THEOREM_MAP.md).

For **every actual complex 4×4 matrix A and every real t**, including zero rows,

    |per A+i t det A| ≤ max{3/2, |t|+1/√3} Π_i ||A_(i,*)||₂.

The constant is attained and exact for every t. The flat branch ends at
`|t|=3/2−1/√3`. Both sharp witnesses are explicit. This completes the whole
**purely imaginary coefficient axis**, including the complete equality
classification. With four nonzero rows: below the transition only flat
rank-one matrices attain equality; at the transition they coexist with
oriented Fourier3 direct sums; above it only the latter class occurs. The
Fourier class has `per A / det A = i sign(t)/sqrt(3)` after any row scalings.
Coefficients with both nonzero real and imaginary parts remain unclassified.

The new boundary argument is an exact 256×256 matrix identity over Q(√3,i).
Seven positive Gram factors, their exact LDL factorizations, explicit partial
transpose subsets and 288 norm-preserving group actions prove the inequality
on the original product row tensors. Scalar convexity and the elementary
determinant bound extend it to all real t. No unitary-optimizer assumption,
finite parameter grid or numerical solver output is a proof premise.

## Reproduction

```bash
python3 check_certificate.py --negative-controls
python3 check_equality_structure.py
```

Python 3.10+ and its standard library suffice. The checker uses rational
arithmetic only; it verifies all 65,536 entries of the boundary identity by
explicitly averaging all 288 group elements, and checks all seven positive
factorizations of sizes 5,3,13,6,11,21,7. It rejects a corrupted Gram coefficient,
a negative factor and the wrong boundary coefficient. Every scalar in the JSON
has an unambiguous exact rational/algebraic interpretation. The equality
checker additionally verifies the actual first Gram difference matrix, all
65,536 zero-support masks and the exact three-row determinant and Fourier
singular-value identities used in the universal analytic equality proof.

Fresh Windows and WSL records are in `verification/`; those are two runs of
the **same** checker, not independent implementations or external peer review.
`SOURCE_HASHES.json` binds the final paper, checker, exact data and records.
This package is a **complete written mathematical proof with exact algebraic
certificates, not a complete Lean formalization**. No Lean build or kernel
replay is claimed for it. Earlier frozen four-row papers and Lean packages
remain unchanged.

The permanent-only endpoint and determinant estimate are classical; the paper
credits Carlen–Lieb–Loss and proves the needed n=4 endpoints directly. The
earlier three-row Fourier witness is credited as motivation. Targeted literature
screening does not certify first historical solution. No external funding,
human refereeing, experiments, Release or DOI is asserted for this new manuscript.
OpenAI AI assistants assisted research and writing. Copyright 2026 Yongxian
Zhang; all rights reserved for original material and existing third-party rights
remain unchanged.
