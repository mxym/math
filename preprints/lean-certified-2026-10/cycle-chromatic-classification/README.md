# Infinite log-concavity of cycle chromatic coefficients: a complete classification

**Zenodo 预印本：[10.5281/zenodo.23249722](https://doi.org/10.5281/zenodo.23249722)**，版本 2.0。PDF、TeX 和固定提交证明归档已公开。

Author: Yongxian Zhang (张永贤). ORCID: https://orcid.org/0009-0000-3864-3536.
School of Computer Science and Engineering, South China University of Technology.
Correspondence: mxymmxym1@gmail.com. No external funding. AI-assisted research.

## Paper and exact scope

[Readable paper](paper.pdf) · [LaTeX source](paper.tex)

**Formalized principal scope:** Every genuine cycle graph C_n, n >= 3; full absolute coefficients, zero extension; infinitely log-concave iff n <= 11. The graph/polynomial correspondence and all positive and negative cases are formalized.

**Coverage is theorem-specific:** a complete proof of a principal theorem does not formalize every ancillary remark, checker implementation, historical draft or separate result in the repository.

## Proof source and reproduction

Proof source snapshot: [`02af7db99db789fecb0d5f5f8f37b1a4e40762a0`](https://github.com/mxym/math/commit/02af7db99db789fecb0d5f5f8f37b1a4e40762a0).
Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Formal entry points:

- `ChromaticCycleAll.cycleGraph_chromatic_polynomial_classification`
- `ChromaticCycleAll.every_actual_cycle_n_ge_17_fails`

Read the following packages' README and verification instructions. Each preserves source, transitive revision locks, audited proof boundaries, commands, negative controls and recorded evidence.

- [ chromatic-cycles-all-n-lean ](../../../formalizations/chromatic-cycles-all-n-lean/README.md)

Compile the paper from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The archive includes the corresponding formal packages and a fixed-commit source manifest. Exact checkers supplement readable proofs and the Lean kernel; their return values alone are not a mathematical proof.

## Rights and provenance

Existing file licenses and third-party notices remain in force. Previously unlicensed original material remains all rights reserved; public access grants no new blanket license. Mathematical facts and classical cited results are not claimed as owned. The manuscript is a newly typeset version of the public research; frozen formal source bytes are unchanged. No external human peer review, journal acceptance or worldwide priority is asserted.
