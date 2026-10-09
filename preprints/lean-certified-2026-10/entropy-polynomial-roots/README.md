# A counterexample to the entropy polynomial root conjecture

**Zenodo 预印本：[10.5281/zenodo.23253028](https://doi.org/10.5281/zenodo.23253028)**，版本 2.1。PDF、TeX 和固定提交证明归档已公开。

Author: Yongxian Zhang (张永贤). ORCID: https://orcid.org/0009-0000-3864-3536.
School of Computer Science and Engineering, South China University of Technology.
Correspondence: mxymmxym1@gmail.com. No external funding. AI-assisted research.

## Paper and exact scope

[Readable paper](paper.pdf) · [LaTeX source](paper.tex)

**Formalized principal scope:** The k=11, r=10 counterexample with the original real-power parameter, its bridge to the integer equation, exact coefficients, strict signs and four distinct open-interval roots. No claim about the exact root count or the separate entropy inequality.

**Coverage is theorem-specific:** a complete proof of a principal theorem does not formalize every ancillary remark, checker implementation, historical draft or separate result in the repository.

## Proof source and reproduction

Proof source snapshot: [`02af7db99db789fecb0d5f5f8f37b1a4e40762a0`](https://github.com/mxym/math/commit/02af7db99db789fecb0d5f5f8f37b1a4e40762a0).
Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Formal entry points:

- `EntropyCounterexample.counterexample_to_conjecture_two_original_real_power`
- `EntropyCounterexample.wakhare_conjecture_two_false_original_real_power`

Read the following packages' README and verification instructions. Each preserves source, transitive revision locks, audited proof boundaries, commands, negative controls and recorded evidence.

- [ formalization ](../../../notes/entropy-polynomial-counterexample/formalization/source/README.md)

Compile the paper from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The archive includes the corresponding formal packages and a fixed-commit source manifest. Exact checkers supplement readable proofs and the Lean kernel; their return values alone are not a mathematical proof.

## Additional complete polynomial formalization (8 October 2026)

A second self-contained [five-module Lake project](../../../formalizations/wakhare-entropy-four-roots-lean/README.md), published at [93a7512](https://github.com/mxym/math/commit/93a7512b3606581fcbbca310c7d2d587a8c1a903), constructs an actual `ℝ[X]` polynomial directly from the original binomial sums. Its endpoint `EntropyRoot.actual_polynomial_has_four_distinct_roots` proves at least four strictly ordered roots in `(0,1)`; it does not assert that there are exactly four. The unique positive parameter, five rational sign certificates and evaluation identity are also formalized.

[GitHub CI 37853632676](https://github.com/mxym/math/actions/runs/37853632676) **completed successfully** on that exact commit: 1,643 Lake build tasks, all source hashes, 12 theorem-root axiom audits and rejection of an intentionally invalid proof. The permitted logical axioms are `propext`, `Classical.choice` and `Quot.sound`.

This is an additional proof implementation of the already public counterexample. Version 2.1 includes both proof implementations. The earlier version 2.0 archive (https://doi.org/10.5281/zenodo.23249754) remains frozen and does not contain the later project. The older proof separately supplies the original real-power parameter bridge; neither historical proof record is replaced. [Current status and CI evidence](../audit/WAKHARE_ADDITIONAL_STATUS.json).

## Rights and provenance

Existing file licenses and third-party notices remain in force. Previously unlicensed original material remains all rights reserved; public access grants no new blanket license. Mathematical facts and classical cited results are not claimed as owned. The manuscript is a newly typeset version of the public research; frozen formal source bytes are unchanged. No external human peer review, journal acceptance or worldwide priority is asserted.

[Article audit and exact publication scope](../../../reviews/manuscript-quality-2026-10-08/README.md).
