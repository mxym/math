# Sharp binary tensor rigidity

This companion to the [global tensor note](../global-orthogonal-tensor-rigidity/README.md)
proves three additional results for real fully symmetric tensors on R²,
with arbitrary real orthogonal-decomposition weights:

- The optimal binary constant in `dist_F(T,odeco) <= C_p sqrt(R_p(T))`
  has order **p^(1/4)** as tensor order tends to infinity. Both an explicit
  all-orders upper bound and an exact infinite lower-bound family are proved.
- For order four the **best constant is 3^(1/4)/sqrt(2)**. All equality
  cases with nonzero residual form one orthogonal orbit up to real scaling.
- A two-dimensional Gram determinant gives the exact complete contraction
  residual, providing the basic bound `C_p <= sqrt(p)/2`, sharper trace
  refinements and the proofs above.

Here `R_p²` sums squared Frobenius commutator norms over **all ordered pairs
of all ordered (p−2)-index contractions**. Omitting multiplicities changes
the constants. The [complete paper](paper.md) defines every convention,
proves all statements and covers zero residual and degenerate weights.
[PDF](paper.pdf) · [Exact checker](checks/check_exact.py) ·
[Lean scalar proofs](formal/QuarticCertificate.lean).

No OpenAI theorem is used in these results. The qualitative odeco algebraic
characterization has established prior literature; our scope is quantitative.
The [preliminary literature comparison](../../research/novelty-assessment/2026-10-07-binary-odeco-benchmarks.md)
was delegated to GPT-6 Luna at High reasoning effort. It reports limited
searches and read sources, not a first-discovery or priority determination.
The proofs and exact checks here were developed and reviewed by the primary
model. There is no external human peer review.

## Reproduction

Exact diagnostic replay needs Python 3.10+ and only its standard library:

```sh
python3 verify.py
```

This verifies package hashes and runs the checker normally and with `-O`.
Sparse rational polynomial expansion verifies the quartic identities;
Q(sqrt(3)) arithmetic verifies the sharp tensor and ordered residual;
rational rotations test contraction multiplicities; orders 5 through 40
replay the lower-family and trace formulas. Those finite checks support
formula debugging; the universal and infinite claims have written proofs.

Nine partial Lean statements formalize the domain-wide scalar quartic
certificate, its residual link, and the elementary matching-growth step:

```sh
cd formal
./bootstrap.sh
cd ..
python3 verify.py --lean
```

The bootstrap pins Lean 4.34.1, mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and all dependencies in
`lake-manifest.json`. It downloads public toolchains/packages and uses no
private service. The recorded axiom exports contain only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, new postulated
axiom, or numerical oracle. Tensor geometry, angular reduction, equality
classification and the infinite binomial proof are **not formalized**.

PDF rebuilding additionally needs Pandoc and pdfLaTeX:

```sh
./build.sh /tmp/sharp-binary-tensor-pdf
```

The frozen published PDF is not rewritten by verification. Build products
can have different metadata; the editable mathematical source is `paper.md`.

## Remaining questions

The growth order p^(1/4) is determined, but its optimal leading constant,
convergence and all-order equality cases remain open in this note.
Higher-dimensional optimal dependence is also unresolved. These are research
results with explicit proof and verification scopes; no major classical
conjecture or award-level breakthrough is claimed.
