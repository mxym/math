# Audit and trust boundary

Date: 8 October 2026. **Model-assisted author self-review only**; neither independent human peer review, blanket novelty certification nor complete Lean formalization is asserted.

## Source dependencies

- All geometric identities \(H=1/a\), \(Q=aR/g(d)\), the product of two simplices and the join additivity law are imported from entry 005 v2, `preprints/005-simplex-product-optimum/v2/paper.md`, blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`. Its development acknowledges the OpenAI/math family-088 simplex-product mechanism and earlier projection-body geometry.
- The present note proves its own one-variable Robbins envelopes, monotonicity and power comparisons; no claim is made that finite enumeration alone proves the two unbounded-parameter inequalities.
- The two-layer class is precisely joins of points and blocks \(T_p\times T_q\). Heterogeneous trees with products above joins are not in that restricted class, and rank-dropping affine maps are excluded.

## Exact checks

`code/check.py` uses Python integers and `Fraction`; it checks 56 spectral-core pairs, 380 H-defect-core pairs, Machin rational \(\pi\) enclosures, rational tail bases at 16 and 40, and the explicit nested dimension-85 body using strict rational-power inequalities. The exact output in both normal and optimized modes is byte-identical. The code does not depend on assertion statements, floats, a solver or the network. `code/negative_controls.py` verifies that invalid \(\pi\) data and false optimum constants are rejected; it does not establish analytical completeness, which rests on `paper.md` Sections 2–4.

## Claims and limits

**New:** unique block optimum for \(Q^{1/D}\), unique block optimum for \(\log Q/(D-H)\), exact asymptotic rate for arbitrary joins of two-simplex products, an explicit dimension-85 strict gap relative to that entire subgrammar, and an asymptotic strict gap for all sufficiently large dimensions. The last theorem **does not** locate the first crossover dimension or the unrestricted point-generated optimum at dimension 85.

The sharp finite all-tree computation to dimension 48 is a different earlier entry-005 supplement and is not silently upgraded here. This note is consistent with its result that a two-layer maximizing witness exists at every dimension through 48; it establishes a dimension 85 at which two layers are strictly insufficient.

Replay:

```sh
python3 notes/two-layer-projection-depth-separation/code/check.py
python3 -O notes/two-layer-projection-depth-separation/code/check.py
python3 notes/two-layer-projection-depth-separation/code/negative_controls.py
cd notes/two-layer-projection-depth-separation && sha256sum -c SHA256SUMS
```
