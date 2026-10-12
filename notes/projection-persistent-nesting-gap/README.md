# Permanent and sharply quantified projection-body nesting gap

**Research supplement to entry 005, 8 October 2026.**

[Complete proof](paper.md) · [Independent rational checker](code/check.py) · [Exact certificate producer](code/build.py) · [Frozen 29-level Pareto extension](certificates/extension57to85.json).

Let `C_d` denote the point-generated class of **all** Cartesian-product/affine-join trees in dimension `d` (up to invertible affine equivalence), and let `B_d` consist of joins of points and two-simplex product blocks `T_p × T_q`. For each class let `M(d)` be the maximum of the normalized projection-body ratio `R(K)/c_d`.

**New theorem (every integer dimension, sharp global constant):**

\[
\boxed{\frac{M_C(d)}{M_B(d)}\ge\rho_*,\quad d\ge55,\qquad
\rho_* = \frac{666588049410094050176708629890606697662639715}{661941565426077453299492872184552524829687808}>1.007.}
\]

**Equality in this ratio occurs only at `d=55`.** In particular, nesting **always** produces a strict improvement over the two-layer class from dimension 55 onward, with no later re-entrance. Quantitatively the factor is strictly **greater than 1.01** in every dimension `d>=56`, and **greater than 209/200 = 1.045** in every dimension `d>=85`. The ratio also **diverges at least exponentially**, with the explicit bound $M_C(d)/M_B(d)>(1009/1000)^{d-84}/45$ for every $d\ge85$.

The new finite certificate covers **every `55<=d<=84`** by independently certifying all sharp two-layer optima and one explicitly attained nested witness in each dimension. It checks **11,234 new Pareto states**, **2,837,399 exact point/block closure comparisons** and **30 rational witness inequalities**, importing and replaying the previously published exact two-layer 1–55 checker. The infinite tail is **analytic**, with only **11 exact rational residue comparisons**: repeat and join the explicit 85-dimensional binary \(T_5\)-orbit body with \(T_5\times T_5\) blocks and points, and use the previously certified pair of universal sharp two-layer block inequalities. It is **not** an inference from a bounded computation.

Replay in ordinary and optimized Python (standard library only):

```sh
python3 notes/projection-persistent-nesting-gap/code/check.py
python3 -O notes/projection-persistent-nesting-gap/code/check.py
python3 notes/projection-persistent-nesting-gap/code/negative_controls.py
(cd notes/projection-persistent-nesting-gap && sha256sum -c SHA256SUMS)
```

The exact program rejects corrupt states/coverage, incorrect constants and altered predecessor hashes. The result extends the sharp [dimension-55 first-crossover theorem](../projection-first-nesting-d55/README.md) and explicitly depends on the [universal two-layer spectral/defect inequalities](../two-layer-projection-depth-separation/paper.md). The formula for the exact global ratio over all `d>=55` is **sharp**, but exact `C_d` maxima in every individual dimension above 55 and the entire recursive class's asymptotic spectral constant remain open. No unrestricted convex-body maximization, external human review, whole-result Lean formalization or priority claim is made.
