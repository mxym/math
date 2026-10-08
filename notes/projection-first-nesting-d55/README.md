# Dimension 55 is the first where product/join nesting is necessary for optimal projection-body volume

**Supplement to manuscript 005 — 8 October 2026.**

[Complete theorem and proof](paper.md) · [Exact 49–55 full-tree checker](code/check_all_tree.py) · [Independent two-layer checker](code/check_two_layer.py) · [Audit and trust boundary](AUDIT.md).

Let `C_d` be the class of all `d`-dimensional convex polytopes generated from a point by **arbitrary** products and affine joins, up to invertible affine equivalences. Let `B_d` be the subclass of affine joins of points and `T_p × T_q` blocks for any positive integer p,q. Let `M_A(d)=max_{K in A_d}R(K)/c_d`, with `c_d` the projection-body value for a `d`-simplex.

**New exact theorem:**

- **Every dimension 1–54:** `M_C(d)=M_B(d)` — there exists a two-layer maximizing body.
- **First separation, dimension 55:** `M_C(55)=333068659627091928809841719168016922609375/83816757831946947640666468303298107539456` strictly exceeds `M_B(55)=9444402294359878125/2393367762580799488`.
- An attaining full-tree body is `B(4,4) * B(5,5) * B(5,5) * (T7 × (B(4,4) * B(4,4)))`; the best two-layer value is attained by `B(5,6) * B(5,5)^(*4)`, with `B(p,q)=T_p×T_q` and `*` denoting affine join.

The full-tree certificate builds on the [independently verified d≤48 base](../exact-product-join-finite-optima/README.md) and adds 3,066 exact frontier states and 2,523,858 new binary-closure comparisons. A **separate** two-layer certificate verifies 5,611 attained states and 430,360 independent block/point additions through dimension 55. Both check **attainability and upper closure**, not just candidate optimal values. Regeneration is reproducible and ordinary/optimized Python outputs are compared byte-identically.

## Reproduce from repository root

```sh
# Replay the pinned original full-tree certificate through dimension 48:
python3 notes/exact-product-join-finite-optima/code/check.py

# New exact full-tree extension and independent two-layer certificate:
python3 notes/projection-first-nesting-d55/code/check_all_tree.py
python3 -O notes/projection-first-nesting-d55/code/check_all_tree.py
python3 notes/projection-first-nesting-d55/code/check_two_layer.py
python3 -O notes/projection-first-nesting-d55/code/check_two_layer.py

# Tamper detection, then source hashes:
python3 notes/projection-first-nesting-d55/code/negative_controls.py
(cd notes/projection-first-nesting-d55 && sha256sum -c SHA256SUMS)
```

Optional exact producer replays (costlier, but also standard-library only):

```sh
python3 notes/projection-first-nesting-d55/code/build_all_tree.py /tmp/product_join49to55.json
cmp /tmp/product_join49to55.json notes/projection-first-nesting-d55/certificates/all_tree49to55.json
python3 notes/projection-first-nesting-d55/code/build_two_layer.py
# `build_two_layer.py` deterministically overwrites only its own two-layer certificate.
```

Neither theorem covers all convex bodies. The result identifies the first dimension where nesting is **needed for attaining the optimum**, not the first dimension in which any nested body is an optimizer; an equality-classification theorem is not claimed. The earlier dimension-85 and asymptotic depth-separation results remain valid, and their historical files are untouched. The paper uses the entry-005 v2 geometric calculus but no heuristic solver output. Model-assisted research, without external human peer review, complete Lean formalization or claims about worldwide priority.
