# An exact Pareto dynamic program for product–join projection geometry: sharp extrema through dimension 48

**Research note, 8 October 2026.** Prepared with AI assistance for the `mxym/math` repository. The proof uses the previously published 005 v2 projection-body calculus. The finite certificate is independently replayed in exact rational arithmetic. No publication-priority or external peer-review claim is made.

## Abstract

For the class \(\mathcal C\) of polytopes generated from a point by arbitrary finite Cartesian products, affine joins and invertible affine transformations on affine hulls, we give an exact algorithm for the normalized projection-body volume maximum in any prescribed dimension. An elementary coordinatewise-dominance principle makes the entire grammar reducible to a finite two-coordinate Pareto frontier. Our exact certificate computes and independently verifies every frontier in dimensions \(0,1,\ldots,48\), including all 1,956,775 binary candidates between retained states. This determines the sharp maximum and supplies an attaining polytope in every positive dimension at most 48, extending the previously certified exact range through dimension 14. Every optimum in this range admits an attaining expression consisting of a join of points and products of two simplices. In dimension 48 the sharp ratio to the simplex value is \(105488578125/34359738368>3\), attained by a join of three \(T_4\times T_4\) and two \(T_5\times T_5\) blocks. The algorithm works abstractly in every finite dimension; the **certified numerical range is only 1 through 48**. The full asymptotic growth problem remains open.

## 1. Class, invariants and theorem

For every \(d\ge1\), write
\[
 R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad g(d)=\frac{d^d}{d!},
 \qquad c_d=(d+1)g(d).
\]
Here \(\Pi K\) is the projection body of a full-dimensional \(d\)-polytope; \(c_d\) is the \(d\)-simplex value. Let \(\mathcal C\) be the smallest class containing a formal zero-dimensional point and closed under (i) Cartesian products in independent spaces; (ii) affine joins; and (iii) invertible affine changes of coordinates between affine hulls. The point is a product identity, and zero-dimensional factors may be omitted from products. The class does not contain arbitrary projections or rank-dropping affine maps.

The affine invariant \(a(K)>0\) is the normalized lifted-facet determinant sum defined and proved in [005 v2](../../preprints/005-simplex-product-optimum/v2/paper.md). For \(d\ge1\), set
\[
 D(K)=d+1,\qquad H(K)=1/a(K),\qquad
 Q(K)=\frac{a(K)R(K)}{g(d)}.
 \tag{1.1}
\]
For the point we use the formal values \(D=H=Q=1\). All coordinates are rational for \(K\in\mathcal C\), by the operation calculus below. In particular,
\[
 \boxed{\frac{R(K)}{c_d}=\frac{H(K)Q(K)}{d+1}.}
 \tag{1.2}
\]
Let \(M_d=\max_{K\in\mathcal C,\ \dim K=d}R(K)/c_d\). This maximum exists: affine-equivalent operation trees yield identical values, and after eliminating neutral products, only finitely many binary tree types are available in any fixed dimension.

**Theorem 1 (exact finite classification).** There is an exact, terminating recursion on finite Pareto sets \(F_d\subset\mathbb Q_{>0}^2\) satisfying
\[
 \boxed{M_d=\max_{(H,Q)\in F_d}\frac{HQ}{d+1}}
 \qquad(d\ge1).
 \tag{1.3}
\]
The frontier recursion is specified in Section 3 and is proved correct for **every integer \(d\ge1\)**. A separately replayable rational certificate establishes all instances \(1\le d\le48\). More precisely:

1. \(M_1=\cdots=M_{13}=1\) and \(M_{14}=385/384\), agreeing with the inherited exact calculations of 005 v2.
2. The exact ratio \(M_d\) and an attaining construction for **every** \(15\le d\le48\) are in [`results/optima.tsv`](results/optima.tsv). For each such dimension, **at least one** maximizing body is an affine join of points and products \(T_p\times T_q\); this is not a uniqueness or complete equality-classification claim.
3. At dimension 48,
\[
 \boxed{M_{48}=\frac{105488578125}{34359738368}>3.}
 \tag{1.4}
\]
An explicit maximizer is
\[
 \boxed{K_{48}=(T_4\times T_4)^{*3}*(T_5\times T_5)^{*2}.}
 \tag{1.5}
\]
Here \(*t\) indicates a \(t\)-fold affine join, not a Cartesian power.

Only the recursion (1.3) is an all-dimensional theorem; its evaluated sharp-value table stops at dimension 48. The class restriction is essential. This is not a claim concerning the unrestricted maximizers among all convex bodies or the optimum asymptotic spectral rate of the entire product–join class.

## 2. Exact two-coordinate calculus

The following identities are imported, with explicit attribution, from [005 v2, product/join calculus](../../preprints/005-simplex-product-optimum/v2/paper.md). For \(A\in\mathcal C_r\), \(B\in\mathcal C_s\), the join satisfies
\[
 D(A*B)=D(A)+D(B),\quad
 H(A*B)=H(A)+H(B),\quad Q(A*B)=Q(A)Q(B).
 \tag{2.1}
\]
These formulas include the formal point. For a **nontrivial product** \(r,s\ge1\), write \(n=r+s\), \((H_A,Q_A)=(h,u)\), and \((H_B,Q_B)=(j,v)\). The product identities read
\[
 \boxed{H(A\times B)=\frac{n}{r/h+s/j},\qquad
 Q(A\times B)=uv\,\frac{g(r)g(s)}{g(n)}\,
 \frac{sh+rj}{n}.}
 \tag{2.2}
\]
Both outputs are positive rational numbers when the inputs are. The dimensions of joins and products are \(r+s+1\) and \(r+s\), respectively; all three invariants are unaffected by affine equivalence.

## 3. Coordinatewise domination and exact frontier algorithm

At a fixed dimension, define
\[
 (h,u)\succeq(j,v)\quad\Longleftrightarrow\quad h\ge j\ \text{and}\ u\ge v.
 \tag{3.1}
\]

**Lemma 2 (context dominance).** If \(A,B\) have equal dimension and \((H(A),Q(A))\succeq(H(B),Q(B))\), then replacing \(B\) by \(A\) in any larger well-typed finite product–join expression never decreases either of the resulting \(H,Q\) coordinates. Thus it never decreases \(R\) at the fixed final dimension.

**Proof.** For joins, (2.1) adds positive \(H\) and multiplies positive \(Q\), both order preserving. For products, the harmonic-mean expression \(n/(r/h+s/j)\) is strictly increasing in each positive argument, as is \((sh+rj)/n\); multiplication by the positive \(uvg(r)g(s)/g(n)\) preserves the order. Hence (2.2) is coordinatewise increasing in each input pair. Apply this at each ancestor node of the substituted subtree, one operation at a time; affine changes of coordinates leave \(D,H,Q\) unchanged. The final claim follows from (1.2). \(\square\)

For any finite set \(S\subset\mathbb Q_{>0}^2\), denote by \(\operatorname{Max}(S)\) its coordinatewise nondominated elements, identifying equal pairs. Construct recursively
\[
 F_0=\{(1,1)\},\qquad F_n=\operatorname{Max}(C_n),
 \tag{3.2}
\]
where \(C_n\) is the union of the following sets:

- \(J(F_r,F_s)\), all \(r,s\ge0\) with \(r+s+1=n\), using (2.1);
- \(P(F_r,F_s)\), all \(r,s\ge1\) with \(r+s=n\), using (2.2).

**Proposition 3 (all-dimensional exactness).** For each \(n\ge0\), every \(n\)-dimensional member of \(\mathcal C\) is coordinatewise dominated by some point of \(F_n\), and every member of \(F_n\) is attained by an explicit polytope in \(\mathcal C_n\). Consequently (1.3) is exact for every \(n\ge1\).

**Proof.** The statement holds at dimension zero. Let \(n\ge1\). Each nontrivial outer operation decomposes a body into smaller-dimensional factors: for a join \(n=r+s+1\) with \(r,s\ge0\), and for a product \(n=r+s\) with \(r,s\ge1\). An affine equivalence changes no state. By induction, each factor is dominated by a front element in its own dimension. Lemma 2 implies the original output is dominated by the operation on those front elements, belonging to \(C_n\). Every element of finite \(C_n\) is dominated by an element of \(\operatorname{Max}(C_n)=F_n\). Conversely every \(C_n\) element is exactly attainable by composing the inductively constructed witnesses for its two inputs, so every front element is attained. Applying the increasing objective \(HQ/(n+1)\) yields (1.3). A neutral product by a point is literally the same body and may be suppressed; a join by a point raises dimension, so no recursive cycle occurs. \(\square\)

This result is **not** merely an empirical observation that a small Pareto list seems adequate: the context-substitution lemma proves global soundness of the deletion step, and the induction covers *all* finite binary product/join expression trees.

## 4. Exact sharp 48-dimensional maximizer

Set \(B_p=T_p\times T_p\). Since \(H(T_p)=p+1\), \(Q(T_p)=1\), formulas (2.2) give
\[
 H(B_p)=p+1,\qquad
 Q(B_p)=(p+1)\frac{g(p)^2}{g(2p)}.
 \tag{4.1}
\]
Direct integer factorial simplification gives
\[
 Q(B_4)=\frac{175}{128},\qquad Q(B_5)=\frac{189}{128}.
 \tag{4.2}
\]
Consider the join \(K_{48}=B_4^{*3}*B_5^{*2}\). Its \(D\)-coordinate and dimension are
\[
 D=3(2\cdot4+1)+2(2\cdot5+1)=49,\qquad d=48.
\]
The join law (2.1) gives
\[
 H(K_{48})=3\cdot5+2\cdot6=27,\qquad
 Q(K_{48})=\left(\frac{175}{128}\right)^3
 \left(\frac{189}{128}\right)^2.
\]
Therefore by (1.2),
\[
 \frac{R(K_{48})}{c_{48}}
 =\frac{27}{49}\frac{175^3 189^2}{128^5}
 =\boxed{\frac{105488578125}{34359738368}}
 >3.
 \tag{4.3}
\]
The difficult assertion is that **no other product/join tree** in dimension 48 has a larger value. That upper assertion follows from Proposition 3 and the complete exact frontier certificate described in Section 5, which independently verifies
\[
 \max_{(h,u)\in F_{48}}\frac{hu}{49}
 =\frac{105488578125}{34359738368}.
\]
The explicit construction verifies attainment without trusting the computational witness pointers.

## 5. Finite certificate: what is verified

The producer [`code/build.py`](code/build.py) constructs exact rational frontiers for \(n=0,\ldots,48\) and emits [`certificates/frontiers48.json`](certificates/frontiers48.json). Each state stores its reduced rational \(H,Q\) and a binary operation pointer to two states from strictly smaller dimensions. There are exactly **6,494** retained states, including the zero-dimensional point.

The **separate verifier** [`code/check.py`](code/check.py) does *not* import the producer. It reads the certificate as untrusted data and checks four mathematical conditions for every dimension:

1. **Attainability.** Every frontier state is reconstructed exactly from its two explicitly indexed parent states using (2.1) or (2.2). All pointers, dimensions, canonical fractions and the zero-dimensional point are checked.
2. **Antichain property.** Frontiers are strictly decreasing in \(H\) and strictly increasing in \(Q\), excluding internal domination and duplicated states.
3. **Exhaustive dominance.** Every binary join and every genuine product of **all pairs of retained lower-dimensional states** is dominated by a state in the indicated frontier. This entails precisely **1,956,775 candidate comparisons** over all dimensions 1 through 48, each in exact integer/Fraction arithmetic. The verifier uses binary search over the ordered frontier, not geometric sampling or a numerical optimizer.
4. **Optimal objective and shape.** It recomputes the maximum \(HQ/(n+1)\), checks each stored exact optimum fraction and its witness pointer, and separately checks that the selected winner is a join of point factors and products of two simplices. It compares the dimension-14 historical value and the dimension-48 explicit fraction independently.

These four conditions and Proposition 3 imply that the reported values are **sharp within the entire class \(\mathcal C_d\)** for every \(1\le d\le48\). They do not depend on floating arithmetic or on the producer's heuristic behavior. Ordinary and optimized Python executions must agree byte for byte. Deliberate certificate corruptions are tested separately by [`code/negative_controls.py`](code/negative_controls.py).

From the repository root:

```sh
python3 notes/exact-product-join-finite-optima/code/check.py
python3 -O notes/exact-product-join-finite-optima/code/check.py
python3 notes/exact-product-join-finite-optima/code/negative_controls.py
```

Optional independent regeneration (more computationally expensive):

```sh
python3 notes/exact-product-join-finite-optima/code/build.py 48 /tmp/frontiers48-regenerated.json
cmp /tmp/frontiers48-regenerated.json notes/exact-product-join-finite-optima/certificates/frontiers48.json
```

The verifier contains no `assert`-dependent decisions; failed inequalities raise explicit exceptions even under \(`python -O`\). The computational theorem is conditional on the cited analytic geometric product/join formulas in v2; **these geometric identities are proved in v2 but are not re-proved or Lean-formalized by the finite checker**. The certificate itself is finite, self-contained and uses standard-library exact rational arithmetic.

## 6. Perspective and precise limitations

The 005 v2 paper already determined \(M_n=1\) through dimension 13 and \(M_{14}=385/384\). The new contribution is (i) the rigorous general Pareto domination/reduction principle as an exact state-compression algorithm for arbitrary expression trees; (ii) the **sharp finite-dimensional classification through dimension 48**, including the explicit body (4.3); and (iii) independent, replayable attainability and dominance certificates for all finite cases. It is not an extension of the balanced or independent-arity *homogeneous* theorems only; different subtrees and arbitrary operation order are allowed.

The numerical frontier sizes observed through dimension 48 are **not** evidence for a proved polynomial bound on frontier sizes, nor does the finite certificate imply the theorem for dimension 49 or beyond. No equality classification of *all* extremizers is asserted. The spectral constant \(\Gamma_{\mathcal C}\) for unbounded dimension remains between the separately published lower and upper bounds; the present finite theorem alone does not determine it. This note is independent of the Gaussian-propeller, quadratically ordered moat and other simultaneous research threads.

### Provenance

Core calculus: [005 version 2](../../preprints/005-simplex-product-optimum/v2/paper.md), Git blob `5d5b909b5b6532910af80e17ba5abf74c0ae4c02`, ultimately building on OpenAI/math family 088's simplex-product projection-body mechanism and earlier classical affine projection inequalities. The current exact result and computation are in this note; all prior formulas are explicitly distinguished from the additional Pareto recurrence and its finite sharp-value certificates. No worldwide-first, human-refereed or full-formalization assertion is made.
