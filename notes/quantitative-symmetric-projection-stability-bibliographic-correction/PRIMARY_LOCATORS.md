# Primary-source verification of the bibliographic correction

Checked on 7 October 2026. This is a read-only source audit for the separate
bibliographic correction. It does not change a theorem, supply a novelty claim,
or compare numerical stability exponents across different functionals.

## 1. Weil bodies and the projection-body antecedent

Christos Saroglou, *On the shape of a convex body with respect to its second
projection body*, arXiv:1409.4347v2 (16 September 2014).

- [Versioned PDF](https://arxiv.org/pdf/1409.4347v2), printed pp. 2–4
  (PDF pages 2–4), and [HTML](https://arxiv.org/html/1409.4347v2).
- The introduction on pp. 2–3 calls Cartesian products of symmetric bodies of
  dimensions one or two Weil bodies. It connects them to Weil's classification
  of polytopes homothetic to their second projection body. Affine invariance is
  discussed in the introduction and Section 2.
- Theorem 1.2 on p. 4 concerns the functional \(M(K)\) for three-dimensional
  zonoids and has precisely centrally symmetric cylinders as equality cases.
  Its functional differs from the supplement's \(a(K)\).
- Do not substitute Saroglou's introductory Theorem A: that distinct result has
  additional equality cases. The 1971 Weil reference is listed as [39] on p. 18:
  *Über die Projektionenkörper konvexer Polytope*, Arch. Math. 22, 664–672.
  The original article was not obtained here; no theorem number is asserted.

Verdict: the proposed geometric-context paragraph is accurate with these
distinctions retained.

## 2. The matroid structural antecedent

Jorn van der Pol, Zach Walsh, and Michael C. Wigal, *Turán densities for matroid
basis hypergraphs*, arXiv:2502.03673v2.

- [Section 5 HTML](https://arxiv.org/html/2502.03673v2#S5),
  [Lemma 5.2 HTML](https://arxiv.org/html/2502.03673v2#S5.Thmtheorem2), and
  [PDF](https://arxiv.org/pdf/2502.03673v2), printed pp. 14–15.
- Raw HTML independently confirms that both of these anchor identifiers exist.
- Section 5 on p. 14 identifies the condition that every circuit has at most
  three elements with exclusion of the \(U_{3,4}\) minor. Lemma 5.2 on p. 15
  gives the decomposition into direct summands of rank at most two. Its proof
  uses a basis and eliminates overlapping two-element spans.
- [arXiv submission history](https://arxiv.org/abs/2502.03673) confirms first
  posting on 5 February 2025 and version 2 on 10 March 2025.

Verdict: the proposed finite-support attribution is correct. The almost-sure
measure formulation and the estimate from small expected cofactors must still
be proved in the supplement; they are not consequences stated in this source.

## 3. Determinant expectations as zonoid volumes

Gleb Koshevoy and Karl Mosler, *Lift zonoids, random convex hulls and the
variability of random vectors*, Bernoulli 4(3) (1998), 377–399.

- [Primary PDF](https://wisostat.uni-koeln.de/sites/dep_econometrics/pdf_publikationen/1998_KoshevoyM98.pdf).
- Definition 2.1, printed p. 379; Proposition 2.2, p. 381; Definition 3.1,
  p. 382: their probability-law normalization is
  \(Z(F)=\mathbb E[0,X]\),
  \(\widehat Z(F)=\mathbb E[0,(1,X)]\).
- Proof of Theorem 4.1 and equation (4.3), printed p. 387 (PDF page 11), give
  \[
  |Z(F)|=\frac{\mathbb E|\det(X_1,\ldots,X_d)|}{d!},\qquad
  |\widehat Z(F)|=\frac{\mathbb E|\det((1,X_1),\ldots,(1,X_{d+1}))|}{(d+1)!}.
  \]
- Placing the lifted coordinate last changes only the determinant sign. For
  the manuscript's definitions this gives \(A/d!\), \(B/(d+1)!\), and ratio
  \(B/((d+1)A)\). The paper attributes the ordinary determinant-volume
  identity to Vitale (1991a); the proposed Koshevoy–Mosler locator is accurate.

Verdict: normalization checked; no extra factor is missing. The cone-law
identity and endpoint conclusions remain separate from this classical volume
representation.

## 4. Nested-body volume loss and containment

Károly J. Böröczky and Martin Henk, *Cone-volume measure and stability*.

- [Primary PDF](https://www.renyi.hu/~carlos/cone-volume-stability.pdf),
  Lemma 3.1(i), printed p. 8 (PDF page 8).
- For a centered outer body \(K\), an inner convex body \(Q\), and relative
  volume loss at most \(t<1/e\), the lemma gives
  \((1-(et)^{1/n})K\subseteq Q\).
- Its proof places a homothetic copy of \(K\) at a support contact and uses
  the centered half-space volume bound \(1/e\). If \(K\) is centrally
  symmetric, that copy has exactly half its volume on either side of its
  central support-parallel hyperplane. The same proof therefore uses \(1/2\)
  and yields the supplement's constant \(2\).

Verdict: the attribution and stated symmetry improvement are justified.

## 5. Truncated cubes and anisotropic weak-measure collapse

Károly J. Böröczky and Apratim De, *Stable solution of the Logarithmic Minkowski
problem in the case of hyperplane symmetries*, Journal of Differential
Equations 298 (2021), 298–322.

- [Published primary PDF](https://real.mtak.hu/196592/1/1-s2.0-S0022039621004393-main.pdf),
  journal p. 302 (PDF page 5).
- The paragraph before Example 1.4 describes an unconditional cube with
  vertices removed by simplices, followed by rescaling to volume one. It is
  sufficient geometric context for the proposed replacement. No numerical
  Wasserstein scaling is imported in this correction.
- Example 1.4 assumes both bodies contain the origin in their interiors, have
  volume one, and give zero cone mass to \(e^\perp\cap S^{n-1}\). Under the
  stated volume-preserving diagonal squeeze, the cone-volume measures converge
  weakly to the same measure supported on \(\{e,-e\}\).

Verdict: both replacement paragraphs accurately distinguish shared truncation
geometry from the supplement's own scalar calculation and full equality-class
distance bound. The zero-equator hypothesis is indispensable to the cited
example and is retained. No claim against an external main theorem is made.

## Overall result

All requested primary attributions are substantively consistent. The precise
section and page locators above have been checked against the named versions.
This audit supplies no correction to the supplement's mathematics and raises
no blocker to applying the proposed editorial changes.
