# Self-review and exact verification scope

Date: 7 October 2026. This is author/model-conducted self-review plus
independently executable exact and kernel checks, not outside human
mathematical review or an independent model proof audit.

## Mathematical checks

- The finite input uses rank, not uniformity. Its parameter k=D-1 is
  at least two. Delta>0 is exactly the strict branch condition, with
  the constant D retained; it is not merely an asymptotic inequality.
- Uniform dual edge weights 1/D are feasible in the original and repaired
  families. Their lower bound matches the finite upper branch.
- Summing all primal loads proves tightness at every edge and degree-D
  support of every optimum. It is a standard tightness consequence,
  not separately advertised as a new theorem.
- An optimal cover set exists by finite compactness after truncation.
  Its load-tight subset lies in the unit box, so the maximum coordinate
  has a minimizer. The proof applies to a finite positive m.
- Three nonempty groups exist only because D>=3. Every repaired
  incident label receives exactly two new vertices; every new degree
  is at least two and strictly below D. Simplicity follows from an
  original distinguishing vertex and its fresh replacements.
- The rank increase is L, not (D-2)L. Delta>K_D L, with K_D=D(D-2),
  implies a repaired optimum avoiding every removed coordinate. Removed
  sets may have large total size; only per-edge incidence is bounded.
- A minimax contradiction requires avoiding *all* maximum coordinates.
  The finite coordinate gap permits a sufficiently small convex mixture.
  The rounded bound follows from L<=1/M<N and the strict inequality
  ceil(Delta/K_D)-1<Delta/K_D. Existence does not bound every optimum;
  the exact parallel-class certificate demonstrates this distinction.
- The incidence dual can contain repeated blocks. Merging them sums
  weights, preserves all weighted restrictions and can use an original
  representative for every chosen integer block.
- The local pair budget counts every outside point at least once and
  counts inside pairs with multiplicity. It is valid even with large
  pair intersections and nonuniform original edges.
- Rare higher-subset mass is at most binomial(h,3) M lambda. The graph
  part is normalized by 1-eta before invoking Edmonds. Higher subsets
  are then included as singleton matchings with their exact weights.
- Ignoring size-zero and size-one restriction coordinates is Kayll's
  stated definition of b(t), not permission to drop cover constraints.
- The threshold follows from C delta<2/3 with
  C=D(D-2)/(1-(D-1)delta). For D=3 it is 24/13; for D=4 it is 44/15.
  The denominator is positive throughout the stated open interval.
- The slow-growing h choice makes both M h and h^3 M lambda vanish,
  uniformly over all point subsets of at most h. It gives b(t)->infinity,
  which is a real hypothesis of the imported theorem.
- The core corollary uses the predecessor's strict-ramp extraction.
  It adds at most one integer vertex for each deleted nonempty edge.
  It does not assume the whole family already has bounded vertex degree.

## Verification executed

`check_exact.py` was replayed in ordinary and `-O` Python with identical
output. It includes 11,684 exact scalar checks, original/avoiding/mixed
optimal-cover certificates, 36 repair instances across D=3--12, 592
actual local budgets, finite local-polytope threshold equality, pair-clone
incidence, an explicit higher-subset matching distribution, and two
negative controls. Fixed diagnostic examples do not prove universality.

Six finite Lean exports compile against the pinned dependencies with
standard axioms only. Two check the three-complement finite mechanism;
one controls the actual local restriction from actual pair counts. The
others are scalar implications. No numerical solver is a proof input.
The bootstrap was executed with available compiled dependency caches;
the manifest pins the corresponding remote source revisions.

The complete proof/PDF was read during self-review. PDFLaTeX was run
twice with no overfull or undefined-reference warnings, and rendered
theorem and local-rounding pages were inspected. Frozen file integrity
and the predecessor inventories are separately replayable.

## Explicit proof dependencies and unresolved claims

The predecessor finite bound and fractional edge-core extraction are
repository inputs with full written proofs. Kayll 1995 Theorem 2.1 and
Edmonds 1965 are stated imported classical inputs. This package does not
reprove either. The readable primary Kayll source is its DIMACS extended
abstract; the full later 1997 article was inaccessible during screening.

The complete minimax compactness/repair existence, global LP facts,
Edmonds, Kayll and asymptotic limits are not Lean-formalized. No global
Kahn 5.5 resolution, threshold optimality, entire-ramp rounding, Ryser
resolution, mathematical priority, outside peer review, or journal
acceptance is claimed. The literature agent compared sources only.
