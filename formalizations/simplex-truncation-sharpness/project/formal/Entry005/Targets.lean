import Entry005.Constants
import Entry005.ProjectionCap
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Literal unconditional end-to-end TARGETS, not theorems.  These definitions
create no axioms and assume no cone-law, Cauchy, Minkowski or cap conclusion.
No term inhabiting the final target propositions is claimed in this project.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Entry005

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def projectionVolumeSet (K : Set E) (u : E) : ℝ :=
  (volume ((ℝ ∙ u)ᗮ.orthogonalProjectionOnto '' K)).toReal

/-- The body whose unit support function is projection volume.  Existence of
that support representation remains an obligation; the target uses the actual
intersection of halfspaces, not an uninterpreted placeholder. -/
def projectionBodySet (K : Set E) : Set E :=
  {x | ∀ u : E, ‖u‖ = 1 → inner ℝ u x ≤ projectionVolumeSet K u}

def projectionRatio (K : Set E) : ℝ :=
  (volume (projectionBodySet K)).toReal / (volume K).toReal ^ (Module.finrank ℝ E - 1)

def pyramidSet (K : Set E) : Set (WithLp 2 (E × ℝ)) :=
  convexHull ℝ ((fun x : E => WithLp.toLp 2 (x, (0 : ℝ))) '' K ∪
    {WithLp.toLp 2 ((0 : E), (1 : ℝ))})

def entryA (K : Set E) : ℝ :=
  (((Module.finrank ℝ E : ℝ) / (Module.finrank ℝ E + 1)) ^ Module.finrank ℝ E) *
    projectionRatio (pyramidSet K) / projectionRatio K - 1

def entryDefect (K : Set E) : ℝ := entryA K - 1 / (Module.finrank ℝ E + 1)

end Definitions

def simplexSet {d : ℕ} (S : Affine.Simplex ℝ (Space d) d) : Set (Space d) :=
  convexHull ℝ (Set.range S.points)

def maximumInscribed {d : ℕ} (K : ConvexBody (Space d))
    (S : Affine.Simplex ℝ (Space d) d) : Prop :=
  simplexSet S ⊆ K ∧ ∀ T : Affine.Simplex ℝ (Space d) d,
    simplexSet T ⊆ K → volume (simplexSet T) ≤ volume (simplexSet S)

def centeredDilation {d : ℕ} (S : Affine.Simplex ℝ (Space d) d) (t : ℝ) : Set (Space d) :=
  (fun x => S.centroid + (1 + t) • (x - S.centroid)) '' simplexSet S

def excess {d : ℕ} (K : Set (Space d)) (S : Affine.Simplex ℝ (Space d) d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ K ⊆ centeredDilation S t}

/-- Main target. In particular, maximum simplex is universally quantified and
there is no choice of a preferred simplex or alternate centroid. -/
def sharpMainGoal : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ K : ConvexBody (Space d),
    (interior (K : Set (Space d))).Nonempty →
    ∀ S : Affine.Simplex ℝ (Space d) d, maximumInscribed K S →
      excess (K : Set (Space d)) S ≤
        gSharp d * (entryDefect (K : Set (Space d))) ^ (1 / ((d - 1 : ℕ) : ℝ))

def sharpLocalGoal : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ K : ConvexBody (Space d),
    (interior (K : Set (Space d))).Nonempty →
    ∀ S : Affine.Simplex ℝ (Space d) d, maximumInscribed K S →
      0 ≤ entryDefect (K : Set (Space d)) → entryDefect (K : Set (Space d)) ≤ eSharp d →
      excess (K : Set (Space d)) S ≤
        aSharp d * (entryDefect (K : Set (Space d))) ^ (1 / ((d - 1 : ℕ) : ℝ))

/-- Explicit local-threshold gate from the written theorem. This is a separate
unproved obligation, not a hypothesis of the local estimate. -/
def thresholdGateGoal : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    aSharp d * (eSharp d) ^ (1 / ((d - 1 : ℕ) : ℝ)) ≤ 1 / 2

/-- Concrete truncation body, not a scalar model of its defect. -/
def truncationSet (d : ℕ) (t : ℝ) : Set (Space d) :=
  {x | (∀ i, 0 ≤ x i) ∧ t ≤ ∑ i, x i ∧ (∑ i, x i) ≤ 1}

/-- Matching sharpness target expressed using actual convex bodies and maxima.
The required witness body is precisely the displayed truncation family. Both the
truncation parameter and the positive defect can be made arbitrarily small. -/
def truncationSharpnessGoal : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ α : ℝ, 1 / ((d - 1 : ℕ) : ℝ) < α →
    ∀ C ε : ℝ, 0 ≤ C → 0 < ε →
      ∃ t : ℝ, 0 < t ∧ t < min ε 1 ∧
        ∃ K : ConvexBody (Space d), (K : Set (Space d)) = truncationSet d t ∧
          (interior (K : Set (Space d))).Nonempty ∧
          ∃ S : Affine.Simplex ℝ (Space d) d, maximumInscribed K S ∧
            0 < entryDefect (K : Set (Space d)) ∧
            entryDefect (K : Set (Space d)) < ε ∧
            C * (entryDefect (K : Set (Space d))) ^ α < excess (K : Set (Space d)) S

end Entry005
