import GaussianSetPartitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Statement-only file. These are precisely stated, still UNPROVED goals.
None is used as a hypothesis by the proved analytic modules. Compiling this
file checks definitions and types; it does not supply a proof of either goal. -/
open MeasureTheory ProbabilityTheory Set
namespace GaussianFourGlobal
open GaussianMeasureBridge

noncomputable def tetraVertex (i : Fin 4) : Space 3 :=
  WithLp.toLp 2 ((![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]] :
    Fin 4 → Fin 3 → ℝ) i)

noncomputable def sharpFourConstant : ℝ :=
  12 * (Real.arctan (Real.sqrt 2)) ^ 2 / Real.pi ^ 3

/-- Isometric embeddings encode arbitrary orthogonal orientation and
cylindrical extension. The permutation encodes relabeling; equality is a.e. -/
def IsTetrahedralFractional {d : ℕ} (F : FractionalPartition d 4) : Prop :=
  ∃ u : Space 3 →ₗᵢ[ℝ] Space d, ∃ sigma : Equiv.Perm (Fin 4),
    ∀ᵐ x ∂gaussian d, ∀ i,
      F.labels i x = (winningCell (fun j => u (tetraVertex (sigma j))) (fun _ => 0) i).indicator
        (fun _ => (1 : ℝ)) x

def IsTetrahedralSet {d : ℕ} (C : SetPartition d 4) : Prop :=
  ∃ u : Space 3 →ₗᵢ[ℝ] Space d, ∃ sigma : Equiv.Perm (Fin 4),
    ∀ᵐ x ∂gaussian d, ∀ i,
      x ∈ C.cells i ↔ x ∈ winningCell (fun j => u (tetraVertex (sigma j))) (fun _ => 0) i

/-- UNPROVED target proposition, not a theorem and not an assumption in the core. -/
def FourCellFractionalTarget : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ F : FractionalPartition d 4,
    (∀ i, F.mass i = 1 / 4) → momentEnergy F ≤ sharpFourConstant ∧
      (momentEnergy F = sharpFourConstant ↔ IsTetrahedralFractional F)

/-- UNPROVED target with the original measurable cells and ENNReal Gaussian masses. -/
def FourCellMeasurableTarget : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ C : SetPartition d 4,
    (∀ i, gaussian d (C.cells i) = 1 / 4) →
      (∑ i, ‖∫ x in C.cells i, x ∂gaussian d‖ ^ 2) ≤ sharpFourConstant ∧
      ((∑ i, ‖∫ x in C.cells i, x ∂gaussian d‖ ^ 2) = sharpFourConstant ↔ IsTetrahedralSet C)

end GaussianFourGlobal
