import GaussianWinningGraphFlux
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! A coordinate direction strictly positive on every vector of a normal
basis exists by Riesz representation. A Householder reflection makes it the
first coordinate. This removes the coordinate choice from simplicial flux. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

lemma basis_inner_interpolate {n : ℕ} (B : Basis (Fin n) ℝ (Space n)) (c : Fin n → ℝ) :
    ∃ u : Space n, ∀ i, ⟪u, B i⟫ = c i := by
  let L : StrongDual ℝ (Space n) := (B.constr ℝ c).toContinuousLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ (Space n)).symm L, ?_⟩
  intro i
  rw [InnerProductSpace.toDual_symm_apply]
  exact B.constr_basis ℝ c i

/-- All inward normals of a simplicial cone can simultaneously have strictly
positive first coordinate after an actual orthogonal change of coordinates. -/
theorem basis_positive_first_coordinates (B : Basis (Fin (d+1)) ℝ (Space (d+1))) :
    ∃ T : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1), ∀ i, 0 < T (B i) 0 := by
  obtain ⟨u, hu⟩ := basis_inner_interpolate B (fun _ => 1)
  have hune : u ≠ 0 := by
    intro h
    have he := hu 0
    rw [h, inner_zero_left] at he
    norm_num at he
  let z : Space (d+1) := ‖u‖⁻¹ • u
  let e : Space (d+1) := EuclideanSpace.basisFun (Fin (d+1)) ℝ 0
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hune
  have hz : ‖z‖ = 1 := by
    simp [z, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),
      inv_mul_cancel₀ hn]
  have he : ‖e‖ = 1 := by simp [e]
  let T : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1) := (ℝ ∙ (z-e))ᗮ.reflection
  have hT : T z = e := Submodule.reflection_sub (hz.trans he.symm)
  have hcoord (x : Space (d+1)) : ⟪e,x⟫ = x 0 := by simp [e, PiLp.inner_apply]
  refine ⟨T, fun i => ?_⟩
  have hi : T (B i) 0 = ‖u‖⁻¹ := by
    rw [← hcoord, ← hT, T.inner_map_map]
    simp [z, real_inner_smul_left, hu i]
  rw [hi]
  exact inv_pos.mpr (norm_pos_iff.mpr hune)

lemma winningGraphSlopes_injective_of_basis
    (v : Fin (k+1) → Space (d+1)) (B : Basis (Fin k) ℝ (Space (d+1)))
    (hB : ∀ i, B i = v 0 - v i.succ) (hv : ∀ i, 0 < inwardCoordinate v i) :
    Function.Injective (winningGraphSlopes v) := by
  intro i j hij
  by_contra hne
  have he := congrArg (fun x : Space d => joinCoordinate 1 (-x)) hij
  rw [winning_graph_normal v i (hv i), winning_graph_normal v j (hv j),
    ← hB i, ← hB j] at he
  have hr := congrArg (fun x : Space (d+1) => B.repr x i) he
  have hz : (inwardCoordinate v i)⁻¹ = 0 := by
    simpa [hne, Ne.symm hne] using hr
  exact inv_ne_zero (hv i).ne' hz

/-- This selects coordinates and the distinct exposed graph slopes for every
full normal basis. The basis hypothesis is the actual nondegeneracy condition
of a full-dimensional simplicial winning cell. -/
theorem simplicial_winning_graph_coordinates
    (v : Fin (d+2) → Space (d+1)) (B : Basis (Fin (d+1)) ℝ (Space (d+1)))
    (hB : ∀ i, B i = v 0 - v i.succ) :
    ∃ T : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1),
      (∀ i, 0 < inwardCoordinate (fun j => T (v j)) i) ∧
      Function.Injective (winningGraphSlopes (fun j => T (v j))) := by
  obtain ⟨T, hT⟩ := basis_positive_first_coordinates B
  have hp (i : Fin (d+1)) : 0 < inwardCoordinate (fun j => T (v j)) i := by
    have hh := hT i
    rw [hB i, map_sub] at hh
    exact hh
  refine ⟨T, hp, ?_⟩
  exact winningGraphSlopes_injective_of_basis _ (B.map T.toLinearEquiv)
    (fun i => by simp [hB i]) hp

end GaussianMeasureBridge
