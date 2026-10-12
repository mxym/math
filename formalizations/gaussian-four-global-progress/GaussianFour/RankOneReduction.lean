import GaussianCovarianceValue
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace MatrixOrder Matrix

namespace GaussianFour
open GaussianMeasureBridge

/-- The rank of an actual Gaussian score Gram matrix is the dimension of the
span of its score rows. The conversion through WithLp is explicit; no
finite-dimensional rank is hidden in the statement. -/
lemma scoreGram_rank_eq_span_rows {d k : ℕ} (v : Fin k → Space d) :
    (scoreGram v).rank = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := by
  let A : Matrix (Fin k) (Fin d) ℝ := fun i j => v i j
  have hgram : scoreGram v = A * Aᵀ := by
    ext i j
    rw [Matrix.mul_apply]
    simp [scoreGram, A, PiLp.inner_apply, Matrix.transpose, mul_comm]
  rw [hgram, Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_row]
  let e : Space d ≃ₗ[ℝ] (Fin d → ℝ) := WithLp.linearEquiv 2 ℝ (Fin d → ℝ)
  have himage : e '' (Set.range v) = Set.range (fun i => A.row i) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      ext j
      rfl
    · rintro ⟨i, rfl⟩
      refine ⟨v i, ⟨i, rfl⟩, ?_⟩
      ext j
      rfl
  have hmap :
      (Submodule.span ℝ (Set.range v)).map (e : Space d →ₗ[ℝ] (Fin d → ℝ)) =
        Submodule.span ℝ (Set.range (fun i => A.row i)) := by
    rw [Submodule.map_span]
    exact congrArg (Submodule.span ℝ) himage
  calc
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i => A.row i))) =
        Module.finrank ℝ ((Submodule.span ℝ (Set.range v)).map
          (e : Space d →ₗ[ℝ] (Fin d → ℝ))) := by rw [hmap]
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) :=
      LinearEquiv.finrank_map_eq e _

/-- A positive-semidefinite score Gram matrix of rank at most one has
collinear score rows. -/
theorem scoreGram_rank_le_one_collinear {d k : ℕ} (v : Fin k → Space d)
    (h : (scoreGram v).rank ≤ 1) :
    ∃ u : Space d, ∀ i, ∃ a : ℝ, v i = a • u := by
  have hs : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ 1 := by
    rw [← scoreGram_rank_eq_span_rows v]
    exact h
  let W : Submodule ℝ (Space d) := Submodule.span ℝ (Set.range v)
  have hW : Module.finrank ℝ W ≤ 1 := hs
  letI : W.IsPrincipal := (Submodule.finrank_le_one_iff_isPrincipal W).1 hW
  let u : Space d := Submodule.IsPrincipal.generator W
  have hgen : W ≤ Submodule.span ℝ {u} := by
    rw [Submodule.IsPrincipal.span_singleton_generator]
  refine ⟨u, fun i => ?_⟩
  have hi : v i ∈ W := Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton.mp (hgen hi))
  refine ⟨a, ?_⟩
  exact ha.symm

end GaussianFour
