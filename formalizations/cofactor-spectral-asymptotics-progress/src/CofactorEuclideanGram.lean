import CofactorGramPSD
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual Gram matrices are realized as Euclidean feature vectors. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def gramFeature (v : V → C → ℂ) (i : V) : EuclideanSpace ℂ C :=
  WithLp.toLp 2 (fun c => star (v i c))

theorem gramFeature_inner (v : V → C → ℂ) (i j : V) :
    inner ℂ (gramFeature v i) (gramFeature v j) = complexGram v i j := by
  rw [gramFeature,gramFeature,EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct,complexGram,mul_comm]

theorem gramFeature_sum_norm_sq (v : V → C → ℂ) (s : Finset V) :
    ‖∑ i ∈ s, gramFeature v i‖^2 = (∑ i ∈ s, ∑ j ∈ s, complexGram v i j).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp_rw [sum_inner,inner_sum,gramFeature_inner]
  rfl

theorem gramFeature_weighted_norm_sq (v : V → C → ℂ) (w : V → ℂ) :
    ‖∑ i, w i • gramFeature v i‖^2 =
      (∑ i, ∑ j, star (w i) * complexGram v i j * w j).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp_rw [sum_inner,inner_sum,inner_smul_left,inner_smul_right,gramFeature_inner]
  change Complex.re _ = Complex.re _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.star_def]
  ring

theorem gramFeature_real_weighted_norm_sq (v : V → C → ℂ) (x : V → ℝ) :
    ‖∑ i, x i • gramFeature v i‖^2 =
      (∑ i, ∑ j, (x i : ℂ) * complexGram v i j * (x j : ℂ)).re := by
  have h := gramFeature_weighted_norm_sq v (fun i => (x i : ℂ))
  have hs : ∀ i, (x i : ℂ) • gramFeature v i = x i • gramFeature v i :=
    fun i => IsScalarTower.algebraMap_smul ℂ (x i) (gramFeature v i)
  simp_rw [hs] at h
  simpa only [Complex.star_def,Complex.conj_ofReal] using h

end
end CofactorSpectral
