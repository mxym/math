import HydrologyTree.StieltjesReindex

/-! Exact regrouping of poles into arbitrary labelled child families. No
cross-cancellation or approximate partial fractions are used. -/
open Polynomial
noncomputable section
namespace HydrologyTree

variable {B : Type*} [Fintype B] [DecidableEq B] (m : B → ℕ)

lemma stieltjesDenominator_sigma (b : (Σ c, Fin (m c+1)) → ℝ) :
    stieltjesDenominator b = ∏ c, stieltjesDenominator (fun i => b ⟨c,i⟩) := by
  exact Fintype.prod_sigma _

lemma stieltjes_sigma_erased_product (b : (Σ c, Fin (m c+1)) → ℝ)
    (c : B) (i : Fin (m c+1)) :
    (∏ v ∈ Finset.univ.erase ⟨c,i⟩, (X+C (b v))) =
      (∏ j ∈ Finset.univ.erase i, (X+C (b ⟨c,j⟩))) *
        ∏ d ∈ Finset.univ.erase c, stieltjesDenominator (fun j => b ⟨d,j⟩) := by
  apply mul_left_cancel₀ (Polynomial.monic_X_add_C (b ⟨c,i⟩)).ne_zero
  rw [Finset.mul_prod_erase Finset.univ
    (fun v : Σ c, Fin (m c+1) => (X+C (b v) : ℝ[X])) (Finset.mem_univ ⟨c,i⟩)]
  rw [← mul_assoc,Finset.mul_prod_erase Finset.univ
    (fun j : Fin (m c+1) => (X+C (b ⟨c,j⟩) : ℝ[X])) (Finset.mem_univ i)]
  change stieltjesDenominator b = stieltjesDenominator (fun j => b ⟨c,j⟩) * _
  rw [stieltjesDenominator_sigma,Finset.mul_prod_erase Finset.univ
    (fun d => stieltjesDenominator (fun j : Fin (m d+1) => b ⟨d,j⟩)) (Finset.mem_univ c)]

/-- Numerator regrouping at polynomial level, including coincident poles. -/
theorem stieltjesNumerator_sigma (b g : (Σ c, Fin (m c+1)) → ℝ) :
    stieltjesNumerator b g =
      ∑ c, stieltjesNumerator (fun i => b ⟨c,i⟩) (fun i => g ⟨c,i⟩) *
        ∏ d ∈ Finset.univ.erase c, stieltjesDenominator (fun i => b ⟨d,i⟩) := by
  rw [stieltjesNumerator,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [stieltjesNumerator,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [stieltjes_sigma_erased_product]
  ring

lemma stieltjesNumerator_scale {I : Type*} [Fintype I] [DecidableEq I]
    (b g : I → ℝ) (k : ℝ) :
    stieltjesNumerator b (fun i => k*g i) = C k * stieltjesNumerator b g := by
  simp only [stieltjesNumerator,map_mul,Finset.mul_sum,mul_assoc]

lemma stieltjesNumerator_normalization {I : Type*} [Fintype I] [DecidableEq I]
    (b g : I → ℝ) (k : ℝ) (hk : k ≠ 0) :
    C k * stieltjesNumerator b (fun i => g i/k) = stieltjesNumerator b g := by
  rw [← stieltjesNumerator_scale]
  congr 1
  funext i
  exact mul_div_cancel₀ (g i) hk

end HydrologyTree
