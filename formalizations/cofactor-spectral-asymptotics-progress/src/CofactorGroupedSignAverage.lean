import CofactorSignSquareAverage

/-! Exact weighted averaging after grouping sign products by any finite degree map. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]

def groupedSignCombination (a : Finset V → ℝ) (degree : Finset V → K)
    (k : K) (ε : V → Bool) : ℝ :=
  signCombination (fun s => if degree s = k then a s else 0) ε

theorem groupedSignCombination_square_sum (a : Finset V → ℝ) (degree : Finset V → K)
    (q : K → ℝ) :
    (∑ ε : V → Bool, ∑ k : K, q k * groupedSignCombination a degree k ε ^ 2) =
      (2 : ℝ)^Fintype.card V * ∑ s : Finset V, q (degree s) * a s ^ 2 := by
  classical
  rw [Finset.sum_comm]
  simp only [groupedSignCombination,← Finset.mul_sum,signCombination_square_sum]
  have ht : ∀ k, q k * ((2 : ℝ)^Fintype.card V *
      ∑ s : Finset V, (if degree s = k then a s else 0)^2) =
      (2 : ℝ)^Fintype.card V * ∑ s : Finset V,
        if degree s = k then q k * a s^2 else 0 := by
    intro k
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : degree s = k <;> simp [h] <;> ring
  simp_rw [ht]
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp

theorem groupedSignCombination_square_average (a : Finset V → ℝ)
    (degree : Finset V → K) (q : K → ℝ) :
    (∑ ε : V → Bool, ∑ k : K, q k * groupedSignCombination a degree k ε ^ 2) /
      (2 : ℝ)^Fintype.card V = ∑ s : Finset V, q (degree s) * a s ^ 2 := by
  rw [groupedSignCombination_square_sum]
  field_simp

theorem groupedSignCombination_has_small_choice (a : Finset V → ℝ)
    (degree : Finset V → K) (q : K → ℝ) :
    ∃ ε : V → Bool, (∑ k : K, q k * groupedSignCombination a degree k ε ^ 2) ≤
      ∑ s : Finset V, q (degree s) * a s ^ 2 := by
  apply finite_average_has_small_choice
  have h := groupedSignCombination_square_average a degree q
  have hc : (Fintype.card (V → Bool) : ℝ) = (2 : ℝ)^Fintype.card V := by
    simp
  rw [hc]
  exact h.le

end
end CofactorSpectral
