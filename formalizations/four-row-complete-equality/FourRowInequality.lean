import FourRowLaplace
open scoped BigOperators
namespace FourRowTradeoff
noncomputable section

def rowNorm (a : Row) : ℝ := Real.sqrt (rowSq a)
def rowProduct (A : Mat) : ℝ := ∏ i, rowNorm (A i)

theorem rowNorm_nonneg (a : Row) : 0 ≤ rowNorm a := Real.sqrt_nonneg _
theorem rowNorm_sq (a : Row) : rowNorm a^2 = rowSq a := Real.sq_sqrt (rowSq_nonneg a)
theorem rowNorm_semantics (a : Row) : rowNorm a = Real.sqrt (∑ i, ‖a i‖^2) := by
  simp only [rowNorm, rowSq, normSq_as_sq]
theorem rowProduct_nonneg (A : Mat) : 0 ≤ rowProduct A :=
  Finset.prod_nonneg (fun _i _ => rowNorm_nonneg _)
theorem rowProduct_sq (A : Mat) :
    rowProduct A^2 = rowSq (A 0)*rowSq (A 1)*rowSq (A 2)*rowSq (A 3) := by
  simp [rowProduct, Fin.prod_univ_succ, mul_pow, rowNorm_sq]
  ring

/-- Weighted Cauchy, derived from an explicit square, without division. -/
theorem weighted_sqrt_cauchy (s t u v c : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) (hc : 0 ≤ c) :
    (Real.sqrt (s*t) + c*Real.sqrt (u*v))^2 ≤ (s+c*u)*(t+c*v) := by
  rw [Real.sqrt_mul hs, Real.sqrt_mul hu]
  have hid : (s+c*u)*(t+c*v) -
      (Real.sqrt s*Real.sqrt t+c*(Real.sqrt u*Real.sqrt v))^2 =
      c*(Real.sqrt s*Real.sqrt v-Real.sqrt t*Real.sqrt u)^2 := by
    ring_nf
    simp only [Real.sq_sqrt hs, Real.sq_sqrt ht, Real.sq_sqrt hu, Real.sq_sqrt hv]
    ring
  have h := mul_nonneg hc (sq_nonneg (Real.sqrt s*Real.sqrt v-Real.sqrt t*Real.sqrt u))
  linarith

theorem weighted_laplace_bound (A : Mat) (c : ℝ) (hc : 0 ≤ c) :
    (‖A.permanent‖+c*‖A.det‖)^2 ≤
      (symEnergy (A 0) (A 1)+c*altEnergy (A 0) (A 1))*
      (symEnergy (A 2) (A 3)+c*altEnergy (A 2) (A 3)) := by
  have hs := symEnergy_nonneg (A 0) (A 1)
  have ht := symEnergy_nonneg (A 2) (A 3)
  have hu := altEnergy_nonneg (A 0) (A 1)
  have hv := altEnergy_nonneg (A 2) (A 3)
  have hp := (Real.le_sqrt (norm_nonneg _) (mul_nonneg hs ht)).2 (permanent_sq_bound A)
  have hd := (Real.le_sqrt (norm_nonneg _) (mul_nonneg hu hv)).2 (det_sq_bound A)
  have hb := add_le_add hp (mul_le_mul_of_nonneg_left hd hc)
  have hn : 0 ≤ ‖A.permanent‖+c*‖A.det‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))
  have hn' : 0 ≤ Real.sqrt (symEnergy (A 0) (A 1)*symEnergy (A 2) (A 3))+
      c*Real.sqrt (altEnergy (A 0) (A 1)*altEnergy (A 2) (A 3)) :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))
  exact ((sq_le_sq₀ hn hn').2 hb).trans (weighted_sqrt_cauchy _ _ _ _ c hs ht hu hv hc)

/-- Main sharp inequality, for all actual complex 4-by-4 matrices, including zero rows. -/
theorem matrix_tradeoff (A : Mat) (c : ℝ) (hc : 0 ≤ c) :
    ‖A.permanent‖+c*‖A.det‖ ≤ sharpConstant c*rowProduct A := by
  have h1 := pair_bound (A 0) (A 1) c
  have h2 := pair_bound (A 2) (A 3) c
  have hf2 : 0 ≤ symEnergy (A 2) (A 3)+c*altEnergy (A 2) (A 3) :=
    add_nonneg (symEnergy_nonneg _ _) (mul_nonneg hc (altEnergy_nonneg _ _))
  have hm := sharpConstant_nonneg c
  have hb1 : 0 ≤ sharpConstant c*(rowSq (A 0)*rowSq (A 1)) :=
    mul_nonneg hm (mul_nonneg (rowSq_nonneg _) (rowSq_nonneg _))
  have hb := (weighted_laplace_bound A c hc).trans (mul_le_mul h1 h2 hf2 hb1)
  have he : sharpConstant c*(rowSq (A 0)*rowSq (A 1))*
      (sharpConstant c*(rowSq (A 2)*rowSq (A 3))) =
      (sharpConstant c*rowProduct A)^2 := by
    rw [mul_pow, rowProduct_sq]
    ring
  rw [he] at hb
  exact (sq_le_sq₀ (add_nonneg (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)))
    (mul_nonneg hm (rowProduct_nonneg A))).1 hb

/-- Exact original-object spelling of the sharp inequality. -/
theorem sharp_four_row (A : Matrix (Fin 4) (Fin 4) ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖A.permanent‖+c*‖A.det‖ ≤ max (3/2) (1+c) *
      ∏ i, Real.sqrt (∑ j, ‖A i j‖^2) := by
  simpa only [sharpConstant, rowProduct, rowNorm_semantics] using matrix_tradeoff A c hc

#print axioms sharp_four_row
end
end FourRowTradeoff
