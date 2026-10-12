import GaussianBalancedValue

/-! Exact homogeneity of the actual balanced Gaussian assignment value,
including zero scale and coincident score vectors. -/
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace GaussianFourGlobal
open GaussianMeasureBridge

lemma scoreMax_scale_nonneg {d : ℕ} (v : Fin 4 → Space d) (b : Fin 4 → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (x : Space d) :
    scoreMax (fun i => c • v i) (fun i => c * b i) x = c * scoreMax v b x := by
  obtain ⟨r, hr⟩ := Finite.exists_max (fun i : Fin 4 => ⟪v i, x⟫ - b i)
  have he : scoreMax v b x = ⟪v r, x⟫ - b r := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun i _ => hr i
    · exact le_scoreMax v b x r
  rw [he]
  apply le_antisymm
  · unfold scoreMax
    apply Finset.sup'_le
    intro i _
    simp only [real_inner_smul_left, ← mul_sub]
    exact mul_le_mul_of_nonneg_left (hr i) hc
  · simpa only [real_inner_smul_left, ← mul_sub] using
      le_scoreMax (fun i => c • v i) (fun i => c * b i) x r

lemma priceObjective_scale_nonneg {d : ℕ} (v : Fin 4 → Space d) (b : Fin 4 → ℝ)
    (c : ℝ) (hc : 0 ≤ c) :
    priceObjective (fun i => c • v i) (fun _ => 1 / 4) (fun i => c * b i) =
      c * priceObjective v (fun _ => 1 / 4) b := by
  unfold priceObjective expectedScore
  simp_rw [scoreMax_scale_nonneg v b c hc]
  rw [integral_const_mul]
  simp_rw [mul_left_comm (1 / 4 : ℝ) c]
  rw [← Finset.mul_sum]
  ring

lemma balancedValue_zero (d : ℕ) : balancedValue (0 : Fin 4 → Space d) = 0 := by
  apply le_antisymm
  · have h := balancedValue_le_price (0 : Fin 4 → Space d) 0
    simpa only [priceObjective, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero, expectedScore_zero_zero] using h
  · exact balancedValue_nonneg 0

/-- The balanced value is positively homogeneous in actual score vectors. -/
theorem balancedValue_pos_scale {d : ℕ} (v : Fin 4 → Space d) (c : ℝ) (hc : 0 < c) :
    balancedValue (fun i => c • v i) = c * balancedValue v := by
  obtain ⟨a, ha, _⟩ := balancedValue_attained v
  obtain ⟨b, hb, _⟩ := balancedValue_attained (fun i => c • v i)
  have hu := balancedValue_le_price (fun i => c • v i) (fun i => c * a i)
  rw [priceObjective_scale_nonneg v a c hc.le, ← ha] at hu
  have hdiv : (fun i => c * (b i / c)) = b := by
    funext i
    field_simp
  have he := priceObjective_scale_nonneg v (fun i => b i / c) c hc.le
  rw [hdiv] at he
  have hl := mul_le_mul_of_nonneg_left (balancedValue_le_price v (fun i => b i / c)) hc.le
  rw [← he, ← hb] at hl
  exact le_antisymm hu hl

/-- Nonnegative scaling, with the degenerate zero-scale endpoint checked. -/
theorem balancedValue_scale_nonneg {d : ℕ} (v : Fin 4 → Space d) (c : ℝ) (hc : 0 ≤ c) :
    balancedValue (fun i => c • v i) = c * balancedValue v := by
  rcases eq_or_lt_of_le hc with hz | hp
  · subst c
    simp only [zero_smul, zero_mul]
    change balancedValue (0 : Fin 4 → Space d) = 0
    exact balancedValue_zero d
  · exact balancedValue_pos_scale v c hp

end GaussianFourGlobal