import BapatSphereFischer
import BapatAsymptotic

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Metric
open BapatFiniteRank BapatRankTwo.MarkedInversions

namespace BapatRealExistence
noncomputable section

abbrev ComplexUnitSphere4 := sphere (0 : EuclideanSpace ℂ (Fin 4)) 1

def rowProductModulus {n : ℕ} (v : Fin n → Fin 4 → ℝ) (z : ComplexUnitSphere4) : ℝ :=
  ‖complexEval (formsProduct v) z‖

def rowWedgeEnergy {n : ℕ} (v : Fin n → Fin 4 → ℝ) (z : ComplexUnitSphere4) : ℝ :=
  ∑ c ∈ originalPairs (ι := Fin 4), ‖complexEval (wedgePolynomial v c.1 c.2) z‖^2

@[fun_prop] theorem rowProductModulus_continuous {n : ℕ} (v : Fin n → Fin 4 → ℝ) :
    Continuous (rowProductModulus v) := by unfold rowProductModulus; fun_prop

@[fun_prop] theorem rowWedgeEnergy_continuous {n : ℕ} (v : Fin n → Fin 4 → ℝ) :
    Continuous (rowWedgeEnergy v) := by unfold rowWedgeEnergy; fun_prop

theorem repeated_fischer_denominator {n : ℕ} (v : Fin n → Fin 4 → ℝ) (L : ℕ) :
    fischerNormSq ((formsProduct v)^L) = ((n*L+3).factorial : ℝ) / 6 *
      ∫ z : ComplexUnitSphere4, (rowProductModulus v z)^(2*L)
        ∂normalizedSphere (complexProductHaar (Fin 4)) := by
  have hp : ((formsProduct v)^L).IsHomogeneous (n*L) := by
    simpa using (formsProduct_isHomogeneous v).pow L
  rw [rank_four_fischer_norm _ _ hp]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp only [complexEval_pow, norm_pow, rowProductModulus, ← pow_mul]
  rw [Nat.mul_comm L 2]

theorem repeated_fischer_numerator {n L : ℕ} (v : Fin n → Fin 4 → ℝ)
    (hn : 2 ≤ n) (hL : 0 < L) :
    (∑ c ∈ originalPairs (ι := Fin 4),
      fischerNormSq ((formsProduct v)^(L-1) * wedgePolynomial v c.1 c.2)) =
      ((n*L+1).factorial : ℝ) / 6 *
        ∫ z : ComplexUnitSphere4, (rowProductModulus v z)^(2*L-2) * rowWedgeEnergy v z
          ∂normalizedSphere (complexProductHaar (Fin 4)) := by
  have hnL : 2 ≤ n*L := le_trans hn (Nat.le_mul_of_pos_right _ hL)
  have hi (c : Fin 4 × Fin 4) : Integrable (fun z : ComplexUnitSphere4 =>
      (rowProductModulus v z)^(2*L-2) * ‖complexEval (wedgePolynomial v c.1 c.2) z‖^2)
        (normalizedSphere (complexProductHaar (Fin 4))) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  simp only [rowWedgeEnergy, Finset.mul_sum]
  rw [integral_finsetSum _ (fun c _ => hi c), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hp := power_wedge_isHomogeneous v (by simpa using hn) hL c.1 c.2
  rw [rank_four_fischer_norm _ _ hp]
  simp only [Fintype.card_fin] at *
  rw [show n*L-2+3 = n*L+1 by omega]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp only [complexEval_mul, complexEval_pow, norm_mul, norm_pow, mul_pow,
    rowProductModulus, ← pow_mul]
  rw [show (L-1)*2 = 2*L-2 by omega]

/-- Endpoint derivative after actual contiguous repetition, expressed by sphere integrals. -/
theorem real_contiguous_sphere_endpoint {n L : ℕ} (v : Fin n → Fin 4 → ℝ)
    (hn : 2 ≤ n) (hL : 0 < L) :
    2 * (qPolynomial (gram (contiguousRows v L))).derivative.eval 1 =
      ((n*L).choose 2 : ℝ) * (((n*L+3).factorial : ℝ) / 6) *
        (∫ z : ComplexUnitSphere4, (rowProductModulus v z)^(2*L)
          ∂normalizedSphere (complexProductHaar (Fin 4))) -
      (L : ℝ)^4 * (((n*L+1).factorial : ℝ) / 6) *
        (∫ z : ComplexUnitSphere4, (rowProductModulus v z)^(2*L-2) * rowWedgeEnergy v z
          ∂normalizedSphere (complexProductHaar (Fin 4))) := by
  rw [real_contiguous_endpoint v hL, repeated_fischer_denominator v L,
    repeated_fischer_numerator v hn hL]
  ring

end
end BapatRealExistence
