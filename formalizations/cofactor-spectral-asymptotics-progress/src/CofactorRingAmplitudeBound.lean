import CofactorSignedRingCoefficients
import CofactorSubsetEntropy

/-! The actual ring amplitude and its geometric entropy estimate. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section
variable {K : Type*} [Fintype K] [LinearOrder K]

def ringRadius (N : ℕ) (C : ℝ) (d : K → ℕ) (k : K) : ℝ :=
  (N : ℝ)/(2*C*(d k : ℝ))

theorem ringAmplitude_radius (N : ℕ) (C : ℝ) (d : K → ℕ) (s : Finset K) :
    ringAmplitude d (ringRadius N C d) s =
      ((N : ℝ)/(2*C))^(∑ k ∈ s, d k) / (∏ k ∈ s, (d k : ℝ)^(d k)) := by
  have he : ∀ k, ringRadius N C d k = ((N : ℝ)/(2*C))/(d k : ℝ) := by
    intro k
    exact (div_div _ _ _).symm
  unfold ringAmplitude
  simp_rw [he,div_pow]
  rw [Finset.prod_div_distrib,Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum]

theorem ringAmplitude_entropy_bound (N : ℕ) (C b : ℝ) (hC : 0 < C) (hb : 1 < b)
    (d : K → ℕ) (hd : ∀ k, 0 < d k)
    (hsep : ∀ i j, i < j → b*(d i : ℝ) ≤ (d j : ℝ))
    (s : Finset K) (hs : s.Nonempty) :
    ringAmplitude d (ringRadius N C d) s ≤
      ((N : ℝ)*entropyConstant b/(2*C*(∑ k ∈ s, d k : ℕ)))^(∑ k ∈ s, d k) := by
  classical
  let J := ∑ k ∈ s, d k
  let D : ℝ := ∏ k ∈ s, (d k : ℝ)^(d k)
  let M : ℝ := (N : ℝ)/(2*C)
  have hJ : 0 < J := Finset.sum_pos (fun k _ => hd k) hs
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hM : 0 ≤ M := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hsum : (∑ k ∈ s, (d k : ℝ)) = (J : ℝ) := by
    dsimp [J]
    rw [Nat.cast_sum]
  have he := geometric_subset_product_bound b hb (fun k => (d k : ℝ))
    (fun k => by exact_mod_cast hd k) hsep s hs
  have hE : (J : ℝ)^J/D ≤ (entropyConstant b)^J := by
    simpa only [hsum,Real.rpow_natCast,D] using he
  have hscaled := mul_le_mul_of_nonneg_left hE
    (pow_nonneg (div_nonneg hM hJr.le) J)
  have hl : (M/(J : ℝ))^J*((J : ℝ)^J/D) = M^J/D := by
    rw [div_pow]
    field_simp [pow_ne_zero J hJr.ne']
  have hr : (M/(J : ℝ))^J*(entropyConstant b)^J =
      ((N : ℝ)*entropyConstant b/(2*C*(J : ℝ)))^J := by
    rw [← mul_pow]
    congr 1
    dsimp [M]
    field_simp
  rw [hl,hr] at hscaled
  rw [ringAmplitude_radius]
  exact hscaled

end
end CofactorSpectral
