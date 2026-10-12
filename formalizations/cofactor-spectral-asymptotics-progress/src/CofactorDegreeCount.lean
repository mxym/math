import CofactorDegreeSequence

/-! An explicit logarithmic number of rings fits in every sufficiently large dimension. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

def degreeBudget (b : ℝ) (m : ℕ) : ℝ := ((m : ℝ)+1/(b-1))/(b-1)
def degreeLogOffset (b : ℝ) (m : ℕ) (δ : ℝ) : ℝ := Real.log (2*degreeBudget b m/δ)/Real.log b
def degreeCount (b : ℝ) (m : ℕ) (δ : ℝ) (N : ℕ) : ℕ :=
  Nat.floor (Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ)

theorem degreeBudget_pos (b : ℝ) (hb : 1 < b) (m : ℕ) : 0 < degreeBudget b m := by
  have hb1 : 0 < b-1 := sub_pos.mpr hb
  unfold degreeBudget
  positivity

theorem degreeCount_power_bound (b : ℝ) (hb : 1 < b) (m N : ℕ)
    (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ)
    (hx : 0 ≤ Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ) :
    b^(degreeCount b m δ N) ≤ δ*(N : ℝ)/(2*degreeBudget b m) := by
  have hb0 : 0 < b := by linarith
  have hl : 0 < Real.log b := Real.log_pos hb
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hT := degreeBudget_pos b hb m
  have hfloor := Nat.floor_le hx
  change (degreeCount b m δ N : ℝ) ≤ Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ at hfloor
  have ht := mul_le_mul_of_nonneg_right hfloor hl.le
  have he : (Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ)*Real.log b =
      Real.log (N : ℝ)-degreeLogOffset b m δ*Real.log b := by field_simp
  rw [he] at ht
  have hoff : degreeLogOffset b m δ*Real.log b = Real.log (2*degreeBudget b m/δ) := by
    unfold degreeLogOffset
    exact div_mul_cancel₀ _ hl.ne'
  have heLog : Real.log (δ*(N : ℝ)/(2*degreeBudget b m)) =
      Real.log (N : ℝ)-degreeLogOffset b m δ*Real.log b := by
    rw [hoff,Real.log_div (mul_pos hδ hNr).ne' (by positivity),
      Real.log_mul hδ.ne' hNr.ne',Real.log_div (by positivity) hδ.ne']
    ring
  apply (Real.log_le_log_iff (pow_pos hb0 _) (div_pos (mul_pos hδ hNr) (by positivity))).mp
  rw [Real.log_pow,heLog]
  exact ht

theorem degreeCount_prefix_budget (b : ℝ) (hb : 1 < b) (m : ℕ) (hm : 0 < m)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ)
    (hx : 0 ≤ Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ) :
    2*((∑ k ∈ Finset.range (degreeCount b m δ N), ringDegreeSequence b m k : ℕ) : ℝ) ≤
      δ*(N : ℝ) := by
  have hT := degreeBudget_pos b hb m
  have hp := ringDegreeSequence_prefix_upper b hb m hm (degreeCount b m δ N)
  change ((∑ k ∈ Finset.range (degreeCount b m δ N), ringDegreeSequence b m k : ℕ) : ℝ) ≤
    degreeBudget b m*b^(degreeCount b m δ N) at hp
  have hpower := degreeCount_power_bound b hb m N hN δ hδ hx
  have hmul := mul_le_mul_of_nonneg_left hpower hT.le
  have he : degreeBudget b m*(δ*(N : ℝ)/(2*degreeBudget b m)) = δ*(N : ℝ)/2 := by
    field_simp
  rw [he] at hmul
  linarith

theorem degreeCount_positive (b : ℝ) (m N : ℕ) (δ : ℝ)
    (hx : 1 ≤ Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ) :
    0 < degreeCount b m δ N := by
  have h : 1 ≤ degreeCount b m δ N := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  omega

theorem degreeCount_lower (b : ℝ) (m N : ℕ) (δ : ℝ) :
    Real.log (N : ℝ)/Real.log b-degreeLogOffset b m δ-1 < (degreeCount b m δ N : ℝ) :=
  Nat.sub_one_lt_floor _

end
end CofactorSpectral
