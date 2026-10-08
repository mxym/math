import EntropyWakhare.Signs
import EntropyWakhare.Alpha
import Mathlib.Tactic.FunProp

set_option maxHeartbeats 2000000

namespace EntropyRoot

/-- Exact real version of Wakhare's defining double binomial sum h_{11,s}. -/
def hReal (s : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 11, x^(s*j) * (innerCoeff s j : ℝ)

def AReal (x : ℝ) : ℝ := 11*(1-x^10)^11*hReal 11 x
def BReal (x : ℝ) : ℝ := 10*(1-x^11)^11*hReal 10 x

/-- This is precisely p_{11,10}(x) with the unique positive alpha from the paper. -/
noncomputable def entropyPolynomial (x : ℝ) : ℝ :=
  alpha*AReal x - BReal x

theorem hReal_at_rat (s : ℕ) (x : ℚ) :
    hReal s (x : ℝ) = (hRat s x : ℝ) := by
  classical
  have hcast (t : Finset ℕ) :
      (∑ j ∈ t, (x : ℝ)^(s*j) * (innerCoeff s j : ℝ)) =
        ((∑ j ∈ t, x^(s*j) * innerCoeff s j : ℚ) : ℝ) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        simp only [Finset.sum_insert ha]
        simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow] using
          congrArg (fun y : ℝ => (x : ℝ)^(s*a) * (innerCoeff s a : ℝ) + y) ih
  exact hcast (Finset.range 11)

theorem AReal_at_rat (x : ℚ) : AReal (x : ℝ) = (A x : ℝ) := by
  simp [AReal, A, hReal_at_rat]

theorem BReal_at_rat (x : ℚ) : BReal (x : ℝ) = (B x : ℝ) := by
  simp [BReal, B, hReal_at_rat]

theorem entropyPolynomial_continuous : Continuous entropyPolynomial := by
  unfold entropyPolynomial AReal BReal hReal
  fun_prop

private theorem entropyPositive_of_rat (x : ℚ)
    (hA : 0 < A x) (hB : B x < (117/125 : ℚ)*A x) :
    0 < entropyPolynomial (x : ℝ) := by
  have hpos : (0 : ℝ) < (A x : ℝ) := by exact_mod_cast hA
  have hc : (B x : ℝ) < (((117/125 : ℚ)*A x : ℚ) : ℝ) := by
    exact_mod_cast hB
  have hbr : (B x : ℝ) < (117/125 : ℝ) * (A x : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using hc
  have hlt : (117/125 : ℝ) * (A x : ℝ) < alpha*(A x : ℝ) :=
    mul_lt_mul_of_pos_right alpha_interval.1 hpos
  rw [entropyPolynomial, AReal_at_rat, BReal_at_rat]
  linarith

private theorem entropyNegative_of_rat (x : ℚ)
    (hA : 0 < A x) (hB : (937/1000 : ℚ)*A x < B x) :
    entropyPolynomial (x : ℝ) < 0 := by
  have hpos : (0 : ℝ) < (A x : ℝ) := by exact_mod_cast hA
  have hc : (((937/1000 : ℚ)*A x : ℚ) : ℝ) < (B x : ℝ) := by
    exact_mod_cast hB
  have hbr : (937/1000 : ℝ) * (A x : ℝ) < (B x : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using hc
  have hlt : alpha*(A x : ℝ) < (937/1000 : ℝ)*(A x : ℝ) :=
    mul_lt_mul_of_pos_right alpha_interval.2.1 hpos
  rw [entropyPolynomial, AReal_at_rat, BReal_at_rat]
  linarith

theorem sample1_positive : 0 < entropyPolynomial ((1/5 : ℚ) : ℝ) :=
  entropyPositive_of_rat (1/5) p1pos p1bound
theorem sample2_negative : entropyPolynomial ((2/5 : ℚ) : ℝ) < 0 :=
  entropyNegative_of_rat (2/5) p2pos p2bound
theorem sample3_positive : 0 < entropyPolynomial ((3/5 : ℚ) : ℝ) :=
  entropyPositive_of_rat (3/5) p3pos p3bound
theorem sample4_negative : entropyPolynomial ((2/3 : ℚ) : ℝ) < 0 :=
  entropyNegative_of_rat (2/3) p4pos p4bound
theorem sample5_positive : 0 < entropyPolynomial ((4/5 : ℚ) : ℝ) :=
  entropyPositive_of_rat (4/5) p5pos p5bound

private theorem zero_between (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) (hab : a < b) (ha : f a < 0) (hb : 0 < f b) :
    ∃ z : ℝ, a < z ∧ z < b ∧ f z = 0 := by
  have hlow : a ∈ Set.Icc a b := ⟨le_rfl, le_of_lt hab⟩
  have hhigh : b ∈ Set.Icc a b := ⟨le_of_lt hab, le_rfl⟩
  obtain ⟨z,hz,he⟩ :=
    (isPreconnected_Icc).intermediate_value₂ hlow hhigh
      hf.continuousOn continuousOn_const
      (le_of_lt ha) (le_of_lt hb)
  rcases hz with ⟨hlo,hhi⟩
  have hstrictLow : a < z := by
    rcases lt_or_eq_of_le hlo with h | h
    · exact h
    · rw [←h] at he
      linarith
  have hstrictHigh : z < b := by
    rcases lt_or_eq_of_le hhi with h | h
    · exact h
    · rw [h] at he
      linarith
  exact ⟨z,hstrictLow,hstrictHigh,he⟩

theorem four_distinct_interior_roots :
    ∃ z₁ z₂ z₃ z₄ : ℝ,
      0 < z₁ ∧ z₁ < z₂ ∧ z₂ < z₃ ∧ z₃ < z₄ ∧ z₄ < 1 ∧
      entropyPolynomial z₁ = 0 ∧ entropyPolynomial z₂ = 0 ∧
      entropyPolynomial z₃ = 0 ∧ entropyPolynomial z₄ = 0 := by
  obtain ⟨z₁,h1l,h1r,h1z⟩ :=
    zero_between (fun x => -entropyPolynomial x) entropyPolynomial_continuous.neg
      ((1/5 : ℚ) : ℝ) ((2/5 : ℚ) : ℝ) (by norm_num)
      (by linarith [sample1_positive]) (by linarith [sample2_negative])
  obtain ⟨z₂,h2l,h2r,h2z⟩ :=
    zero_between entropyPolynomial entropyPolynomial_continuous
      ((2/5 : ℚ) : ℝ) ((3/5 : ℚ) : ℝ) (by norm_num) sample2_negative sample3_positive
  obtain ⟨z₃,h3l,h3r,h3z⟩ :=
    zero_between (fun x => -entropyPolynomial x) entropyPolynomial_continuous.neg
      ((3/5 : ℚ) : ℝ) ((2/3 : ℚ) : ℝ) (by norm_num)
      (by linarith [sample3_positive]) (by linarith [sample4_negative])
  obtain ⟨z₄,h4l,h4r,h4z⟩ :=
    zero_between entropyPolynomial entropyPolynomial_continuous
      ((2/3 : ℚ) : ℝ) ((4/5 : ℚ) : ℝ) (by norm_num) sample4_negative sample5_positive
  refine ⟨z₁,z₂,z₃,z₄,?_,?_,?_,?_,?_,?_,h2z,?_,h4z⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith


/-- The witness parameters satisfy the usual admissibility and coprimality. -/
theorem witness_parameters_admissible :
    0 < (10 : ℕ) ∧ 10 < 11 ∧ Nat.Coprime 11 10 := by
  constructor
  · norm_num
  constructor
  · norm_num
  · decide

end EntropyRoot
