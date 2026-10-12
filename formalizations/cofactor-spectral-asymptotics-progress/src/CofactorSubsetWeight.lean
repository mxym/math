import CofactorRingAmplitudeBound
import CofactorBinomialEstimate

/-! The actual nonempty subset weight is bounded by the summable geometric weight. -/
set_option autoImplicit false
open scoped BigOperators
namespace CofactorSpectral
noncomputable section

theorem amplitude_binomial_weight (N J : ℕ) (hN : 0 < N) (hJ : 0 < J)
    (C E δ a : ℝ) (hC : 0 < C) (hE : 0 ≤ E) (hδ : δ < 1) (ha : 0 ≤ a)
    (hamp : a ≤ ((N : ℝ)*E/(2*C*(J : ℝ)))^J)
    (hJN : 2*J ≤ N) (hfrac : (2*J : ℕ) ≤ δ*(N : ℝ)) :
    a^2/(N.choose (2*J) : ℝ) ≤
      2*Real.exp 1*(J : ℝ)*(E/(C*Real.exp 1*(1-δ)))^(2*J) := by
  let B : ℝ := (N : ℝ)*E/(2*C*(J : ℝ))
  let D : ℝ := (N : ℝ)*(1-δ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 < D := mul_pos hNr (sub_pos.mpr hδ)
  have hfacpos : (0 : ℝ) < ((2*J).factorial : ℝ) := by positivity
  have hchoose : (0 : ℝ) < (N.choose (2*J) : ℝ) := by
    exact_mod_cast Nat.choose_pos hJN
  have hbin := binomial_lower N (2*J) δ hδ hJN hfrac
  have hsquare : a^2 ≤ B^(2*J) := by
    calc
      _ ≤ (B^J)^2 := pow_le_pow_left₀ ha hamp 2
      _ = _ := by rw [← pow_mul,mul_comm J 2]
  have hfac : ((2*J).factorial : ℝ) ≤
      Real.exp 1*((2*J : ℕ) : ℝ)*(((2*J : ℕ) : ℝ)/Real.exp 1)^(2*J) := by
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2*J ≠ 0)
    rw [hm]
    simpa only [Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using factorial_upper m
  have he : B*(((2*J : ℕ) : ℝ)/Real.exp 1)/D = E/(C*Real.exp 1*(1-δ)) := by
    dsimp [B,D]
    push_cast
    field_simp [hNr.ne',hC.ne',hJr.ne',Real.exp_ne_zero,ne_of_gt (sub_pos.mpr hδ)]
    <;> ring
  calc
    _ ≤ B^(2*J)/(N.choose (2*J) : ℝ) :=
      div_le_div_of_nonneg_right hsquare hchoose.le
    _ ≤ B^(2*J)/(D^(2*J)/((2*J).factorial : ℝ)) :=
      div_le_div_of_nonneg_left (pow_nonneg hB _) (div_pos (pow_pos hD _) hfacpos) hbin
    _ = B^(2*J)*((2*J).factorial : ℝ)/D^(2*J) := by field_simp
    _ ≤ B^(2*J)*(Real.exp 1*((2*J : ℕ) : ℝ)*
        (((2*J : ℕ) : ℝ)/Real.exp 1)^(2*J))/D^(2*J) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (pow_nonneg hB _))
        (pow_nonneg hD.le _)
    _ = Real.exp 1*((2*J : ℕ) : ℝ)*
        (B*(((2*J : ℕ) : ℝ)/Real.exp 1)/D)^(2*J) := by
      conv_rhs => rw [div_pow,mul_pow]
      ring
    _ = _ := by rw [he]; push_cast; ring

theorem ring_subset_weight_bound {K : Type*} [Fintype K] [LinearOrder K]
    (N : ℕ) (hN : 0 < N) (C b δ : ℝ) (hC : 0 < C) (hb : 1 < b) (hδ : δ < 1)
    (d : K → ℕ) (hd : ∀ k, 0 < d k)
    (hsep : ∀ i j, i < j → b*(d i : ℝ) ≤ (d j : ℝ))
    (hD : 2*∑ k, d k ≤ N) (hfrac : (2*∑ k, d k : ℕ) ≤ δ*(N : ℝ))
    (s : Finset K) (hs : s.Nonempty) :
    (ringAmplitude d (ringRadius N C d) s)^2/(N.choose (2*∑ k ∈ s, d k) : ℝ) ≤
      2*Real.exp 1*(∑ k ∈ s, d k : ℕ)*
        (entropyConstant b/(C*Real.exp 1*(1-δ)))^(2*∑ k ∈ s, d k) := by
  have hsum : (∑ k ∈ s, d k) ≤ ∑ k, d k :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ s)
  have hJN : 2*∑ k ∈ s, d k ≤ N := by omega
  have hsumR : ((2*∑ k ∈ s, d k : ℕ) : ℝ) ≤ (2*∑ k, d k : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left 2 hsum
  apply amplitude_binomial_weight N _ hN (Finset.sum_pos (fun k _ => hd k) hs)
    C (entropyConstant b) δ _ hC (entropyConstant_pos b hb).le hδ
    (Finset.prod_nonneg (fun k _ => pow_nonneg (by unfold ringRadius; positivity) _))
    (ringAmplitude_entropy_bound N C b hC hb d hd hsep s hs) hJN
    (hsumR.trans hfrac)

end
end CofactorSpectral
