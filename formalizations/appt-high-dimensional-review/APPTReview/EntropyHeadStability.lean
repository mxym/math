import APPTReview.EntropyHead

open scoped BigOperators
namespace APPTReview

/-- Scalar hypotheses, subsequently derived from actual APPT eigenvalues. -/
structure EntropyHeadConditions {n : ℕ} (a : Fin (n+1) → ℝ) (β : Fin (n+2) → ℝ) : Prop where
  a_nonneg : ∀ i, 0 ≤ a i
  a_max : ∀ i, a i ≤ a 0
  beta_nonneg : ∀ i, 0 ≤ β i
  beta_antitone : Antitone β
  beta_le_one : β 0 ≤ 1
  star_budget : (∑ i : Fin (n+1), (a i+β i.succ)^2) ≤ 4*(1-β 0)

theorem entropyHead_deficit_nonneg {n : ℕ} {a : Fin (n+1) → ℝ} {β : Fin (n+2) → ℝ}
    (h : EntropyHeadConditions a β) : 0 ≤ 2-entropyHead a β := by
  have hh := entropyHead_le_two a β h.a_nonneg h.a_max h.beta_nonneg h.beta_antitone h.beta_le_one h.star_budget
  linarith

theorem entropyHead_first_square {n : ℕ} {a : Fin (n+1) → ℝ} {β : Fin (n+2) → ℝ}
    (h : EntropyHeadConditions a β) : (a 0)^2 ≤ 4*(1-β 0) ∧ a 0 ≤ 2 := by
  have ht : (a 0+β (0 : Fin (n+1)).succ)^2 ≤ ∑ i : Fin (n+1), (a i+β i.succ)^2 :=
    Finset.single_le_sum (fun i (_ : i∈Finset.univ) => sq_nonneg (a i+β i.succ)) (Finset.mem_univ (0 : Fin (n+1)))
  have hp := mul_nonneg (h.a_nonneg 0) (h.beta_nonneg (0 : Fin (n+1)).succ)
  have hs := h.star_budget
  have hb := h.beta_nonneg 0
  constructor <;> nlinarith [sq_nonneg (β (0 : Fin (n+1)).succ)]

/-- A positive outlier of relative amplitude at least one has a fixed deficit. -/
theorem entropyHead_large_outlier_deficit {n : ℕ}
    {a : Fin (n+1) → ℝ} {β : Fin (n+2) → ℝ}
    (h : EntropyHeadConditions a β) (ha : 1 ≤ a 0) :
    (37/1344 : ℝ) ≤ 2-entropyHead a β := by
  have hp := entropyHead_prebound a β h.a_nonneg h.a_max h.beta_nonneg h.beta_antitone h.beta_le_one h.star_budget
  obtain ⟨hs,hu⟩ := entropyHead_first_square h
  have hg := entropy_head_outlier_margin ha hu
  have hc := mul_le_mul_of_nonneg_right
    (show β 0 ≤ 1-(a 0)^2/4 by nlinarith) (show 0 ≤ a 0-1 by linarith)
  dsimp [entropyGap] at hp
  linarith

/-- Quantitative stability with constants independent of the number of eigenvalues. -/
theorem entropyHead_outlier_bounds {n : ℕ}
    {a : Fin (n+1) → ℝ} {β : Fin (n+2) → ℝ}
    (h : EntropyHeadConditions a β) :
    (a 0)^3 ≤ 300*(2-entropyHead a β) ∧ β 0 ≤ 72*(2-entropyHead a β) := by
  let Δ := 2-entropyHead a β
  have hΔ : 0 ≤ Δ := entropyHead_deficit_nonneg h
  have ha := h.a_nonneg 0
  have hb := h.beta_nonneg 0
  have hb1 := h.beta_le_one
  by_cases hlarge : 1 ≤ a 0
  · have hd : (37/1344:ℝ) ≤ Δ := entropyHead_large_outlier_deficit h hlarge
    have hu := (entropyHead_first_square h).2
    have hc := pow_le_pow_left₀ ha hu 3
    norm_num at hc
    constructor <;> change _ ≤ _*Δ <;> linarith
  · have hsmall : a 0 ≤ 1 := (lt_of_not_ge hlarge).le
    have hp := entropyHead_prebound a β h.a_nonneg h.a_max h.beta_nonneg h.beta_antitone h.beta_le_one h.star_budget
    have hg0 := entropyGap_nonneg ha
    have hterm := mul_nonneg hb (show 0 ≤ 1-a 0 by linarith)
    have hg : entropyGap (a 0) ≤ Δ := by dsimp [Δ]; nlinarith
    have hgap := entropy_positive_gap_bound ha
    have hden : 0 < 3*(a 0+2) := by positivity
    have hcube : (a 0)^3 ≤ 9*Δ := by
      have hc := (div_le_iff₀ hden).mp (hgap.trans hg)
      have hm := mul_le_mul_of_nonneg_left (show 3*(a 0+2) ≤ 9 by linarith) hΔ
      nlinarith
    refine ⟨by change _ ≤ 300*Δ; linarith,?_⟩
    change β 0 ≤ 72*Δ
    by_cases haHalf : a 0 ≤ 1/2
    · have hhalf := mul_le_mul_of_nonneg_left haHalf hb
      dsimp [Δ] at *
      nlinarith
    · have hc := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2)
        (le_of_lt (lt_of_not_ge haHalf)) 3
      norm_num at hc
      linarith

/-- The finite head has strict inequality; two is only an asymptotic endpoint. -/
theorem entropyHead_lt_two {n : ℕ}
    {a : Fin (n+1) → ℝ} {β : Fin (n+2) → ℝ}
    (h : EntropyHeadConditions a β) : entropyHead a β < 2 := by
  have hd := entropyHead_deficit_nonneg h
  have hb := entropyHead_outlier_bounds h
  by_contra hn
  have he : entropyHead a β = 2 := by linarith
  have hc : (a 0)^3 = 0 := by rw [he] at hb; nlinarith [pow_nonneg (h.a_nonneg 0) 3]
  have ha0 : a 0 = 0 := (pow_eq_zero_iff (by decide : (3:ℕ) ≠ 0)).mp hc
  have hβ0 : β 0 = 0 := by rw [he] at hb; linarith [h.beta_nonneg 0]
  have haAll (i) : a i = 0 := le_antisymm (by simpa [ha0] using h.a_max i) (h.a_nonneg i)
  have hbAll (i) : β i = 0 := le_antisymm (by simpa [hβ0] using h.beta_antitone (Fin.zero_le i)) (h.beta_nonneg i)
  have hz : entropyHead a β = 0 := by simp [entropyHead,haAll,hbAll,entropyKernel]
  linarith

end APPTReview
