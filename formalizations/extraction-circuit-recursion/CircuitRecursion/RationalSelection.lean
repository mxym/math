import CircuitRecursion.DyadicPrecision

namespace CircuitRecursion

/-- An executable finite rational-score selector. The caller supplies the
finite score table; no real comparison or classical choice occurs here. -/
def rationalMinIndex : (n : ℕ) → (Fin (n+1) → ℚ) → Fin (n+1)
  | 0,_ => 0
  | n+1,score =>
    let j := rationalMinIndex n (fun i => score i.succ)
    if score 0≤score j.succ then 0 else j.succ

theorem rationalMinIndex_le (n : ℕ) (score : Fin (n+1) → ℚ) (i : Fin (n+1)) :
    score (rationalMinIndex n score)≤score i := by
  induction n with
  | zero => fin_cases i; exact le_refl _
  | succ n ih =>
    simp only [rationalMinIndex]
    split_ifs with h
    · cases i using Fin.cases with
      | zero => exact le_refl _
      | succ j => exact h.trans (ih (fun i => score i.succ) j)
    · cases i using Fin.cases with
      | zero => exact (not_le.mp h).le
      | succ j => exact ih (fun i => score i.succ) j

/-- Approximate score comparisons lose at most twice the score error. -/
theorem rationalMinIndex_error (n : ℕ) (score : Fin (n+1) → ℚ)
    (trueScore : Fin (n+1) → ℝ) (η : ℝ)
    (he : ∀ i,|(score i:ℝ)-trueScore i|≤η) (i : Fin (n+1)) :
    trueScore (rationalMinIndex n score)≤trueScore i+2*η := by
  have hm : (score (rationalMinIndex n score):ℝ)≤(score i:ℝ) := by
    exact_mod_cast rationalMinIndex_le n score i
  have hsel := (abs_le.mp (he (rationalMinIndex n score))).1
  have hi := (abs_le.mp (he i)).2
  linarith

/-- A fixed net with slack can be searched by finite rational comparisons.
The theorem certifies the selector, not construction or cost of its table
or matrix-distance scores. -/
theorem rationalMinIndex_net_error {X : Type*} [PseudoMetricSpace X]
    (n : ℕ) (table : Fin (n+1) → X) (target : X)
    (score : Fin (n+1) → ℚ) (ρ η : ℝ)
    (he : ∀ i,|(score i:ℝ)-dist target (table i)|≤η)
    (hcover : ∃ i,dist target (table i)≤ρ) :
    dist target (table (rationalMinIndex n score))≤ρ+2*η := by
  obtain ⟨i,hi⟩ := hcover
  have hs := rationalMinIndex_error n score (fun i => dist target (table i)) η he i
  linarith

end CircuitRecursion
