import MinimaxProfile.Protocol
import MinimaxProfile.IntegerPacking

open scoped BigOperators ComplexOrder
open Matrix
namespace MinimaxProfile

variable {a b K : ℕ} {ι : Type*}

/-- Guarantees of genuine fixed physical protocols on the entire input family. -/
def guaranteedValues
    (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (K : ℕ) : Set ℝ :=
  {c | ∃ V : KrausPPTProtocol a b K, ∀ i, c ≤ V.fidelity (X i)}

noncomputable def minimaxValue
    (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (K : ℕ) : ℝ :=
  sSup (guaranteedValues X K)

theorem smaller_dimension_feasible {a b r d e : ℕ}
    (he : 0 < e) (hed : e ≤ d) (h : r ≤ (a / d) * (b / d)) :
    r ≤ (a / e) * (b / e) := by
  have ha : a / d ≤ a / e := (Nat.le_div_iff_mul_le he).2
    ((Nat.mul_le_mul_left (a / d) hed).trans (Nat.div_mul_le_self a d))
  have hb : b / d ≤ b / e := (Nat.le_div_iff_mul_le he).2
    ((Nat.mul_le_mul_left (b / d) hed).trans (Nat.div_mul_le_self b d))
  exact h.trans (Nat.mul_le_mul ha hb)

/-- The protocol attains the whole finite target profile, including targets
smaller than the feasible Bell dimension. -/
theorem common_support_profile_protocol (a b d K : ℕ) (hd : 0 < d) (hK : 0 < K)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hr : P.rank ≤ (a / d) * (b / d)) :
    ∃ V : KrausPPTProtocol a b K,
      ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        APPT.Quantum.IsDensity X → P * X * P = X → V.fidelity X = profile d K := by
  obtain ⟨V,hV⟩ := common_support_protocol a b (min d K) K (lt_min hd hK)
    (min_le_right _ _) P hP hPP (smaller_dimension_feasible (lt_min hd hK) (min_le_left _ _) hr)
  refine ⟨V, ?_⟩
  intro X hX hPX
  rw [hV X hX hPX]
  unfold profile
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases h : d ≤ K
  · rw [min_eq_left h, min_eq_right ((div_le_one hKR).2 (by exact_mod_cast h))]
  · rw [min_eq_right (le_of_not_ge h), min_eq_left ((one_le_div hKR).2 (by exact_mod_cast (le_of_not_ge h)))]
    exact div_self (ne_of_gt hKR)

/-- The finite ensemble support/average minimax theorem for actual matrix
protocols. The ensemble is an adversarial mathematical average; no random
preprocessing is supplied to the extractor. -/
theorem actual_minimax_finite_bounds
    (d : ℕ) (hd : 0 < d) (hK : 0 < K)
    (X : ι → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hX : ∀ i, APPT.Quantum.IsDensity (X i))
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P)
    (hr : P.rank ≤ (a / d) * (b / d)) (hsupp : ∀ i, P * X i * P = X i)
    {β : Type*} [Fintype β] (sample : β → ι) (p : β → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) :
    profile d K ≤ minimaxValue X K ∧
    minimaxValue X K ≤ min 1 (min ((a : ℝ) / K)
      (Real.sqrt (((finiteAverage p (fun j => X (sample j))) *
        (finiteAverage p (fun j => X (sample j)))).trace.re *
          ((a * b : ℝ) / (K : ℝ)^2)))) := by
  obtain ⟨V,hV⟩ := common_support_profile_protocol a b d K hd hK P hP hPP hr
  have hlo : profile d K ∈ guaranteedValues X K := ⟨V, fun i => (hV _ (hX i) (hsupp i)).ge⟩
  have hupper (c : ℝ) (hc : c ∈ guaranteedValues X K) :
      c ≤ min 1 (min ((a : ℝ) / K)
        (Real.sqrt (((finiteAverage p (fun j => X (sample j))) *
          (finiteAverage p (fun j => X (sample j)))).trace.re *
            ((a * b : ℝ) / (K : ℝ)^2)))) := by
    obtain ⟨W,hW⟩ := hc
    exact physical_finite_ensemble_bound hK W.A W.complete W.ptPositive W.U
      p (fun j => X (sample j)) hp hpsum (fun j => hX (sample j)) c
        (fun j => hW (sample j))
  exact ⟨le_csSup ⟨_,hupper⟩ hlo, csSup_le ⟨_,hlo⟩ hupper⟩

end MinimaxProfile
