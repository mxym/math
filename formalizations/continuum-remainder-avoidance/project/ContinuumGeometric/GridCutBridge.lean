import ContinuumGeometric.Planar
import ContinuumGeometric.ClosedProjection

/-!
Actual grid/activation cuts at a fixed center. Positivity is proved before
any logarithm comparison. All three signs, in particular exact equality,
are preserved. The independent arrangement theorem is USED, never assumed.
-/
namespace ContinuumGeometric

open Set

noncomputable def gridCrossingCut (input β : ℝ) (k : ℤ) : AffineCut :=
  (Real.log input, 1, (k : ℝ) * Real.log 2 - Real.log β)

noncomputable def logPowerParams {s₀ s₁ : ℝ} (p : PowerParams s₀ s₁) : ℝ × ℝ :=
  (p.1.1, Real.log p.2.1)

/-- A positive lifted boundary has the same negative/zero/positive sign after logarithms. -/
theorem power_grid_cut_sign (input β s t : ℝ) (k : ℤ)
    (hinput : 0 < input) (hβ : 0 < β) (ht : 0 < t) :
    cutSign (t * (2 : ℝ) ^ k * input ^ s - β) =
      cutSign (evalCut (gridCrossingCut input β k) (s, Real.log t)) := by
  have hk : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hp : 0 < input ^ s := Real.rpow_pos_of_pos hinput s
  have hoff : 0 < t * (2 : ℝ) ^ k * input ^ s := mul_pos (mul_pos ht hk) hp
  have hlog : Real.log (t * (2 : ℝ) ^ k * input ^ s) - Real.log β =
      evalCut (gridCrossingCut input β k) (s, Real.log t) := by
    rw [Real.log_mul (mul_pos ht hk).ne' hp.ne', Real.log_mul ht.ne' hk.ne',
      Real.log_zpow, Real.log_rpow hinput]
    unfold evalCut gridCrossingCut
    ring
  rw [← hlog]
  by_cases hn : t * (2 : ℝ) ^ k * input ^ s < β
  · have hl : Real.log (t * (2 : ℝ) ^ k * input ^ s) < Real.log β :=
      (Real.log_lt_log_iff hoff hβ).2 hn
    rw [(cutSign_eq_negative _).2 (by linarith),
      (cutSign_eq_negative _).2 (by linarith)]
  · by_cases hz : t * (2 : ℝ) ^ k * input ^ s = β
    · rw [hz, sub_self, sub_self]
    · have hv : β < t * (2 : ℝ) ^ k * input ^ s :=
        lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have hl : Real.log β < Real.log (t * (2 : ℝ) ^ k * input ^ s) :=
        (Real.log_lt_log_iff hβ hoff).2 hv
      rw [(cutSign_eq_positive _).2 (by linarith),
        (cutSign_eq_positive _).2 (by linarith)]

/-- The actual dyadic point and a lifted grid boundary; center x remains fixed. -/
theorem actual_grid_boundary_sign (s₀ s₁ x : ℝ) (n N : ℕ) (k b : ℤ)
    (_hN : 0 < N) (p : PowerParams s₀ s₁)
    (hβ : 0 < (b : ℝ) / N - x) :
    cutSign (powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) - (b : ℝ) / N) =
      cutSign (evalCut (gridCrossingCut (dyadic n) ((b : ℝ) / N - x) k)
        (logPowerParams p)) := by
  have hinput : 0 < dyadic n := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
  have ht : 0 < p.2.1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) p.2.2.1
  have h := power_grid_cut_sign (dyadic n) ((b : ℝ) / N - x) p.1.1 p.2.1 k
    hinput hβ ht
  convert h using 1 <;> simp only [powerPoint, logPowerParams]
  congr 1
  ring

def lowerActivationCut (n : ℕ) (k : ℤ) (u : ℝ) : AffineCut :=
  (n, 0, -(k : ℝ) - u)

def upperActivationCut (n : ℕ) (k : ℤ) (v : ℝ) : AffineCut :=
  (-(n : ℝ), 0, (k : ℝ) + v)

/-- Zero signs at EITHER activation boundary are inactive, exactly as in Section 7. -/
theorem activation_cut_signs (s₀ s₁ u v : ℝ) (n : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁) :
    p ∈ powerActivation n k u v ↔
      cutSign (evalCut (lowerActivationCut n k u) (logPowerParams p)) = .positive ∧
      cutSign (evalCut (upperActivationCut n k v) (logPowerParams p)) = .positive := by
  rw [cutSign_eq_positive, cutSign_eq_positive]
  simp only [powerActivation, mem_ofPred_eq, evalCut, lowerActivationCut,
    upperActivationCut, logPowerParams]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

theorem logPowerParams_inRectangle (s₀ s₁ : ℝ) (p : PowerParams s₀ s₁) :
    inRectangle (s₀, 0) (s₁, Real.log 2) (logPowerParams p) := by
  have ht : 0 < p.2.1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) p.2.2.1
  exact ⟨p.1.2.1, p.1.2.2, Real.log_nonneg p.2.2.1,
    Real.log_le_log ht p.2.2.2⟩

/-- Representatives in the ORIGINAL compact power parameters, using the proved interface.

Domain edges are not appended again to the m cuts: the rectangle restriction
is already handled by arrangementRepresentativeBound. This preserves every
real exponent and coefficient endpoint, including zero-sign strata.
-/
theorem power_parameter_sign_representatives (s₀ s₁ : ℝ) (hs : s₀ ≤ s₁)
    (m : ℕ) (cuts : Fin m → AffineCut) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (m + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps, ∀ i : Fin m,
        cutSign (evalCut (cuts i) (logPowerParams r)) =
          cutSign (evalCut (cuts i) (logPowerParams p)) := by
  classical
  obtain ⟨reps, hrect, hcard, hsig⟩ := arrangementRepresentativeBound m cuts
    (s₀, 0) (s₁, Real.log 2) hs (Real.log_nonneg (by norm_num))
  let lift : {r // r ∈ reps} → PowerParams s₀ s₁ := fun r =>
    (⟨r.1.1, ⟨(hrect r.1 r.2).1, (hrect r.1 r.2).2.1⟩⟩,
     ⟨Real.exp r.1.2, ⟨by
       simpa using (Real.exp_le_exp.2 (hrect r.1 r.2).2.2.1), by
       calc
         Real.exp r.1.2 ≤ Real.exp (Real.log 2) :=
           Real.exp_le_exp.2 (hrect r.1 r.2).2.2.2
         _ = 2 := Real.exp_log (by norm_num)⟩⟩)
  have hlift : ∀ r : {r // r ∈ reps}, logPowerParams (lift r) = r.1 := by
    intro r
    apply Prod.ext
    · rfl
    · exact Real.log_exp _
  refine ⟨reps.attach.image lift, (Finset.card_image_le.trans ?_), ?_⟩
  · simpa using hcard
  · intro p
    obtain ⟨r, hr, hsign⟩ := hsig (logPowerParams p) (logPowerParams_inRectangle s₀ s₁ p)
    refine ⟨lift ⟨r, hr⟩, Finset.mem_image.2 ⟨⟨r, hr⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    intro i
    rw [hlift]
    exact hsign i

/-- Representatives are independent of arbitrary still-unexposed table assignments.

This is the uniformity statement for SIGNATURE-DEFINED readouts. Proving that
the actual routing address/readout factors through this signature remains
an explicit grid/tree obligation; it is not assumed or asserted here.
-/
theorem signature_representatives_uniform_readout {Ω Y : Type*}
    (s₀ s₁ : ℝ) (hs : s₀ ≤ s₁) (m : ℕ) (cuts : Fin m → AffineCut)
    (readout : Ω → (Fin m → CutSign) → Y) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (m + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps, ∀ ω : Ω,
        readout ω (fun i => cutSign (evalCut (cuts i) (logPowerParams r))) =
          readout ω (fun i => cutSign (evalCut (cuts i) (logPowerParams p))) := by
  obtain ⟨reps, hcard, hsig⟩ := power_parameter_sign_representatives s₀ s₁ hs m cuts
  refine ⟨reps, hcard, ?_⟩
  intro p
  obtain ⟨r, hr, hsign⟩ := hsig p
  refine ⟨r, hr, ?_⟩
  intro ω
  exact congrArg (readout ω) (funext hsign)

end ContinuumGeometric
