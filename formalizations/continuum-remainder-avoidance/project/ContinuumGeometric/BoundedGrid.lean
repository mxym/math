import ContinuumGeometric.GridCutBridge
import Mathlib.Data.Int.Interval

/-!
Finite, boundary-complete cuts determine ACTUAL periodic grid addresses,
not only an abstract signature readout. Bounds for the finite boundary batch
are explicit inputs; deriving the routing-window entropy/cardinality bounds
is still a separate obligation. Address equality is uniform for all tables.
-/
namespace ContinuumGeometric

theorem cutSign_pos_mul (c z : ℝ) (hc : 0 < c) : cutSign (c * z) = cutSign z := by
  by_cases hn : z < 0
  · exact ((cutSign_eq_negative _).2 (mul_neg_of_pos_of_neg hc hn)).trans
      ((cutSign_eq_negative _).2 hn).symm
  · by_cases hz : z = 0
    · simp [hz]
    · have hp : 0 < z := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      exact ((cutSign_eq_positive _).2 (mul_pos hc hp)).trans
        ((cutSign_eq_positive _).2 hp).symm

/-- Exact half-open convention: equality at integer b belongs to floor b. -/
theorem bounded_floor_eq_of_boundary_signs (A B : ℤ) (z z' : ℝ)
    (hl : (A : ℝ) ≤ z) (hu : z ≤ (B : ℝ))
    (hl' : (A : ℝ) ≤ z') (hu' : z' ≤ (B : ℝ))
    (hsig : ∀ b ∈ Finset.Icc A B,
      cutSign (z - (b : ℝ)) = cutSign (z' - (b : ℝ))) :
    Int.floor z = Int.floor z' := by
  have hmem : ∀ (v : ℝ), (A : ℝ) ≤ v → v ≤ (B : ℝ) →
      Int.floor v ∈ Finset.Icc A B := by
    intro v hlo hhi
    refine Finset.mem_Icc.2 ⟨Int.le_floor.2 hlo, ?_⟩
    exact_mod_cast (Int.floor_le v).trans hhi
  apply le_antisymm
  · apply Int.le_floor.2
    by_contra h
    have hneg : cutSign (z' - (Int.floor z : ℝ)) = .negative :=
      (cutSign_eq_negative _).2 (by linarith)
    have hzneg := (hsig (Int.floor z) (hmem z hl hu)).trans hneg
    have := (cutSign_eq_negative _).1 hzneg
    linarith [Int.floor_le z]
  · apply Int.le_floor.2
    by_contra h
    have hneg : cutSign (z - (Int.floor z' : ℝ)) = .negative :=
      (cutSign_eq_negative _).2 (by linarith)
    have hzneg := (hsig (Int.floor z') (hmem z' hl' hu')).symm.trans hneg
    have := (cutSign_eq_negative _).1 hzneg
    linarith [Int.floor_le z']

noncomputable def periodicGridKey (N : ℕ) (z : ℝ) : ℤ :=
  Int.floor ((N : ℝ) * z) % (N : ℤ)

theorem grid_boundary_sign_rescale (N : ℕ) (hN : 0 < N) (z : ℝ) (b : ℤ) :
    cutSign ((N : ℝ) * z - b) = cutSign (z - (b : ℝ) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : (N : ℝ) * z - b = (N : ℝ) * (z - (b : ℝ) / N) := by
    field_simp
  rw [heq]
  exact cutSign_pos_mul _ _ hNr

theorem bounded_periodicGridKey_eq (N : ℕ) (hN : 0 < N) (A B : ℤ) (z z' : ℝ)
    (hl : (A : ℝ) ≤ (N : ℝ) * z) (hu : (N : ℝ) * z ≤ (B : ℝ))
    (hl' : (A : ℝ) ≤ (N : ℝ) * z') (hu' : (N : ℝ) * z' ≤ (B : ℝ))
    (hsig : ∀ b ∈ Finset.Icc A B,
      cutSign (z - (b : ℝ) / N) = cutSign (z' - (b : ℝ) / N)) :
    periodicGridKey N z = periodicGridKey N z' := by
  have heq := bounded_floor_eq_of_boundary_signs A B ((N : ℝ) * z) ((N : ℝ) * z')
    hl hu hl' hu' (fun b hb => by
      rw [grid_boundary_sign_rescale N hN, grid_boundary_sign_rescale N hN]
      exact hsig b hb)
  unfold periodicGridKey
  rw [heq]

/-- Positive lifted-boundary log cuts determine the actual dyadic point's periodic key.

Nonpositive lifted boundaries need no logarithm: both offsets from the fixed
center are strictly positive, so their boundary signs are automatically equal.
All finite-batch range bounds and every positive-boundary signature are explicit.
-/
theorem actual_grid_key_eq_of_log_signs (s₀ s₁ x : ℝ) (n N : ℕ) (k : ℤ)
    (hN : 0 < N) (A B : ℤ) (p p' : PowerParams s₀ s₁)
    (hl : (A : ℝ) ≤ (N : ℝ) * powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p))
    (hu : (N : ℝ) * powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ≤ (B : ℝ))
    (hl' : (A : ℝ) ≤ (N : ℝ) * powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p'))
    (hu' : (N : ℝ) * powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p') ≤ (B : ℝ))
    (hsig : ∀ b ∈ Finset.Icc A B, 0 < (b : ℝ) / N - x →
      cutSign (evalCut (gridCrossingCut (dyadic n) ((b : ℝ) / N - x) k)
        (logPowerParams p)) =
      cutSign (evalCut (gridCrossingCut (dyadic n) ((b : ℝ) / N - x) k)
        (logPowerParams p'))) :
    periodicGridKey N (powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p)) =
      periodicGridKey N (powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p')) := by
  have hpoint : ∀ r : PowerParams s₀ s₁,
      x < powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, r) := by
    intro r
    have ht : 0 < r.2.1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) r.2.2.1
    have hk : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have ha : 0 < dyadic n := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
    have hoff := mul_pos (mul_pos ht hk) (Real.rpow_pos_of_pos ha r.1.1)
    unfold powerPoint
    linarith
  apply bounded_periodicGridKey_eq N hN A B _ _ hl hu hl' hu'
  intro b hb
  by_cases hβ : 0 < (b : ℝ) / N - x
  · rw [actual_grid_boundary_sign s₀ s₁ x n N k b hN p hβ,
      actual_grid_boundary_sign s₀ s₁ x n N k b hN p' hβ]
    exact hsig b hb hβ
  · have hp : 0 < powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) - (b : ℝ) / N := by
      linarith [hpoint p]
    have hp' : 0 < powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p') - (b : ℝ) / N := by
      linarith [hpoint p']
    rw [(cutSign_eq_positive _).2 hp, (cutSign_eq_positive _).2 hp']

/-- Actual grid-table reads are uniform over EVERY still-unexposed assignment.
The address theorem above, not an assumed signature-factorization law, supplies
the equality. The finite-batch bounds are kept as explicit obligations.
-/
theorem actual_grid_table_reads_uniform {Ω Y : Type*}
    (s₀ s₁ x : ℝ) (n N : ℕ) (k : ℤ) (hN : 0 < N) (A B : ℤ)
    (p p' : PowerParams s₀ s₁)
    (hl : (A : ℝ) ≤ (N : ℝ) * powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p))
    (hu : (N : ℝ) * powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ≤ (B : ℝ))
    (hl' : (A : ℝ) ≤ (N : ℝ) * powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p'))
    (hu' : (N : ℝ) * powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p') ≤ (B : ℝ))
    (hsig : ∀ b ∈ Finset.Icc A B, 0 < (b : ℝ) / N - x →
      cutSign (evalCut (gridCrossingCut (dyadic n) ((b : ℝ) / N - x) k)
        (logPowerParams p)) =
      cutSign (evalCut (gridCrossingCut (dyadic n) ((b : ℝ) / N - x) k)
        (logPowerParams p')))
    (tables : Ω → ℤ → Y) :
    ∀ ω : Ω,
      tables ω (periodicGridKey N (powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p))) =
        tables ω (periodicGridKey N (powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p'))) := by
  intro ω
  exact congrArg (tables ω)
    (actual_grid_key_eq_of_log_signs s₀ s₁ x n N k hN A B p p' hl hu hl' hu' hsig)

end ContinuumGeometric
