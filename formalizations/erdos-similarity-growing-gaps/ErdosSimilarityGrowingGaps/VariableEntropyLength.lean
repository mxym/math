import ErdosSimilarityGrowingGaps.AsymptoticHelpers
import ErdosSimilarityGrowingGaps.EntropySchedule
import ErdosSimilarityGrowingGaps.VariableParameterBounds

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-- An explicit integer lower length for the varying-branching entropy cost.
The fixed term includes the final probability budget; `2*M` controls the
otherwise changing logarithm of the branching factor. -/
noncomputable def variableEntropyLength (p : ℝ) (M U : ℕ) : ℕ :=
  2 * M + Nat.ceil (max (Real.log (46080 / p) + 1) 0) +
    Nat.ceil (max (4 * Real.log ((U : ℝ) + 2)) 0)

theorem variableEntropyLength_log_lower
    (p κ : ℝ) (M U L : ℕ) (hp : 0 < p) (hM : 1 ≤ M)
    (hκ : 1 ≤ κ) (hL : variableEntropyLength p M U ≤ L) :
    4 * Real.log ((U : ℝ) + 2) +
      Real.log ((46080 * (M : ℝ)^2) / p) + 1 ≤ κ * (L : ℝ) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogM : Real.log (M : ℝ) ≤ (M : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hMpos]
  have hfixed : Real.log (46080 / p) + 1 ≤
      (Nat.ceil (max (Real.log (46080 / p) + 1) 0) : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hlog : 4 * Real.log ((U : ℝ) + 2) ≤
      (Nat.ceil (max (4 * Real.log ((U : ℝ) + 2)) 0) : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hLe : (variableEntropyLength p M U : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have hC : Real.log ((46080 * (M : ℝ)^2) / p) =
      Real.log (46080 / p) + 2 * Real.log (M : ℝ) := by
    rw [show (46080 * (M : ℝ)^2) / p = (46080 / p) * (M : ℝ)^2 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hLL : (L : ℝ) ≤ κ * (L : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) L]
  rw [hC]
  dsimp [variableEntropyLength] at hLe
  push_cast at hLe
  linarith

theorem variable_entropy_budget_of_length
    {K : ℕ} (hK : 2 ≤ K) (p σ D : ℝ)
    (hp : 0 < p) (hσ : 0 < σ) (hD : 0 ≤ D) (U L : ℕ)
    (hL : variableEntropyLength p (lateBranching K p σ D) U ≤ L) :
    46080 * (lateBranching K p σ D : ℝ)^2 * ((U : ℝ) + 1)^2 *
      Real.exp (-(p * lateActivationRate K σ D *
        ((lateBranching K p σ D : ℝ) - 1) / 2 - 4 * Real.log 2) *
          (L : ℝ)) < p := by
  have hdecay := lateBranching_decay_ge_two K hK p σ D hp hσ hD
  have hM := lateBranching_ge_two K p σ D
  have hC : 0 < 46080 * (lateBranching K p σ D : ℝ)^2 := by
    have hMr : (0 : ℝ) < lateBranching K p σ D := by exact_mod_cast (show 0 < lateBranching K p σ D by omega)
    positivity
  exact entropy_budget_of_log_lower
    (46080 * (lateBranching K p σ D : ℝ)^2) p
    (p * lateActivationRate K σ D * ((lateBranching K p σ D : ℝ) - 1) / 2 - 4 * Real.log 2)
    (L : ℝ) hC hp U
    (variableEntropyLength_log_lower p _ _ U L hp (by omega) (by linarith) hL)

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-- The explicit entropy length has a little-o square as soon as the varying
branching factor does.  Ceilings contribute only bounded constants. -/
theorem variableEntropyLength_sq_littleO
    {ι : Type*} {l : Filter ι} (p : ℝ) (M U : ι → ℕ)
    (hU : Tendsto (fun i => (U i : ℝ)) l atTop)
    (hM2 : (fun i => (M i : ℝ)^2) =o[l] (fun i => (U i : ℝ))) :
    (fun i => (variableEntropyLength p (M i) (U i) : ℝ)^2) =o[l]
      (fun i => (U i : ℝ)) := by
  let C : ℝ := (Nat.ceil (max (Real.log (46080 / p) + 1) 0) : ℝ) + 1
  let S : ι → ℝ := fun i => 2 * (M i : ℝ) + 4 * Real.log ((U i : ℝ) + 2)
  have hU0 : ∀ᶠ i in l, 0 ≤ (U i : ℝ) := by
    filter_upwards [] with i
    positivity
  have hM0 : ∀ᶠ i in l, 0 ≤ 2 * (M i : ℝ) := by
    filter_upwards [] with i
    positivity
  have hlog0 : ∀ᶠ i in l, 0 ≤ 4 * Real.log ((U i : ℝ) + 2) := by
    filter_upwards [] with i
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    have hUn : (0 : ℝ) ≤ U i := by positivity
    linarith
  have hMscaled : (fun i => (2 * (M i : ℝ))^2) =o[l]
      (fun i => (U i : ℝ)) := by
    have h := hM2.const_mul_left 4
    convert h using 1 <;> ext i <;> ring
  have hlogscaled : (fun i => (4 * Real.log ((U i : ℝ) + 2))^2) =o[l]
      (fun i => (U i : ℝ)) := by
    have h := (shifted_log_sq_littleO (fun i => (U i : ℝ)) hU).const_mul_left 16
    convert h using 1 <;> ext i <;> ring
  have hS2 : (fun i => (S i)^2) =o[l] (fun i => (U i : ℝ)) := by
    dsimp [S]
    exact sq_add_littleO_of_sq _ _ _ hMscaled hlogscaled hM0 hlog0 hU0
  have hS0 : ∀ᶠ i in l, 0 ≤ S i := by
    filter_upwards [hM0, hlog0] with i hMi hLi
    dsimp [S]
    linarith
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hbound2 : (fun i => (S i + C)^2) =o[l]
      (fun i => (U i : ℝ)) := sq_add_const_littleO S _ C hS2 hS0 hU hC0
  have hlength_upper : ∀ i,
      (variableEntropyLength p (M i) (U i) : ℝ) ≤ S i + C := by
    intro i
    have hlog : 0 ≤ 4 * Real.log ((U i : ℝ) + 2) := by
      apply mul_nonneg (by norm_num)
      apply Real.log_nonneg
      have hUn : (0 : ℝ) ≤ U i := by positivity
      linarith
    have hceil : (Nat.ceil (max (4 * Real.log ((U i : ℝ) + 2)) 0) : ℝ) ≤
        4 * Real.log ((U i : ℝ) + 2) + 1 := by
      rw [max_eq_left hlog]
      exact (Nat.ceil_lt_add_one hlog).le
    dsimp [variableEntropyLength, S, C]
    push_cast
    linarith
  apply IsLittleO.of_bound
  intro c hc
  have hsmall := hbound2.bound hc
  filter_upwards [hsmall, hS0, hU0] with i hi hSi hUi
  have hnonneg : 0 ≤ (variableEntropyLength p (M i) (U i) : ℝ) := by positivity
  have hbound : (variableEntropyLength p (M i) (U i) : ℝ)^2 ≤ (S i + C)^2 := by
    nlinarith [hlength_upper i]
  have hi' : (S i + C)^2 ≤ c * (U i : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (S i + C)),
      Real.norm_eq_abs, abs_of_nonneg hUi, mul_one] using hi
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg hUi]
  exact hbound.trans hi'

end ErdosSimilarityGrowingGaps
