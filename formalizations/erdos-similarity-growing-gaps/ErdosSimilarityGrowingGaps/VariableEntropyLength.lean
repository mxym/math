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
