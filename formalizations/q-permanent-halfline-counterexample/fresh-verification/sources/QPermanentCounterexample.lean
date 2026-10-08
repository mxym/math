import QPermanentPosDef
import QPermanentValues

namespace QPermanentHalfline

/-- The non-diagonal real positive-definite half-line conjecture (open endpoint version). -/
def HalfLineConjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    A.PosDef → (¬ ∃ d : Fin n → ℝ, A = Matrix.diagonal d) →
    ∃ a : ℝ, a < -1 ∧ StrictMonoOn (qPermanent A) (Set.Ioi a)

theorem counterexampleMatrix_not_monotone_closed {a : ℝ} (ha : a ≤ 49) :
    ¬ MonotoneOn (qPermanent counterexampleMatrix) (Set.Ici a) := by
  intro h
  have hh := h ha (by change a ≤ 50; linarith) (by norm_num : (49 : ℝ) ≤ 50)
  exact (not_le_of_gt counterexampleMatrix_decreases) hh

theorem counterexampleMatrix_not_strictMono_open {a : ℝ} (ha : a < 49) :
    ¬ StrictMonoOn (qPermanent counterexampleMatrix) (Set.Ioi a) := by
  intro h
  have hh := h ha (by change a < 50; linarith) (by norm_num : (49 : ℝ) < 50)
  exact (not_lt_of_ge (le_of_lt counterexampleMatrix_decreases)) hh

/-- The actual positive-definite matrix, exact values, and failure for every required endpoint. -/
theorem explicit_counterexample :
    counterexampleMatrix.PosDef ∧
    (¬ ∃ d : Fin 4 → ℝ, counterexampleMatrix = Matrix.diagonal d) ∧
    qPermanent counterexampleMatrix 49 = 81807513 / 500000 ∧
    qPermanent counterexampleMatrix 50 = 7969 / 50 ∧
    qPermanent counterexampleMatrix 50 < qPermanent counterexampleMatrix 49 ∧
    ∀ a : ℝ, a ≤ -1 →
      (¬ MonotoneOn (qPermanent counterexampleMatrix) (Set.Ici a)) ∧
      (¬ StrictMonoOn (qPermanent counterexampleMatrix) (Set.Ioi a)) := by
  refine ⟨counterexampleMatrix_posDef, counterexampleMatrix_not_diagonal,
    counterexampleMatrix_value_49, counterexampleMatrix_value_50,
    counterexampleMatrix_decreases, ?_⟩
  intro a ha
  constructor
  · exact counterexampleMatrix_not_monotone_closed (by linarith)
  · exact counterexampleMatrix_not_strictMono_open (by linarith)

theorem halfLineConjecture_false : ¬ HalfLineConjecture := by
  intro h
  obtain ⟨a, ha, hmono⟩ :=
    h 4 counterexampleMatrix counterexampleMatrix_posDef counterexampleMatrix_not_diagonal
  exact counterexampleMatrix_not_strictMono_open (by linarith) hmono

end QPermanentHalfline
