import ChromaticCyclesAllN.GeneralCycleTrace
import ChromaticCyclesAllN.CyclePolynomialClassification
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace ChromaticCycleAll
open SimpleGraph Polynomial

theorem cycleGraph_colorings_all (n q : ℕ) (hn : 3 ≤ n) :
    (cycleFormulaPolynomial n).eval (q : ℤ) =
      (Fintype.card ((cycleGraph n).Coloring (Fin q)) : ℤ) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [coloring_card_eq_trace_all n q hn, trace_complete_adj_pow]
  norm_num [cycleFormulaPolynomial]
  ring

def IsChromaticPolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) (P : ℤ[X]) : Prop :=
  ∀ q : ℕ, P.eval (q : ℤ) =
    (Fintype.card (G.Coloring (Fin q)) : ℤ)

theorem cyclePolynomial_isChromatic (n : ℕ) (hn : 3 ≤ n) :
    IsChromaticPolynomial (cycleGraph n) (cycleFormulaPolynomial n) := by
  intro q
  exact cycleGraph_colorings_all n q hn

theorem cycleGraph_chromatic_polynomial_classification (n : ℕ) (hn : 3 ≤ n) :
    IsChromaticPolynomial (cycleGraph n) (cycleFormulaPolynomial n) ∧
      (InfinitelyLogConcave (cycleAbsCoeff n) ↔ n ≤ 11) :=
  ⟨cyclePolynomial_isChromatic n hn,
    cycle_polynomial_infinite_logconcavity_iff n hn⟩

theorem every_actual_cycle_n_ge_17_fails (n : ℕ) (hn : 17 ≤ n) :
    IsChromaticPolynomial (cycleGraph n) (cycleFormulaPolynomial n) ∧
    LC (LC (LC (cycleAbsCoeff n))) 2 < 0 :=
  ⟨cyclePolynomial_isChromatic n (by omega),
    cycleFormula_all_large_negative n hn⟩

end ChromaticCycleAll
