import HydrologyTree.RingTreeModel
import Mathlib.Algebra.MvPolynomial.Basic

/-! Independent symbolic coordinates for the actual physical rate arrays. -/
noncomputable section
namespace HydrologyTree

abbrev SymbolicRateIndex (n : ℕ) := Fin (n+1) ⊕ Fin n
abbrev RatePolynomial (n : ℕ) := MvPolynomial (SymbolicRateIndex n) ℝ

def rateEvaluation {n : ℕ} (x : TreeRates n) : SymbolicRateIndex n → ℝ := Sum.elim x.1 x.2

def universalTreeRates (n : ℕ) : RatesOver (RatePolynomial n) n :=
  (fun v => MvPolynomial.X (.inl v), fun e => MvPolynomial.X (.inr e))

lemma universalTreeRates_evaluate {n : ℕ} (x : TreeRates n) :
    ratesOverMap (MvPolynomial.eval (rateEvaluation x)) (universalTreeRates n) = x := by
  apply Prod.ext
  · funext v
    simp [ratesOverMap,universalTreeRates,rateEvaluation]
  · funext e
    simp [ratesOverMap,universalTreeRates,rateEvaluation]

end HydrologyTree
