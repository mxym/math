import SchurCompletion.PermutationMoments
import Mathlib.GroupTheory.Perm.Cycle.Factors

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

abbrev PositionCycles (k : ℕ) (σ : Equiv.Perm (Fin k)) :=
  Quotient (Equiv.Perm.SameCycle.setoid σ)

instance positionCyclesFintype (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Fintype (PositionCycles k σ) := Fintype.ofFinite _

/-- All cycles, including fixed points, are counted. -/
def positionCycleCount (k : ℕ) (σ : Equiv.Perm (Fin k)) : ℕ :=
  Fintype.card (PositionCycles k σ)

theorem fixedWord_constant_on_cycles (D k : ℕ) (σ : Equiv.Perm (Fin k))
    (w : Word D k) (hw : ∀ i, w (σ i) = w i) (i j : Fin k) (hij : σ.SameCycle i j) :
    w i = w j := by
  have hp (n : ℕ) : ∀ i, w ((σ^n) i) = w i := by
    induction n with
    | zero => intro i; rfl
    | succ n ih =>
      intro i
      rw [pow_succ',Equiv.Perm.mul_apply,hw,ih]
  obtain ⟨n,_,_,hn⟩ := hij.exists_pow_eq σ
  rw [← hn]
  exact (hp n i).symm

/-- Actual fixed computational words are precisely colorings of the actual
cycle quotient. This derives the permutation character rather than assuming it. -/
def fixedWordColorEquiv (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (Function.fixedPoints (positionWordEquiv D k σ)) ≃ (PositionCycles k σ → Fin D) where
  toFun w := Quotient.lift w.val (by
    intro i j hij
    apply fixedWord_constant_on_cycles D k σ w.val ?_ i j hij
    intro i
    exact congrFun w.property i)
  invFun f := ⟨fun i => f (Quotient.mk _ i), by
    apply funext
    intro i
    change f (Quotient.mk _ (σ i)) = f (Quotient.mk _ i)
    congr 1
    exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr Equiv.Perm.SameCycle.rfl)⟩
  left_inv w := by apply Subtype.ext; apply funext; intro i; rfl
  right_inv f := by
    apply funext
    intro q
    induction q using Quotient.inductionOn
    rfl

theorem fixedWordCard_eq_pow_cycleCount (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    fixedWordCard D k σ = D ^ positionCycleCount k σ := by
  classical
  rw [fixedWordCard,← Set.fintypeCard_eq_ncard]
  rw [Fintype.card_congr (fixedWordColorEquiv D k σ),Fintype.card_fun,Fintype.card_fin]
  rfl

/-- Actual finite-dimensional tensor character D raised to the full cycle
count. Valid for every D and k, including zero. -/
theorem copyPermutation_trace_cycleCount (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (copyPermutationMatrix D k σ).trace = (D : ℂ) ^ positionCycleCount k σ := by
  rw [copyPermutation_trace,fixedWordCard_eq_pow_cycleCount,Nat.cast_pow]

theorem flatHaarAverage_permutation_cycle_moment (D s k : ℕ) (hsD : s ≤ D)
    (σ : Equiv.Perm (Fin k)) :
    (copyPermutationMatrix D k σ * flatHaarAverage D s k hsD).trace =
      ((s : ℝ)^k)⁻¹ • (s : ℂ)^positionCycleCount k σ := by
  rw [flatHaarAverage_permutation_moment,fixedWordCard_eq_pow_cycleCount,Nat.cast_pow]

theorem copyPermutation_cycle_gram (D k : ℕ) (σ τ : Equiv.Perm (Fin k)) :
    ((copyPermutationMatrix D k σ)ᴴ * copyPermutationMatrix D k τ).trace =
      (D : ℂ) ^ positionCycleCount k (σ⁻¹*τ) := by
  rw [copyPermutation_gram,fixedWordCard_eq_pow_cycleCount,Nat.cast_pow]

end
end ExtractionSchur
