import Entry002.PrimeIdealPowerSummation
import Mathlib.NumberTheory.LSeries.Convolution

/-! The actual Dedekind-zeta norm fibers. The raw coefficient at zero counts
the zero ideal. LSeries handles index zero separately. -/

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- All integral ideals of a prescribed absolute norm, including the zero
ideal at norm zero. -/
def idealNormFiber (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_eq n).toFinset

/-- The raw coefficient of mathlib's Dedekind zeta L-series. -/
def idealNormCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

def idealNormCoefficient (n : ℕ) : ℝ := (idealNormCount K n : ℝ)

@[simp] theorem mem_idealNormFiber (n : ℕ) (I : Ideal (𝓞 K)) :
    I ∈ idealNormFiber K n ↔ Ideal.absNorm I = n := by
  simp [idealNormFiber]

end

end Entry002
