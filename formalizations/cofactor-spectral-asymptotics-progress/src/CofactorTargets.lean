import CofactorIndicator
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Exact variational extrema for the logarithmic theorem. Real directions
still allow arbitrary complex Hermitian matrices. These are definitions,
not hypotheses supplying any of the upper or lower estimates. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
noncomputable section

def vectorNormSq {n : ℕ} (w : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (w i)

def cofactorRayleighRatio {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) : ℝ :=
  (∑ i, ∑ j, star (w i) * compound A i j * w j).re /
    (A.permanent.re * vectorNormSq w)

def psdAdmissible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A.PosSemidef ∧ 0 < A.permanent.re

def rankTwoCorrelationAdmissible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  psdAdmissible A ∧ (∀ i, A i i = 1) ∧ A.rank = 2

def pdCorrelationAdmissible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  A.PosDef ∧ 0 < A.permanent.re ∧ ∀ i, A i i = 1

def complexRayleighValues (n : ℕ) (P : Matrix (Fin n) (Fin n) ℂ → Prop) : Set ℝ :=
  {r | ∃ A, P A ∧ ∃ w : Fin n → ℂ, 0 < vectorNormSq w ∧ r = cofactorRayleighRatio A w}

def realRayleighValues (n : ℕ) (P : Matrix (Fin n) (Fin n) ℂ → Prop) : Set ℝ :=
  {r | ∃ A, P A ∧ ∃ w : Fin n → ℝ,
    0 < vectorNormSq (fun i => (w i : ℂ)) ∧
      r = cofactorRayleighRatio A (fun i => (w i : ℂ))}

def complexExtremum (n : ℕ) : ℝ := sSup (complexRayleighValues n psdAdmissible)
def realExtremum (n : ℕ) : ℝ := sSup (realRayleighValues n psdAdmissible)
def rankTwoComplexExtremum (n : ℕ) : ℝ :=
  sSup (complexRayleighValues n rankTwoCorrelationAdmissible)
def rankTwoRealExtremum (n : ℕ) : ℝ := sSup (realRayleighValues n rankTwoCorrelationAdmissible)
def pdComplexExtremum (n : ℕ) : ℝ := sSup (complexRayleighValues n pdCorrelationAdmissible)
def pdRealExtremum (n : ℕ) : ℝ := sSup (realRayleighValues n pdCorrelationAdmissible)

end
end CofactorSpectral
