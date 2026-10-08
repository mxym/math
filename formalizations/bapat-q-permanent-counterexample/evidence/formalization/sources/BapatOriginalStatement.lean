import BapatReality
import BapatContinuity
import Mathlib.LinearAlgebra.Matrix.IsDiag

open scoped ComplexOrder
open Set

set_option autoImplicit false

namespace BapatRankTwo

/-- Mitchell (2020), p. 915: non-diagonal complex Hermitian positive definite
matrices have strictly increasing q-permanents on the original interval. -/
def OriginalBapatConjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosDef → ¬ A.IsDiag →
    StrictMonoOn (fun q : ℝ => (qPermanent A (q : ℂ)).re) (Icc (-1) 1)

theorem perturb_not_isDiag {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ¬ A.IsDiag) (δ : ℝ) : ¬ (perturb A δ).IsDiag := by
  intro hd
  apply hA
  intro i j hij
  have hz := hd hij
  simpa [perturb, Matrix.diagonal_apply_ne _ hij] using hz

/-- A PSD negative endpoint derivative, together with non-diagonality,
refutes the original strict formulation including all its hypotheses. -/
theorem originalBapatConjecture_false_of_psd_derivative_neg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (hdiag : ¬ A.IsDiag)
    (hneg : (realQPolynomial A).derivative.eval 1 < 0) :
    ¬ OriginalBapatConjecture := by
  obtain ⟨δ, hδ, hPD, a, ha, b, hb, hab, hdec⟩ :=
    exists_posDef_interior_counterexample_of_psd_derivative_neg hA hneg
  intro hc
  have hinc := hc n (perturb A δ) hPD (perturb_not_isDiag hdiag δ)
    ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩ hab
  exact (not_lt_of_gt hinc) hdec

end BapatRankTwo
