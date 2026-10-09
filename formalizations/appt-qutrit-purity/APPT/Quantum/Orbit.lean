import APPT.Quantum.Basic
set_option maxHeartbeats 1500000
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem absolutelyPPT_smul {A : Matrix (a × b) (a × b) ℂ}
    (hA : AbsolutelyPPT A) {c : ℝ} (hc : 0 ≤ c) : AbsolutelyPPT (c • A) := by
  intro U
  simpa [Matrix.mul_smul, Matrix.smul_mul] using (hA U).smul hc

theorem absolutelyPPT_conjugate {A : Matrix (a × b) (a × b) ℂ}
    (hA : AbsolutelyPPT A) (V : Matrix.unitaryGroup (a × b) ℂ) :
    AbsolutelyPPT ((V : Matrix (a × b) (a × b) ℂ)*A*
      (V : Matrix (a × b) (a × b) ℂ)ᴴ) := by
  intro U
  have h := hA (U*V)
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h

theorem trace_unitaryConjugate (A : Matrix (a × b) (a × b) ℂ)
    (U : Matrix.unitaryGroup (a × b) ℂ) :
    ((U : Matrix (a × b) (a × b) ℂ)*A*
      (U : Matrix (a × b) (a × b) ℂ)ᴴ).trace = A.trace := by
  have hu : (U : Matrix (a × b) (a × b) ℂ)ᴴ*U=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem isDensity_unitaryConjugate {A : Matrix (a × b) (a × b) ℂ}
    (hA : IsDensity A) (U : Matrix.unitaryGroup (a × b) ℂ) :
    IsDensity ((U : Matrix (a × b) (a × b) ℂ)*A*
      (U : Matrix (a × b) (a × b) ℂ)ᴴ) :=
  ⟨hA.1.mul_mul_conjTranspose_same (U : Matrix (a × b) (a × b) ℂ), (trace_unitaryConjugate A U).trans hA.2⟩

theorem purity_unitaryConjugate (A : Matrix (a × b) (a × b) ℂ)
    (U : Matrix.unitaryGroup (a × b) ℂ) :
    purity ((U : Matrix (a × b) (a × b) ℂ)*A*
      (U : Matrix (a × b) (a × b) ℂ)ᴴ) = purity A := by
  have hu : (U : Matrix (a × b) (a × b) ℂ)ᴴ*U=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have he : ((U : Matrix (a × b) (a × b) ℂ)*A*(U : Matrix (a × b) (a × b) ℂ)ᴴ)*
      ((U : Matrix (a × b) (a × b) ℂ)*A*(U : Matrix (a × b) (a × b) ℂ)ᴴ) =
      (U : Matrix (a × b) (a × b) ℂ)*(A*A)*(U : Matrix (a × b) (a × b) ℂ)ᴴ := by
    calc
      _ = (U : Matrix (a × b) (a × b) ℂ)*A*((U : Matrix (a × b) (a × b) ℂ)ᴴ*U)*A*(U : Matrix (a × b) (a × b) ℂ)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu]; simp [Matrix.mul_assoc]
  unfold purity
  rw [he, trace_unitaryConjugate]

end APPT.Quantum
