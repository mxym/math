import APPT.Quantum.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum
variable {b : Type*} [Fintype b] [DecidableEq b]

def lift (K : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3 × b) (Fin 3 × b) ℂ :=
  K.kronecker 1

theorem lift_mul_apply (K : Matrix (Fin 3) (Fin 3) ℂ)
    (P : Matrix (Fin 3 × b) (Fin 3 × b) ℂ) (i j : Fin 3) (x y : b) :
    (lift (b := b) K * P) (i,x) (j,y) = ∑ r : Fin 3, K i r * P (r,x) (j,y) := by
  simp [Matrix.mul_apply, lift, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul]

theorem mul_lift_apply (P : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) (x y : b) :
    (P * lift (b := b) K) (i,x) (j,y) = ∑ r : Fin 3, P (i,x) (r,y) * K r j := by
  simp [Matrix.mul_apply, lift, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.one_apply, mul_ite, ite_mul]

@[simp] theorem lift_conjTranspose (K : Matrix (Fin 3) (Fin 3) ℂ) :
    lift (b := b) Kᴴ = (lift K)ᴴ := by
  simp [lift, Matrix.conjTranspose_kronecker]

def sandwich (P : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)
    (K : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3 × b) (Fin 3 × b) ℂ :=
  (lift K)ᴴ * P * lift (b := b) K

theorem sandwich_apply (P : Matrix (Fin 3 × b) (Fin 3 × b) ℂ)
    (K : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) (x y : b) :
    sandwich P K (i,x) (j,y) =
      ∑ s : Fin 3, (∑ r : Fin 3, star (K r i) * P (r,x) (s,y)) * K s j := by
  rw [sandwich, ← lift_conjTranspose, mul_lift_apply]
  simp_rw [lift_mul_apply, Matrix.conjTranspose_apply]

theorem sandwich_posSemidef {P : Matrix (Fin 3 × b) (Fin 3 × b) ℂ}
    (hP : P.PosSemidef) (K : Matrix (Fin 3) (Fin 3) ℂ) :
    (sandwich P K).PosSemidef := hP.conjTranspose_mul_mul_same (lift K)

end APPT.Quantum
