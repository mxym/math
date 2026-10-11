import APPT.Quantum.Orbit
import Mathlib.LinearAlgebra.Matrix.Kronecker

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem complex_conj_ite (p : Prop) [Decidable p] (z w : ℂ) :
    (starRingEnd ℂ) (if p then z else w) = if p then star z else star w := by
  split_ifs <;> rfl

/-- Local congruence maps, in arbitrary finite bipartite dimensions. -/
def localLift (K : Matrix a a ℂ) : Matrix (a × b) (a × b) ℂ := K.kronecker 1

def localCongruence (P : Matrix (a × b) (a × b) ℂ) (K : Matrix a a ℂ) :=
  (localLift K)ᴴ * P * localLift (b := b) K

theorem localCongruence_posSemidef {P : Matrix (a × b) (a × b) ℂ}
    (hP : P.PosSemidef) (K : Matrix a a ℂ) : (localCongruence P K).PosSemidef :=
  hP.conjTranspose_mul_mul_same _

theorem localCongruence_apply (P : Matrix (a × b) (a × b) ℂ)
    (K : Matrix a a ℂ) (i j : a) (x y : b) :
    localCongruence P K (i,x) (j,y) =
      ∑ s : a, ∑ r : a, star (K r i) * P (r,x) (s,y) * K s j := by
  simp [localCongruence, localLift, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply,
    mul_ite, ite_mul, Finset.sum_mul, Finset.mul_sum, complex_conj_ite]

/-- An elementary local diagonal coordinate projector. -/
def localDiagonal (i : a) : Matrix a a ℂ := fun r s => if r=i ∧ s=i then 1 else 0

/-- The real symmetric or antisymmetric exchange on two local coordinates. -/
def localPair (i j : a) (c : ℝ) : Matrix a a ℂ := fun r s =>
  (if r=i ∧ s=j then 1 else 0) + (if r=j ∧ s=i then (c : ℂ) else 0)

theorem localDiagonal_apply (P : Matrix (a × b) (a × b) ℂ) (t i j : a) (x y : b) :
    localCongruence P (localDiagonal t) (i,x) (j,y) =
      if i=t ∧ j=t then P (t,x) (t,y) else 0 := by
  rw [localCongruence_apply]
  by_cases hi : i=t <;> by_cases hj : j=t <;>
    simp [localDiagonal, hi, hj, mul_ite, ite_mul, complex_conj_ite]

/-- Expanded pair identity; no Hermitian or positivity assumption is needed. -/
theorem localPair_apply (P : Matrix (a × b) (a × b) ℂ)
    (t u i j : a) (c : ℝ) (x y : b) :
    localCongruence P (localPair t u c) (i,x) (j,y) =
      (if i=u ∧ j=u then P (t,x) (t,y) else 0) +
      (if i=u ∧ j=t then (c : ℂ)*P (t,x) (u,y) else 0) +
      (if i=t ∧ j=u then (c : ℂ)*P (u,x) (t,y) else 0) +
      (if i=t ∧ j=t then (c : ℂ)^2*P (u,x) (u,y) else 0) := by
  rw [localCongruence_apply]
  by_cases htu : t=u <;> by_cases hi : i=u <;> by_cases hj : j=u <;>
    by_cases hit : i=t <;> by_cases hjt : j=t <;>
    simp_all [localPair, mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, complex_conj_ite]
    <;> ring

end APPTReview
