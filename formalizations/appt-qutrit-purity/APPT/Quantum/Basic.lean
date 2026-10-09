import APPT.Core

open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

variable {a b : Type*}

/-- Partial transpose on the first tensor factor, in the product basis. -/
def partialTranspose (A : Matrix (a × b) (a × b) ℂ) :
    Matrix (a × b) (a × b) ℂ := fun i j => A (j.1, i.2) (i.1, j.2)

@[simp] theorem partialTranspose_apply (A : Matrix (a × b) (a × b) ℂ)
    (i j : a) (x y : b) : partialTranspose A (i,x) (j,y) = A (j,x) (i,y) := rfl

@[simp] theorem partialTranspose_involutive (A : Matrix (a × b) (a × b) ℂ) :
    partialTranspose (partialTranspose A) = A := rfl

@[simp] theorem partialTranspose_add (A B : Matrix (a × b) (a × b) ℂ) :
    partialTranspose (A+B) = partialTranspose A + partialTranspose B := rfl

@[simp] theorem partialTranspose_sub (A B : Matrix (a × b) (a × b) ℂ) :
    partialTranspose (A-B) = partialTranspose A - partialTranspose B := rfl

@[simp] theorem partialTranspose_smul (c : ℝ) (A : Matrix (a × b) (a × b) ℂ) :
    partialTranspose (c • A) = c • partialTranspose A := rfl

@[simp] theorem partialTranspose_conjTranspose (A : Matrix (a × b) (a × b) ℂ) :
    partialTranspose Aᴴ = (partialTranspose A)ᴴ := rfl

@[simp] theorem partialTranspose_one [DecidableEq a] [DecidableEq b] :
    partialTranspose (1 : Matrix (a × b) (a × b) ℂ) = 1 := by
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases hij : i=j <;> by_cases hxy : x=y <;>
    simp_all [partialTranspose, Matrix.one_apply, eq_comm]

theorem partialTranspose_isHermitian {A : Matrix (a × b) (a × b) ℂ}
    (h : A.IsHermitian) : (partialTranspose A).IsHermitian := by
  change (partialTranspose A)ᴴ = partialTranspose A
  rw [← partialTranspose_conjTranspose, h.eq]

variable [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Density matrices have their actual PSD and trace-one semantics. -/
def IsDensity (A : Matrix (a × b) (a × b) ℂ) : Prop :=
  A.PosSemidef ∧ A.trace = 1

/-- APPT quantifies over every global unitary, not spectral surrogate constraints. -/
def AbsolutelyPPT (A : Matrix (a × b) (a × b) ℂ) : Prop :=
  ∀ U : Matrix.unitaryGroup (a × b) ℂ,
    (partialTranspose ((U : Matrix (a × b) (a × b) ℂ) * A *
      (U : Matrix (a × b) (a × b) ℂ)ᴴ)).PosSemidef

/-- The actual trace-square purity. -/
def purity (A : Matrix (a × b) (a × b) ℂ) : ℝ := (A*A).trace.re

theorem absolutelyPPT_isPPT {A : Matrix (a × b) (a × b) ℂ}
    (h : AbsolutelyPPT A) : (partialTranspose A).PosSemidef := by
  simpa using h 1

@[simp] theorem partialTranspose_trace (A : Matrix (a × b) (a × b) ℂ) :
    (partialTranspose A).trace = A.trace := rfl

end APPT.Quantum
