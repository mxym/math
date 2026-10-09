import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix

namespace ECQC

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A density matrix is positive semidefinite and has trace one. -/
def IsDensity (A : Matrix n n ℂ) : Prop := A.PosSemidef ∧ A.trace = 1

/-- The actual rank-one operator associated to a state vector. -/
def pureState (v : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec v (star v)

theorem pureState_posSemidef (v : n → ℂ) : (pureState v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

/-- The von Neumann entropy, expressed through Mathlib's spectral theorem. -/
noncomputable def vonNeumannEntropy (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ :=
  ∑ i, -(hA.eigenvalues i) * Real.log (hA.eigenvalues i)

/-- Polynomial relations of a Hermitian matrix constrain its actual eigenvalues. -/
theorem eigenvalue_zero_or_scale {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (a : ℝ) (hAA : A * A = a • A) (i : n) :
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = a := by
  let v : n → ℂ := ⇑(hA.eigenvectorBasis i)
  have hv : v ≠ 0 := by
    intro hz
    have hnorm := hA.eigenvectorBasis.orthonormal.1 i
    have hvz : hA.eigenvectorBasis i = 0 := by
      apply PiLp.ext
      intro j
      exact congrFun hz j
    rw [hvz, norm_zero] at hnorm
    norm_num at hnorm
  have heig : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
  have heq := congrArg (fun B : Matrix n n ℂ => B *ᵥ v) hAA
  rw [← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, heig,
    Matrix.smul_mulVec, heig, smul_smul, smul_smul] at heq
  have hs : hA.eigenvalues i * hA.eigenvalues i = a * hA.eigenvalues i :=
    (smul_left_injective ℝ hv) heq
  have hz : hA.eigenvalues i * (hA.eigenvalues i - a) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- A trace-one scaled projection has entropy -log(a), proved using actual eigenvalues. -/
theorem entropy_scaled_projection {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (a : ℝ) (hAA : A * A = a • A) (htrace : A.trace = 1) :
    vonNeumannEntropy A hA = -Real.log a := by
  have hterm (i : n) : -(hA.eigenvalues i) * Real.log (hA.eigenvalues i) =
      hA.eigenvalues i * (-Real.log a) := by
    rcases eigenvalue_zero_or_scale hA a hAA i with h | h
    · simp [h]
    · rw [h]; ring
  have hsum : ∑ i, hA.eigenvalues i = 1 := by
    have ht := hA.trace_eq_sum_eigenvalues
    rw [htrace] at ht
    have hre := congrArg Complex.re ht
    simpa using hre.symm
  simp only [vonNeumannEntropy, hterm, ← Finset.sum_mul, hsum, one_mul]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Partial trace over the second tensor factor, in the standard product basis. -/
def partialTraceRight (A : Matrix (n × m) (n × m) ℂ) : Matrix n n ℂ :=
  fun i j => ∑ k, A (i,k) (j,k)

/-- Partial trace over the first tensor factor. -/
def partialTraceLeft (A : Matrix (n × m) (n × m) ℂ) : Matrix m m ℂ :=
  fun i j => ∑ k, A (k,i) (k,j)

/-- The Born expectation of a rank-one projector for the outcome vector v. -/
def born (A : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  (dotProduct (star v) (A *ᵥ v)).re

end ECQC
