import OperationalCompletion.CapacitySets
import APPTReview.CompactMaximum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

open scoped BigOperators ComplexOrder Topology Matrix.Norms.L2Operator
open Matrix ExtractionSpectrum
namespace ExtractionAPPT
noncomputable section
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A genuine matrix functional, including zero eigenvalues, defined using the
continuous function -x log x and the actual continuous functional calculus. -/
def quantumEntropy (A : Matrix ι ι ℂ) : ℝ := (cfc Real.negMulLog A).trace.re

theorem trace_cfc (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose]
  have hu : (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * hA.eigenvectorUnitary = 1 :=
    hA.eigenvectorUnitary.property.1
  rw [hu, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

theorem quantumEntropy_eq_spectral (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    quantumEntropy A = entropy hA.eigenvalues := by
  rw [quantumEntropy, trace_cfc A hA, Complex.re_sum,
    ExtractionDeviation.entropy_eq_sum_negMulLog]
  simp only [Complex.ofReal_re]

/-- Entropy continuity is proved internally via CFC, rather than imposed as
an optimizer/continuity assumption. -/
theorem continuousOn_quantumEntropy :
    ContinuousOn (quantumEntropy : Matrix ι ι ℂ → ℝ) {A | A.IsHermitian} := by
  have hc : ContinuousOn (fun A : Matrix ι ι ℂ => cfc Real.negMulLog A) {A | A.IsHermitian} := by
    exact continuous_id.continuousOn.cfc_of_mem_nhdsSet Real.negMulLog
      (s := Set.univ) (by simp) (fun _ h => h) Real.continuous_negMulLog.continuousOn
  have ht : Continuous (fun A : Matrix ι ι ℂ => A.trace.re) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  exact ht.comp_continuousOn hc

def reindexStarAlgEquiv (e : κ ≃ ι) :
    Matrix ι ι ℂ ≃⋆ₐ[ℝ] Matrix κ κ ℂ where
  __ := Matrix.reindexAlgEquiv ℝ ℂ e.symm
  map_star' A := by ext i j; rfl
  map_smul' c A := rfl

theorem cfc_submatrix (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (e : κ ≃ ι) :
    cfc Real.negMulLog (A.submatrix e e) = (cfc Real.negMulLog A).submatrix e e := by
  have hc : Continuous (reindexStarAlgEquiv e) := by
    change Continuous (fun A : Matrix ι ι ℂ => A.submatrix e e)
    fun_prop
  exact (StarAlgHomClass.map_cfc (reindexStarAlgEquiv e) Real.negMulLog A
    Real.continuous_negMulLog.continuousOn hc hA.isSelfAdjoint
    (hA.submatrix e).isSelfAdjoint).symm

theorem quantumEntropy_submatrix (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : κ ≃ ι) :
    quantumEntropy (A.submatrix e e) = quantumEntropy A := by
  rw [quantumEntropy, cfc_submatrix A hA e, quantumEntropy]
  exact congrArg Complex.re (e.sum_comp (fun i => cfc Real.negMulLog A i i))

/-- Explicit coordinate equivalence between the physical product register and
the flattened register used by the extraction capacity endpoints. -/
def flatten (m n : ℕ) (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :
    Matrix (Fin (m*n)) (Fin (m*n)) ℂ :=
  A.submatrix finProdFinEquiv.symm finProdFinEquiv.symm

theorem flatten_density {m n : ℕ} (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hA : APPT.Quantum.IsDensity A) : (flatten m n A).PosSemidef ∧ (flatten m n A).trace=1 := by
  refine ⟨hA.1.submatrix _, ?_⟩
  exact (finProdFinEquiv.symm.sum_comp (fun i => A i i)).trans hA.2

theorem flatten_entropy {m n : ℕ} (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hA : A.IsHermitian) :
    quantumEntropy (flatten m n A) = quantumEntropy A :=
  quantumEntropy_submatrix A hA finProdFinEquiv.symm

theorem flatten_spectral_entropy {m n : ℕ} (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
    (hA : APPT.Quantum.IsDensity A) :
    entropy (flatten_density A hA).1.isHermitian.eigenvalues = quantumEntropy A := by
  rw [← quantumEntropy_eq_spectral, flatten_entropy A hA.1.isHermitian]

def apptEntropyValues (m n : ℕ) : Set ℝ :=
  quantumEntropy '' APPTReview.physicalAPPTStates m n

def apptMinEntropy (m n : ℕ) : ℝ := sInf (apptEntropyValues m n)

theorem continuousOn_appt_entropy (m n : ℕ) :
    ContinuousOn quantumEntropy (APPTReview.physicalAPPTStates m n) :=
  continuousOn_quantumEntropy.mono (fun _ h => h.1.1.isHermitian)

/-- An actual physical APPT state attains the true entropy minimum. -/
theorem exists_appt_entropy_isLeast {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ A ∈ APPTReview.physicalAPPTStates m n,
      IsLeast (apptEntropyValues m n) (quantumEntropy A) := by
  obtain ⟨A,hA,hmin⟩ := (APPTReview.isCompact_physicalAPPTStates m n).exists_isMinOn
    (APPTReview.physicalAPPTStates_nonempty hm hmn) (continuousOn_appt_entropy m n)
  refine ⟨A,hA,⟨⟨A,hA,rfl⟩,?_⟩⟩
  rintro x ⟨B,hB,rfl⟩
  exact hmin hB

theorem exists_appt_entropy_eq_inf {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ A ∈ APPTReview.physicalAPPTStates m n, quantumEntropy A = apptMinEntropy m n := by
  obtain ⟨A,hA,hmin⟩ := exists_appt_entropy_isLeast hm hmn
  exact ⟨A,hA,hmin.csInf_eq.symm⟩

end
end ExtractionAPPT
