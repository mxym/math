import APPTReview.FixedLocalLimit
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.MetricSpace.ProperSpace

open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Partial transpose is continuous on the original complex matrix space. -/
theorem continuous_partialTranspose : Continuous
    (APPT.Quantum.partialTranspose : Matrix (a × b) (a × b) ℂ → Matrix (a × b) (a × b) ℂ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : Matrix (a × b) (a × b) ℂ => A (j.1,i.2) (i.1,j.2))
  fun_prop

/-- Closedness retains the quantifier over every global unitary. -/
theorem isClosed_absolutelyPPT : IsClosed
    {A : Matrix (a × b) (a × b) ℂ | APPT.Quantum.AbsolutelyPPT A} := by
  change IsClosed {A : Matrix (a × b) (a × b) ℂ | ∀ U : Matrix.unitaryGroup (a × b) ℂ,
    (APPT.Quantum.partialTranspose ((U : Matrix (a × b) (a × b) ℂ)*A*(U : Matrix (a × b) (a × b) ℂ)ᴴ)).PosSemidef}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro U
  apply Matrix.posSemidef_is_closed.preimage
  apply continuous_partialTranspose.comp
  fun_prop

theorem continuous_quantum_trace : Continuous
    (fun A : Matrix (a × b) (a × b) ℂ => A.trace) := by
  unfold Matrix.trace Matrix.diag
  fun_prop

theorem continuous_quantum_purity : Continuous
    (APPT.Quantum.purity : Matrix (a × b) (a × b) ℂ → ℝ) := by
  unfold APPT.Quantum.purity Matrix.trace Matrix.diag
  fun_prop

theorem isClosed_density : IsClosed
    {A : Matrix (a × b) (a × b) ℂ | APPT.Quantum.IsDensity A} := by
  change IsClosed ({A : Matrix (a × b) (a × b) ℂ | A.PosSemidef} ∩ {A | A.trace=1})
  exact Matrix.posSemidef_is_closed.inter (isClosed_eq continuous_quantum_trace continuous_const)

/-- On Hermitian matrices the squared-entry sum equals the original purity. -/
theorem purity_eq_entry_norm_sum {A : Matrix (a × b) (a × b) ℂ} (hA : A.IsHermitian) :
    APPT.Quantum.purity A = ∑ i, ∑ j, ‖A i j‖^2 := by
  unfold APPT.Quantum.purity
  have he : A*A=A*Aᴴ := by rw [hA.eq]
  rw [he]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.normSq_apply, Complex.sq_norm]

/-- Every entry of a density matrix lies in the closed complex unit disk. -/
theorem density_entry_norm_le_one {A : Matrix (a × b) (a × b) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (i j : a × b) : ‖A i j‖≤1 := by
  have hp := (density_purity_unit_interval hρ).2
  rw [purity_eq_entry_norm_sum hρ.1.isHermitian] at hp
  have hrow : ‖A i j‖^2 ≤ ∑ k, ‖A i k‖^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (‖A i k‖)) (Finset.mem_univ j)
  have hfull : (∑ k, ‖A i k‖^2) ≤ ∑ l, ∑ k, ‖A l k‖^2 :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg (‖A l k‖))) (Finset.mem_univ i)
  nlinarith [hrow.trans hfull, norm_nonneg (A i j)]

theorem density_norm_le_one {A : Matrix (a × b) (a × b) ℂ}
    (hρ : APPT.Quantum.IsDensity A) : ‖A‖≤1 :=
  (Matrix.norm_le_iff (by norm_num)).2 (density_entry_norm_le_one hρ)

/-- Compactness is proved for the physical state set, not an assumed spectral model. -/
theorem isCompact_density : IsCompact
    {A : Matrix (a × b) (a × b) ℂ | APPT.Quantum.IsDensity A} := by
  apply (isCompact_closedBall (0 : Matrix (a × b) (a × b) ℂ) 1).of_isClosed_subset isClosed_density
  intro A hA
  simpa [Metric.mem_closedBall, dist_zero_right] using density_norm_le_one hA

def physicalAPPTStates (m n : ℕ) : Set (Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) :=
  {A | APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A}

theorem isCompact_physicalAPPTStates (m n : ℕ) : IsCompact (physicalAPPTStates m n) :=
  isCompact_density.inter_right isClosed_absolutelyPPT

end APPTReview
