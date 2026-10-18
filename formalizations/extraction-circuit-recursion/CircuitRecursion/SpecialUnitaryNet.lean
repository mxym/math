import CircuitRecursion.FiniteNet
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Matrix

open scoped Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

theorem specialUnitary_isCompact {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    IsCompact (Matrix.specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  have hc : IsClosed (Matrix.specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
    change IsClosed ((unitary (Matrix ι ι ℂ) : Set (Matrix ι ι ℂ))∩{A | A.det=1})
    exact isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)
  apply (isCompact_closedBall (0 : Matrix ι ι ℂ) 1).of_isClosed_subset hc
  intro A hA
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (CStarRing.norm_of_mem_unitary hA.1).le

/-- The compactness needed for calibration is proved for the actual finite
matrix group, in the same Euclidean operator norm used for circuit error. -/
theorem specialUnitary_compactSpace {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    CompactSpace (Matrix.specialUnitaryGroup ι ℂ) :=
  isCompact_iff_compactSpace.mp specialUnitary_isCompact

/-- Inverse-closed SU(2) universality alone yields one fixed finite basic
net with a uniform actual word-length bound. No calibration premise is used. -/
theorem su2_uniform_instructionLength {m : ℕ}
    (G : Fin m → Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set (Matrix.specialUnitaryGroup (Fin 2) ℂ)))
    (ε : ℝ) (hε : 0<ε) :
    ∃ L : ℕ,∀ U : Matrix.specialUnitaryGroup (Fin 2) ℂ,∃ w : List (Fin m),
      w.length≤L ∧ ‖(U : Matrix (Fin 2) (Fin 2) ℂ)-
        (instructionWordValue (H := Matrix.specialUnitaryGroup (Fin 2) ℂ) G w :
          Matrix (Fin 2) (Fin 2) ℂ)‖<ε := by
  letI : CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) := specialUnitary_compactSpace
  obtain ⟨L,hL⟩ := uniform_instructionLength G hinv huniversal ε hε
  refine ⟨L,fun U => ?_⟩
  obtain ⟨w,hw,he⟩ := hL U
  refine ⟨w,hw,?_⟩
  simpa only [Subtype.dist_eq,dist_eq_norm] using he

end CircuitRecursion
