import CircuitCompletion.FidelityError
import CircuitCompletion.Semantics
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
namespace CircuitCompletion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem vectorSquare_eq_norm_sq (v : ι → ℂ) :
    vectorSquare v=‖(EuclideanSpace.equiv ι ℂ).symm v‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm]
  rfl

theorem vectorSquare_unitary (U : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    vectorSquare ((U : Matrix ι ι ℂ)*ᵥv)=vectorSquare v := by
  have hU : (U : Matrix ι ι ℂ)ᴴ*U=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have h := congrArg Matrix.trace (Extraction.congruence_pure (U : Matrix ι ι ℂ) v)
  change ((U : Matrix ι ι ℂ)*pureMatrix v*(U : Matrix ι ι ℂ)ᴴ).trace=
    (pureMatrix ((U : Matrix ι ι ℂ)*ᵥv)).trace at h
  rw [Matrix.trace_mul_cycle,hU,Matrix.one_mul,pureMatrix_trace,pureMatrix_trace] at h
  exact Complex.ofReal_injective h.symm

/-- Euclidean operator error on the original matrix controls the actual input
vector uniformly in the number of original wires. -/
theorem operator_error_controls_vector (U V : Matrix.unitaryGroup ι ℂ)
    (z : ι → ℂ) (hz : vectorSquare z=1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hUV : ‖(U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)‖ ≤ δ) :
    squaredDistance ((U : Matrix ι ι ℂ)*ᵥz) ((V : Matrix ι ι ℂ)*ᵥz) ≤ δ^2 := by
  let x := (EuclideanSpace.equiv ι ℂ).symm z
  let w := (EuclideanSpace.equiv ι ℂ).symm (((V : Matrix ι ι ℂ)-(U : Matrix ι ι ℂ))*ᵥz)
  have hx : ‖x‖=1 := by
    have hs : ‖x‖^2=1 := (vectorSquare_eq_norm_sq z).symm.trans hz
    nlinarith [norm_nonneg x]
  have he := Matrix.l2_opNorm_mulVec ((V : Matrix ι ι ℂ)-(U : Matrix ι ι ℂ)) x
  change ‖w‖ ≤ ‖(V : Matrix ι ι ℂ)-(U : Matrix ι ι ℂ)‖*‖x‖ at he
  rw [hx,mul_one,norm_sub_rev] at he
  have hw := he.trans hUV
  change vectorSquare (((V : Matrix ι ι ℂ)*ᵥz)-((U : Matrix ι ι ℂ)*ᵥz)) ≤ _
  rw [← Matrix.sub_mulVec,vectorSquare_eq_norm_sq]
  change ‖w‖^2 ≤ δ^2
  nlinarith [norm_nonneg w]

/-- A literal list replacement has additive actual operator error; the cost
is the length of the replaced list, not a field assumed to bound a matrix. -/
theorem compiled_word_error {n : ℕ} (compile : Gate n → Circuit n) (a : Circuit n) :
    ‖(denote (a.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)-denote a‖ ≤
      (a.map (fun g => ‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-g.denote‖)).sum := by
  induction a with
  | nil => simp [denote]
  | cons g gs ih =>
    simp only [List.flatMap_cons,denote_append,denote_cons,Matrix.UnitaryGroup.mul_val,
      List.map_cons,List.sum_cons]
    have he :
        (denote (gs.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)*denote (compile g)-
          (denote gs : Matrix (Bits n) (Bits n) ℂ)*g.denote=
        ((denote (gs.flatMap compile) : Matrix (Bits n) (Bits n) ℂ)-denote gs)*denote (compile g)+
          (denote gs : Matrix (Bits n) (Bits n) ℂ)*((denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-g.denote) := by
      noncomm_ring
    rw [he]
    exact (norm_add_le _ _).trans (by
      rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
      simpa only [add_comm] using add_le_add_right ih
        ‖(denote (compile g) : Matrix (Bits n) (Bits n) ℂ)-g.denote‖)

theorem compiled_word_length {n : ℕ} (compile : Gate n → Circuit n) (a : Circuit n) :
    (a.flatMap compile).length=(a.map (fun g => (compile g).length)).sum := by
  induction a with
  | nil => rfl
  | cons g gs ih => simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,ih]

end CircuitCompletion
