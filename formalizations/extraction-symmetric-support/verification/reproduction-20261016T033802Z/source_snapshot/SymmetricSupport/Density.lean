import SymmetricSupport.PureSpan
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped BigOperators ComplexOrder
open Matrix

namespace SymmetricSupport

noncomputable section

theorem partitionProjector_trace {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (label : α → β)
    (hsurj : Function.Surjective label) :
    (partitionProjector label).trace = (Fintype.card β : ℂ) := by
  rw [partitionProjector, Matrix.trace_mul_comm, average_columns label hsurj]
  simp

theorem symmetricProjector_trace (D k : ℕ) :
    (symmetricProjector D k).trace = (Fintype.card (Sym (Fin D) k) : ℂ) :=
  partitionProjector_trace _ (occupation_surjective D k)

theorem symmetricProjector_posSemidef (D k : ℕ) :
    (symmetricProjector D k).PosSemidef := by
  have h : (symmetricProjector D k)ᴴ * symmetricProjector D k = symmetricProjector D k := by
    rw [(symmetricProjector_hermitian D k).eq, symmetricProjector_idempotent]
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- A concrete matrix on the original tensor-power coordinates. Its equality to a
pure-state Haar average is a separate theorem and is not assumed in its definition. -/
def symmetricState (D k : ℕ) : Matrix (Word D k) (Word D k) ℂ :=
  ((Fintype.card (Sym (Fin D) k) : ℝ)⁻¹) • symmetricProjector D k

theorem symmetricState_posSemidef (D k : ℕ) :
    (symmetricState D k).PosSemidef :=
  (symmetricProjector_posSemidef D k).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem occupation_card_pos (D k : ℕ) (hD : 0 < D) :
    0 < Fintype.card (Sym (Fin D) k) :=
  Fintype.card_pos_iff.mpr ⟨Sym.replicate k ⟨0, hD⟩⟩

theorem symmetricState_trace (D k : ℕ) (hD : 0 < D) :
    (symmetricState D k).trace = 1 := by
  have hr : (Fintype.card (Sym (Fin D) k) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (occupation_card_pos D k hD)
  simp [symmetricState, Matrix.trace_smul, symmetricProjector_trace,
    RCLike.real_smul_eq_coe_mul, hr]

theorem symmetricState_purity (D k : ℕ) :
    (symmetricState D k * symmetricState D k).trace =
      (Fintype.card (Sym (Fin D) k) : ℂ)⁻¹ := by
  simp only [symmetricState, Matrix.smul_mul, Matrix.mul_smul,
    symmetricProjector_idempotent, Matrix.trace_smul, symmetricProjector_trace]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, RCLike.ofReal_natCast]
  by_cases hr : Fintype.card (Sym (Fin D) k) = 0
  · simp [hr]
  · have hr' : (Fintype.card (Sym (Fin D) k) : ℂ) ≠ 0 := by exact_mod_cast hr
    field_simp

/-- Actual pure iid input density before imposing normalization. -/
def purePowerDensity (D k : ℕ) (z : Fin D → ℂ) : Matrix (Word D k) (Word D k) ℂ :=
  Matrix.vecMulVec (purePower D k z) (star (purePower D k z))

theorem purePowerDensity_posSemidef (D k : ℕ) (z : Fin D → ℂ) :
    (purePowerDensity D k z).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem purePowerDensity_trace (D k : ℕ) (z : Fin D → ℂ) :
    (purePowerDensity D k z).trace = (∑ i, z i * star (z i)) ^ k := by
  simp only [purePowerDensity, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply,
    Pi.star_apply, purePower, star_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun i : Fin D => z i * star (z i)) k).symm

theorem purePowerDensity_trace_one (D k : ℕ) (z : Fin D → ℂ)
    (hz : ∑ i, z i * star (z i) = 1) :
    (purePowerDensity D k z).trace = 1 := by
  rw [purePowerDensity_trace, hz, one_pow]

theorem purePowerDensity_supported (D k : ℕ) (z : Fin D → ℂ) :
    symmetricProjector D k * purePowerDensity D k z * symmetricProjector D k =
      purePowerDensity D k z := by
  have hl : symmetricProjector D k * purePowerDensity D k z = purePowerDensity D k z := by
    rw [purePowerDensity, Matrix.mul_vecMulVec, symmetricProjector_fixes_purePower]
  have hr : purePowerDensity D k z * symmetricProjector D k = purePowerDensity D k z := by
    have hc := congrArg Matrix.conjTranspose hl
    simpa only [Matrix.conjTranspose_mul,
      (symmetricProjector_hermitian D k).eq,
      (purePowerDensity_posSemidef D k z).isHermitian.eq] using hc
  rw [hl, hr]

end
end SymmetricSupport
