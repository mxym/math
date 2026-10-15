import Extraction.BellPacking
import Mathlib.Tactic.FieldSimp

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

variable {d u v : Type*} [Fintype d] [Fintype u] [Fintype v]
  [DecidableEq d] [DecidableEq u] [DecidableEq v]

/-- An actual rectangular matrix encoding one logical basis into Bell labels. -/
def codeEmbedding (c : ℂ) : Matrix ((d × u) × (d × v)) (u × v) ℂ :=
  fun p q => bellCode c q.1 q.2 p

/-- Each product Kraus branch reads exactly one logical label. -/
theorem productEraseKraus_embedding (c : ℂ) (z q : u × v) (p : d × d) :
    (productEraseKraus (d := d) (u := u) (v := v) z * codeEmbedding (d := d) (u := u) (v := v) c) p q =
      if z = q then bellVector (d := d) c p else 0 := by
  have h := congrFun
    (productEraseKraus_code (d := d) c q.1 z.1 q.2 z.2) p
  simpa only [codeEmbedding, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Prod.mk.eta, ← Prod.ext_iff, ite_apply, Pi.zero_apply] using h

/-- A single Kraus readout kills every other logical coordinate. -/
theorem single_readout_congruence
    (B : Matrix (d × d) (u × v) ℂ) (w : d × d → ℂ) (z : u × v)
    (hB : ∀ p q, B p q = if z = q then w p else 0)
    (X : Matrix (u × v) (u × v) ℂ) :
    B * X * Bᴴ = X z z • Matrix.vecMulVec w (star w) := by
  ext p q
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hB, Matrix.vecMulVec_apply,
    Matrix.smul_apply, apply_ite, ite_mul, mul_ite, eq_comm]
  ring

/-- Coherent packing: every logical matrix, including its off-diagonal entries,
is deterministically sent to its trace times one Bell projector. -/
theorem productEraseKraus_encoded (c : ℂ) (X : Matrix (u × v) (u × v) ℂ) :
    krausApply (productEraseKraus (d := d) (u := u) (v := v))
      (codeEmbedding (d := d) (u := u) (v := v) c * X * (codeEmbedding (d := d) (u := u) (v := v) c)ᴴ) =
      X.trace • Matrix.vecMulVec (bellVector (d := d) c) (star (bellVector (d := d) c)) := by
  have hb (z : u × v) :
      productEraseKraus (d := d) (u := u) (v := v) z * (codeEmbedding (d := d) (u := u) (v := v) c * X * (codeEmbedding (d := d) (u := u) (v := v) c)ᴴ) *
        (productEraseKraus (d := d) (u := u) (v := v) z)ᴴ =
      X z z • Matrix.vecMulVec (bellVector (d := d) c) (star (bellVector (d := d) c)) := by
    have he :
        productEraseKraus (d := d) (u := u) (v := v) z * (codeEmbedding (d := d) (u := u) (v := v) c * X * (codeEmbedding (d := d) (u := u) (v := v) c)ᴴ) *
          (productEraseKraus (d := d) (u := u) (v := v) z)ᴴ =
        (productEraseKraus (d := d) (u := u) (v := v) z * codeEmbedding (d := d) (u := u) (v := v) c) * X *
          (productEraseKraus (d := d) (u := u) (v := v) z * codeEmbedding (d := d) (u := u) (v := v) c)ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [he]
    exact single_readout_congruence _ _ z
      (fun p q => productEraseKraus_embedding c z q p) X
  simp only [krausApply, hb, Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_smul]

/-- Every actual logical density is extracted exactly, with the same channel. -/
theorem productEraseKraus_encoded_trace_one (c : ℂ)
    (X : Matrix (u × v) (u × v) ℂ) (hX : X.trace = 1) :
    krausApply (productEraseKraus (d := d) (u := u) (v := v))
      (codeEmbedding (d := d) (u := u) (v := v) c * X * (codeEmbedding (d := d) (u := u) (v := v) c)ᴴ) =
      Matrix.vecMulVec (bellVector (d := d) c) (star (bellVector (d := d) c)) := by
  rw [productEraseKraus_encoded, hX, one_smul]

/-- Explicit normalization; no vector length is silently assumed. -/
noncomputable def bellCoeff (d : Type*) [Fintype d] : ℂ :=
  ((1 / Real.sqrt (Fintype.card d : ℝ) : ℝ) : ℂ)

theorem bellCoeff_normalized [Nonempty d] :
    (Fintype.card d : ℂ) * star (bellCoeff d) * bellCoeff d = 1 := by
  have hd : 0 < (Fintype.card d : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs := Real.sq_sqrt hd.le
  have hp := Real.sqrt_pos.mpr hd
  have hr : (Fintype.card d : ℝ) * (1 / Real.sqrt (Fintype.card d : ℝ)) *
      (1 / Real.sqrt (Fintype.card d : ℝ)) = 1 := by
    field_simp
    nlinarith
  simpa [bellCoeff] using congrArg (fun t : ℝ => (t : ℂ)) hr

/-- The coherent Bell encoding is an actual isometry at the explicit normalization. -/
theorem codeEmbedding_isometry [Nonempty d] :
    (codeEmbedding (d := d) (u := u) (v := v) (bellCoeff d))ᴴ *
      codeEmbedding (d := d) (u := u) (v := v) (bellCoeff d) = 1 := by
  ext ⟨j,l⟩ ⟨j',l'⟩
  by_cases hj : j = j' <;> by_cases hl : l = l' <;>
    simp_all [codeEmbedding, bellCode, bellVector, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_prod_type,
      apply_ite, ite_mul, mul_ite, eq_comm, ← mul_assoc]
  exact (bellCoeff_normalized (d := d)).symm

/-- The normalized Bell output is a positive trace-one matrix. -/
theorem bellProjector_density [Nonempty d] :
    (Matrix.vecMulVec (bellVector (d := d) (bellCoeff d)) (star (bellVector (d := d) (bellCoeff d)))).PosSemidef ∧
    (Matrix.vecMulVec (bellVector (d := d) (bellCoeff d)) (star (bellVector (d := d) (bellCoeff d)))).trace = 1 := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  simpa [Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, bellVector,
    Fintype.sum_prod_type, apply_ite, ite_mul, mul_ite, mul_comm, ← mul_assoc] using
    bellCoeff_normalized (d := d)

/-- Actual trace-one PSD logical inputs give actual trace-one PSD encoded inputs. -/
theorem codeEmbedding_density [Nonempty d]
    (X : Matrix (u × v) (u × v) ℂ) (hX : X.PosSemidef ∧ X.trace = 1) :
    (codeEmbedding (d := d) (u := u) (v := v) (bellCoeff d) * X * (codeEmbedding (d := d) (u := u) (v := v) (bellCoeff d))ᴴ).PosSemidef ∧
    (codeEmbedding (d := d) (u := u) (v := v) (bellCoeff d) * X * (codeEmbedding (d := d) (u := u) (v := v) (bellCoeff d))ᴴ).trace = 1 := by
  refine ⟨hX.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_mul_cycle, codeEmbedding_isometry, Matrix.one_mul, hX.2]

end Extraction
