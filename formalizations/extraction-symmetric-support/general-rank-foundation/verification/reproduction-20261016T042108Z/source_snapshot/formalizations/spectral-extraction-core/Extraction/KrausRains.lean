import Extraction.BellOrder
import Extraction.ProjectionBudget

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace Extraction

variable {ι ο κ : Type*} [Fintype ι] [Fintype ο] [Fintype κ]
  [DecidableEq ι] [DecidableEq ο]

@[simp] theorem krausApply_add (A : κ → Matrix ο ι ℂ) (X Y : Matrix ι ι ℂ) :
    krausApply A (X + Y) = krausApply A X + krausApply A Y := by
  simp only [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

@[simp] theorem krausApply_sub (A : κ → Matrix ο ι ℂ) (X Y : Matrix ι ι ℂ) :
    krausApply A (X - Y) = krausApply A X - krausApply A Y := by
  simp only [krausApply, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

@[simp] theorem krausApply_real_smul (A : κ → Matrix ο ι ℂ) (t : ℝ) (X : Matrix ι ι ℂ) :
    krausApply A (t • X) = t • krausApply A X := by
  simp only [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem krausApply_hermitian (A : κ → Matrix ο ι ℂ) (X : Matrix ι ι ℂ)
    (hX : X.IsHermitian) : (krausApply A X).IsHermitian := by
  apply isSelfAdjoint_sum
  intro j _
  change (A j * X * (A j)ᴴ)ᴴ = A j * X * (A j)ᴴ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hX.eq, Matrix.mul_assoc]

/-- Exact Heisenberg--Schrodinger trace duality for the actual finite Kraus map. -/
theorem krausApply_trace_duality (A : κ → Matrix ο ι ℂ)
    (X : Matrix ι ι ℂ) (Y : Matrix ο ο ℂ) :
    (Y * krausApply A X).trace =
      (krausApply (fun j => (A j)ᴴ) Y * X).trace := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.conjTranspose_conjTranspose]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle' Y (A j * X) (A j)ᴴ

/-- Quadratic forms are trace pairings with actual rank-one positive matrices. -/
theorem trace_mul_pure (X : Matrix ι ι ℂ) (w : ι → ℂ) :
    (X * Matrix.vecMulVec w (star w)).trace = star w ⬝ᵥ (X *ᵥ w) := by
  change (∑ i, ∑ j, X i j * (w j * star (w i))) =
    ∑ i, star (w i) * (∑ j, X i j * w j)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {a b d : Type*} [Fintype a] [Fintype b] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq d]

/-- Base-level positivity of the partial-transpose conjugate.
Complete PPT channels satisfy this necessary physical condition; the converse
theorem below deliberately needs only this weaker condition. -/
def PTConjugatePositive
    (A : κ → Matrix (d × d) (a × b) ℂ) : Prop :=
  ∀ X : Matrix (a × b) (a × b) ℂ, X.PosSemidef →
    (APPT.Quantum.partialTranspose (krausApply A (APPT.Quantum.partialTranspose X))).PosSemidef

/-- Transpose-conjugate positivity of the Schrodinger map implies the actual
dual positivity; it is proved by trace pairing, not assumed for effects. -/
theorem dual_pt_positive
    (A : κ → Matrix (d × d) (a × b) ℂ) (hA : PTConjugatePositive A)
    (Y : Matrix (d × d) (d × d) ℂ) (hY : Y.PosSemidef) :
    (APPT.Quantum.partialTranspose
      (krausApply (fun j => (A j)ᴴ) (APPT.Quantum.partialTranspose Y))).PosSemidef := by
  let Z := APPT.Quantum.partialTranspose
    (krausApply (fun j => (A j)ᴴ) (APPT.Quantum.partialTranspose Y))
  have hZ : Z.IsHermitian :=
    APPT.Quantum.partialTranspose_isHermitian
      (krausApply_hermitian _ _ (APPT.Quantum.partialTranspose_isHermitian hY.isHermitian))
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hZ
  intro w
  have hp := Matrix.posSemidef_vecMulVec_self_star w
  have hnon := positive_product_trace_re Y
    (APPT.Quantum.partialTranspose
      (krausApply A (APPT.Quantum.partialTranspose (Matrix.vecMulVec w (star w)))))
    hY (hA _ hp)
  have he : (Z * Matrix.vecMulVec w (star w)).trace =
      (Y * APPT.Quantum.partialTranspose
        (krausApply A (APPT.Quantum.partialTranspose (Matrix.vecMulVec w (star w))))).trace := by
    unfold Z
    rw [← trace_partialTranspose_pairing, ← krausApply_trace_duality,
      ← trace_partialTranspose_pairing]
  rw [← he, trace_mul_pure] at hnon
  exact RCLike.nonneg_iff.mpr ⟨hnon, hZ.im_star_dotProduct_mulVec_self w⟩

/-- The actual channel's target effect. -/
noncomputable def targetEffect (A : κ → Matrix (d × d) (a × b) ℂ) :
    Matrix (a × b) (a × b) ℂ :=
  krausApply (fun j => (A j)ᴴ) (bellProjector (d := d))

/-- Physical, trace-preserving Kraus channels with positive transpose conjugate
satisfy all four Rains effect inequalities. In particular this applies to cPPT. -/
theorem targetEffect_rains [Nonempty d]
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1) (hpt : PTConjugatePositive A) :
    RainsEffect (Fintype.card d) (targetEffect A) := by
  have hJ1 : krausApply (fun j => (A j)ᴴ) 1 = 1 := by
    simpa only [krausApply, Matrix.mul_one, Matrix.conjTranspose_conjTranspose] using hcomplete
  have hphi := bellProjector_density (d := d)
  have hfirst : (targetEffect A).PosSemidef := krausApply_posSemidef _ _ hphi.1
  have hsecond : (1 - targetEffect A).PosSemidef := by
    have h := krausApply_posSemidef (fun j => (A j)ᴴ)
      (1 - bellProjector (d := d)) one_sub_bellProjector_posSemidef
    simpa only [krausApply_sub, hJ1, targetEffect] using h
  obtain ⟨hlo, hhi⟩ := bellProjector_pt_order (d := d)
  have hl := dual_pt_positive A hpt _ hlo
  have hh := dual_pt_positive A hpt _ hhi
  refine ⟨hfirst, hsecond, ?_, ?_⟩
  · simpa only [APPT.Quantum.partialTranspose_add, APPT.Quantum.partialTranspose_smul,
      APPT.Quantum.partialTranspose_one, APPT.Quantum.partialTranspose_involutive,
      krausApply_add, krausApply_real_smul, hJ1, targetEffect] using hl
  · simpa only [APPT.Quantum.partialTranspose_sub, APPT.Quantum.partialTranspose_smul,
      APPT.Quantum.partialTranspose_one, APPT.Quantum.partialTranspose_involutive,
      krausApply_sub, krausApply_real_smul, hJ1, targetEffect] using hh

/-- The physical output overlap equals the actual effect pairing. -/
theorem target_overlap_eq
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (X : Matrix (a × b) (a × b) ℂ) :
    (bellProjector (d := d) * krausApply A X).trace.re =
      (targetEffect A * X).trace.re := by
  rw [krausApply_trace_duality]
  rfl

end Extraction
