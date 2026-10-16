import SpectralProtocol.IntegerBellReal
import SymmetricSupport.ExactEffect
import Mathlib.LinearAlgebra.Matrix.Reindex

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- A fixed input-independent relabelling of the original 2k qubits. Since
preprocessing allows an arbitrary original-space unitary, this permutation
of computational coordinates consumes no supplied memory or extra system. -/
noncomputable def twoQubitCoordinates (k : ℕ) :
    SymmetricSupport.Word 4 k ≃ (Fin (2^k) × Fin (2^k)) :=
  Fintype.equivOfCardEq (by
    simp only [SymmetricSupport.Word, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_prod]
    rw [← mul_pow]
    norm_num)

noncomputable def twoQubitTransport (k : ℕ) :=
  Matrix.reindexAlgEquiv ℂ ℂ (twoQubitCoordinates k)

/-- The physical unknown pure iid input in the existing balanced qubit spaces. -/
noncomputable def pureTwoQubitInput (k : ℕ) (z : Fin 4 → ℂ) :
    Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ :=
  twoQubitTransport k (SymmetricSupport.purePowerDensity 4 k z)

noncomputable def twoQubitSymmetricProjection (k : ℕ) :
    Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ :=
  twoQubitTransport k (SymmetricSupport.symmetricProjector 4 k)

variable {ι η : Type*} [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η]

theorem reindex_trace (e : ι ≃ η) (X : Matrix ι ι ℂ) :
    (Matrix.reindexAlgEquiv ℂ ℂ e X).trace = X.trace := by
  change (∑ i, X (e.symm i) (e.symm i)) = ∑ j, X j j
  exact Equiv.sum_comp e.symm (fun i => X i i)

theorem twoQubitSymmetricProjection_hermitian (k : ℕ) :
    (twoQubitSymmetricProjection k).IsHermitian :=
  (SymmetricSupport.symmetricProjector_hermitian 4 k).reindex (twoQubitCoordinates k)

theorem twoQubitSymmetricProjection_idempotent (k : ℕ) :
    twoQubitSymmetricProjection k * twoQubitSymmetricProjection k =
      twoQubitSymmetricProjection k := by
  exact (map_mul (twoQubitTransport k) _ _).symm.trans
    (congrArg (twoQubitTransport k) (SymmetricSupport.symmetricProjector_idempotent 4 k))

theorem twoQubitSymmetricProjection_rank (k : ℕ) :
    (twoQubitSymmetricProjection k).rank = (k+3).choose 3 := by
  rw [twoQubitSymmetricProjection]
  change (Matrix.reindex (twoQubitCoordinates k) (twoQubitCoordinates k)
    (SymmetricSupport.symmetricProjector 4 k)).rank = _
  rw [Matrix.rank_reindex]
  simpa only [Nat.reduceSub, show k+4-1=k+3 by omega] using
    SymmetricSupport.symmetricProjector_rank_choose_complement 4 k (by decide)

theorem twoQubitSymmetricProjection_rank_pos (k : ℕ) :
    0 < (twoQubitSymmetricProjection k).rank := by
  rw [twoQubitSymmetricProjection_rank]
  exact Nat.choose_pos (by omega)

theorem twoQubitSymmetricProjection_rank_le (k : ℕ) :
    (twoQubitSymmetricProjection k).rank ≤ 4^k := by
  have h := Matrix.rank_le_card_width (twoQubitSymmetricProjection k)
  simpa only [Fintype.card_prod, Fintype.card_fin, ← mul_pow, Nat.reduceMul] using h

theorem pureTwoQubitInput_density (k : ℕ) (z : Fin 4 → ℂ)
    (hz : SymmetricSupport.IsUnitVector z) : APPT.Quantum.IsDensity (pureTwoQubitInput k z) := by
  refine ⟨(SymmetricSupport.purePowerDensity_posSemidef 4 k z).submatrix
    (twoQubitCoordinates k).symm, ?_⟩
  rw [pureTwoQubitInput, twoQubitTransport, reindex_trace]
  exact SymmetricSupport.unitVector_trace 4 k z hz

theorem pureTwoQubitInput_supported (k : ℕ) (z : Fin 4 → ℂ) :
    twoQubitSymmetricProjection k * pureTwoQubitInput k z * twoQubitSymmetricProjection k =
      pureTwoQubitInput k z := by
  unfold twoQubitSymmetricProjection pureTwoQubitInput
  rw [← map_mul, ← map_mul, SymmetricSupport.purePowerDensity_supported]

/-- An actual effect perfect on every normalized unknown pure iid input fixes
the entire computed symmetric support, with no support-spanning hypothesis. -/
theorem exact_pureTwoQubit_effect_fixes_projection (k : ℕ)
    (M : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hM : (1-M).PosSemidef)
    (hfit : ∀ z : Fin 4 → ℂ, SymmetricSupport.IsUnitVector z →
      (M * pureTwoQubitInput k z).trace.re=1) :
    M * twoQubitSymmetricProjection k = twoQubitSymmetricProjection k := by
  let M' := (twoQubitTransport k).symm M
  have hM' : (1-M').PosSemidef := by
    have h := hM.submatrix (twoQubitCoordinates k)
    change (1 - M.submatrix (twoQubitCoordinates k) (twoQubitCoordinates k)).PosSemidef
    simpa only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv] using h
  have hf' (z : Fin 4 → ℂ) (hz : SymmetricSupport.IsUnitVector z) :
      (M' * SymmetricSupport.purePowerDensity 4 k z).trace.re=1 := by
    have heq : (M' * SymmetricSupport.purePowerDensity 4 k z).trace =
        (M * pureTwoQubitInput k z).trace := by
      rw [← reindex_trace (twoQubitCoordinates k)]
      change (twoQubitTransport k (M' * SymmetricSupport.purePowerDensity 4 k z)).trace = _
      rw [map_mul]
      simp only [M', AlgEquiv.apply_symm_apply, pureTwoQubitInput]
    rw [heq]
    exact hfit z hz
  have hfix := SymmetricSupport.exact_unitPurePower_effect_mul_symmetricProjector
    4 k (by decide) M' hM' hf'
  have h := congrArg (twoQubitTransport k) hfix
  simpa only [map_mul, M', AlgEquiv.apply_symm_apply, twoQubitSymmetricProjection] using h


section PhysicalPure
variable {a b d κ : Type*} [Fintype a] [Fintype b] [Fintype d] [Fintype κ]
  [DecidableEq a] [DecidableEq b] [DecidableEq d] [Nonempty d]

/-- Heisenberg effect after the actual original-input unitary. -/
noncomputable def preprocessedEffect
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (U : Matrix.unitaryGroup (a × b) ℂ) : Matrix (a × b) (a × b) ℂ :=
  (U : Matrix (a × b) (a × b) ℂ)ᴴ * Extraction.targetEffect A * U

theorem preprocessedEffect_pairing
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (U : Matrix.unitaryGroup (a × b) ℂ)
    (X : Matrix (a × b) (a × b) ℂ) :
    (Extraction.bellProjector (d := d) * Extraction.krausApply A
      ((U : Matrix (a × b) (a × b) ℂ)*X*(U : Matrix (a × b) (a × b) ℂ)ᴴ)).trace.re =
    (preprocessedEffect A U * X).trace.re := by
  rw [Extraction.target_overlap_eq]
  have h := Matrix.trace_mul_cycle
    (Extraction.targetEffect A * (U : Matrix (a × b) (a × b) ℂ)) X
    (U : Matrix (a × b) (a × b) ℂ)ᴴ
  exact congrArg Complex.re (by simpa only [preprocessedEffect, Matrix.mul_assoc] using h)

theorem one_sub_preprocessedEffect_posSemidef
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (a × b) ℂ) :
    (1-preprocessedEffect A U).PosSemidef := by
  have hU : (U : Matrix (a × b) (a × b) ℂ)ᴴ*U=1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have h := (Extraction.targetEffect_rains A hcomplete hpt).2.1.mul_mul_conjTranspose_same
    (U : Matrix (a × b) (a × b) ℂ)ᴴ
  simpa only [preprocessedEffect, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU] using h

end PhysicalPure

/-- The mathematical exact-achievability part of the paper's pure two-qubit
application, now on actual iid density matrices rather than a supplied support
certificate. This statement does not assert a gate-count or synthesis bound. -/
theorem pure_iid_integerBell_actual_extractor (k : ℕ) :
    let h := integerBellYield k ((k+3).choose 3)
    ∃ (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
      (A : Fin (2^k/2^h) ⊕ Fin (2^k) → Matrix (Fin (2^h)) (Fin (2^k)) ℂ)
      (B : Fin (2^k/2^h) ⊕ Fin (2^k) → Matrix (Fin (2^h)) (Fin (2^k)) ℂ),
      (∑ j,(A j)ᴴ*A j=1) ∧ (∑ j,(B j)ᴴ*B j=1) ∧
      Extraction.PTConjugatePositive (Extraction.productKraus A B) ∧
      ∀ z : Fin 4 → ℂ, SymmetricSupport.IsUnitVector z →
        (Extraction.bellProjector (d := Fin (2^h)) *
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ) *
              pureTwoQubitInput k z *
              (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re=1 := by
  have hall := integerBellYield_actual_extractor k
    (twoQubitSymmetricProjection k) (twoQubitSymmetricProjection_hermitian k)
    (twoQubitSymmetricProjection_idempotent k) (twoQubitSymmetricProjection_rank_le k)
  dsimp only at hall
  rw [twoQubitSymmetricProjection_rank] at hall
  obtain ⟨U,A,B,hA,hB,hpt,he⟩ := hall
  refine ⟨U,A,B,hA,hB,hpt,?_⟩
  intro z hz
  exact he _ (pureTwoQubitInput_density k z hz) (pureTwoQubitInput_supported k z)

/-- Exact optimality on unknown pure iid inputs themselves. The proof internally
establishes that those actual inputs span the computed symmetric support, then
uses the actual physical channel's Rains budget. -/
theorem pure_iid_integerBell_optimal (k h : ℕ) {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin (2^h) × Fin (2^h)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hcomplete : ∑ j,(A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
    (hexact : ∀ z : Fin 4 → ℂ, SymmetricSupport.IsUnitVector z →
      (Extraction.bellProjector (d := Fin (2^h)) * Extraction.krausApply A
        ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ) *
          pureTwoQubitInput k z *
          (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re=1) :
    h ≤ integerBellYield k ((k+3).choose 3) := by
  letI : Nonempty (Fin (2^h)) := ⟨⟨0,by positivity⟩⟩
  let P := twoQubitSymmetricProjection k
  let M := preprocessedEffect A U
  have hfix : M*P=P := exact_pureTwoQubit_effect_fixes_projection k M
    (one_sub_preprocessedEffect_posSemidef A hcomplete hpt U)
    (by intro z hz; rw [← preprocessedEffect_pairing]; exact hexact z hz)
  have hsupport : ∀ X : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ,
      APPT.Quantum.IsDensity X → P*X*P=X →
      (Extraction.bellProjector (d := Fin (2^h)) * Extraction.krausApply A
        ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ) * X *
          (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re=1 := by
    intro X hX hPX
    rw [preprocessedEffect_pairing]
    have hMX : M*X=X := by
      calc
        M*X = M*(P*X*P) := congrArg (fun Y => M*Y) hPX.symm
        _ = (M*P)*X*P := by simp only [Matrix.mul_assoc]
        _ = X := by rw [hfix,hPX]
    change (M*X).trace.re=1
    rw [hMX,hX.2,Complex.one_re]
  have hopt := integerBellYield_optimal k h P
    (twoQubitSymmetricProjection_hermitian k) (twoQubitSymmetricProjection_idempotent k)
    (twoQubitSymmetricProjection_rank_pos k) (twoQubitSymmetricProjection_rank_le k)
    A hcomplete hpt U hsupport
  simpa only [P,twoQubitSymmetricProjection_rank] using hopt
/-- The achieved and optimal natural-number yield equals the exact paper
formula, including every integer rounding boundary. -/
theorem pure_iid_integerBell_eq_paper_floor (k : ℕ) :
    integerBellYield k ((k+3).choose 3) =
      ⌊(k:ℝ) - (1/2:ℝ)*(Real.log (((k+3).choose 3 : ℕ):ℝ)/Real.log 2)⌋₊ := by
  apply integerBellYield_eq_paper_floor
  · exact Nat.choose_pos (by omega)
  · have h := twoQubitSymmetricProjection_rank_le k
    rwa [twoQubitSymmetricProjection_rank] at h

end SpectralProtocol
