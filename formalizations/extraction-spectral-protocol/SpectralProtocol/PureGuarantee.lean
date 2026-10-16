import SpectralProtocol.PureBell
import SymmetricSupport.PureAverageBound

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

noncomputable def pureTwoQubitAverage (k : ℕ) :
    Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ :=
  twoQubitTransport k (SymmetricSupport.symmetricState 4 k)

theorem pureTwoQubitAverage_density (k : ℕ) : APPT.Quantum.IsDensity (pureTwoQubitAverage k) := by
  refine ⟨(SymmetricSupport.symmetricState_posSemidef 4 k).submatrix
    (twoQubitCoordinates k).symm,?_⟩
  rw [pureTwoQubitAverage,twoQubitTransport,reindex_trace]
  exact SymmetricSupport.symmetricState_trace 4 k (by decide)

theorem pureTwoQubitAverage_purity (k : ℕ) :
    (pureTwoQubitAverage k*pureTwoQubitAverage k).trace.re =
      (((k+3).choose 3 : ℕ):ℝ)⁻¹ := by
  unfold pureTwoQubitAverage
  rw [← map_mul]
  change (Matrix.reindexAlgEquiv ℂ ℂ (twoQubitCoordinates k)
    (SymmetricSupport.symmetricState 4 k*SymmetricSupport.symmetricState 4 k)).trace.re=_
  rw [reindex_trace,SymmetricSupport.symmetricState_purity]
  have hcard : Fintype.card (Sym (Fin 4) k) = (k+3).choose 3 := by
    have ht := projection_trace_eq_rank (SymmetricSupport.symmetricProjector 4 k)
      (SymmetricSupport.symmetricProjector_hermitian 4 k)
      (SymmetricSupport.symmetricProjector_idempotent 4 k)
    rw [SymmetricSupport.symmetricProjector_trace,
      SymmetricSupport.symmetricProjector_rank_choose_complement 4 k (by decide)] at ht
    norm_num only [Nat.reduceSub] at ht
    have hidx : k+4-1=k+3 := by omega
    rw [hidx] at ht
    exact_mod_cast ht
  rw [hcard]
  change ((↑((((k+3).choose 3 : ℕ):ℝ)) : ℂ)⁻¹).re = _
  rw [← Complex.ofReal_inv,Complex.ofReal_re]

/-- A guarantee for all normalized actual unknown iid pure inputs is bounded
by one actual symmetric-state expectation. The ensemble reduction is fully
proved by the dependency's finite-phase and positive radial integral, rather
than supplied as a Haar/design premise. -/
theorem pureTwoQubit_guarantee_le_average (k : ℕ)
    (M : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ) (f : ℝ)
    (hf : ∀ z : Fin 4 → ℂ, SymmetricSupport.IsUnitVector z →
      f ≤ (M*pureTwoQubitInput k z).trace.re) :
    f ≤ (M*pureTwoQubitAverage k).trace.re := by
  let M' := (twoQubitTransport k).symm M
  have htrace (Y : Matrix (SymmetricSupport.Word 4 k) (SymmetricSupport.Word 4 k) ℂ) :
      (M'*Y).trace=(M*twoQubitTransport k Y).trace := by
    rw [← reindex_trace (twoQubitCoordinates k)]
    change (twoQubitTransport k (M'*Y)).trace=_
    rw [map_mul]
    simp only [M',AlgEquiv.apply_symm_apply]
  have h := SymmetricSupport.pure_guarantee_le_symmetricState 4 k (by decide) M' f (by
    intro z hz
    rw [htrace]
    exact hf z hz)
  simpa only [htrace,pureTwoQubitAverage] using h

/-- Every physical PPT-Kraus protocol and every original-space unitary has a
worst-pure-input fidelity bounded by the explicit unit/purity envelope at
all finite blocklengths and every integer target K. -/
theorem pure_iid_fidelity_guarantee_upper (k K : ℕ) (hK : 0 < K)
    {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin K × Fin K) (Fin (2^k) × Fin (2^k)) ℂ)
    (hcomplete : ∑ j,(A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ) (f : ℝ)
    (hf : ∀ z : Fin 4 → ℂ, SymmetricSupport.IsUnitVector z →
      f ≤ (Extraction.bellProjector (d := Fin K)*Extraction.krausApply A
        ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)*
          pureTwoQubitInput k z*
          (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re) :
    f ≤ min 1 (Real.sqrt ((4:ℝ)^k /
      ((K:ℝ)^2*(((k+3).choose 3 : ℕ):ℝ)))) := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  have havg := pureTwoQubit_guarantee_le_average k (preprocessedEffect A U) f (by
    intro z hz
    rw [← preprocessedEffect_pairing]
    exact hf z hz)
  rw [← preprocessedEffect_pairing] at havg
  have hdensity := pureTwoQubitAverage_density k
  have hU : (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ*U=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hstate : APPT.Quantum.IsDensity
      ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)*
        pureTwoQubitAverage k*(U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ) :=
    ⟨hdensity.1.mul_mul_conjTranspose_same _,
      (Extraction.isometry_trace_congruence _ hU _).trans hdensity.2⟩
  have hunit := Extraction.kraus_target_overlap_le_one A hcomplete hpt _ hstate
  have hpur := Extraction.kraus_target_overlap_unitary_le A hcomplete hpt _ hdensity.1.isHermitian U
  rw [pureTwoQubitAverage_purity] at hpur
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at hpur
  have hsq : (2:ℝ)^k*(2:ℝ)^k=(4:ℝ)^k := by rw [← mul_pow]; norm_num
  rw [hsq] at hpur
  have heq : (((k+3).choose 3 : ℕ):ℝ)⁻¹ * ((4:ℝ)^k/(K:ℝ)^2) =
      (4:ℝ)^k/((K:ℝ)^2*(((k+3).choose 3 : ℕ):ℝ)) := by ring
  rw [heq] at hpur
  exact le_min (havg.trans hunit) (havg.trans hpur)

end SpectralProtocol