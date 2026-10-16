import SpectralProtocol.PureGuarantee
import LocalCap.ActualCap

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- A fixed permutation of the original computational coordinates, valid for
all local dimensions and chosen independently of every unknown input. -/
noncomputable def bipartitePowerCoordinates (m n k : ℕ) :
    SymmetricSupport.Word (m*n) k ≃ (Fin (m^k) × Fin (n^k)) :=
  Fintype.equivOfCardEq (by
    simp only [SymmetricSupport.Word,Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,mul_pow])

noncomputable def bipartitePowerTransport (m n k : ℕ) :=
  Matrix.reindexAlgEquiv ℂ ℂ (bipartitePowerCoordinates m n k)

noncomputable def purePowerInput (m n k : ℕ) (z : Fin (m*n) → ℂ) :
    Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ :=
  bipartitePowerTransport m n k (SymmetricSupport.purePowerDensity (m*n) k z)

noncomputable def purePowerProjection (m n k : ℕ) :
    Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ :=
  bipartitePowerTransport m n k (SymmetricSupport.symmetricProjector (m*n) k)

noncomputable def purePowerAverage (m n k : ℕ) :
    Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ :=
  bipartitePowerTransport m n k (SymmetricSupport.symmetricState (m*n) k)

def pureSupportRank (m n k : ℕ) : ℕ := (k+m*n-1).choose (m*n-1)

theorem purePowerProjection_hermitian (m n k : ℕ) : (purePowerProjection m n k).IsHermitian :=
  (SymmetricSupport.symmetricProjector_hermitian (m*n) k).reindex (bipartitePowerCoordinates m n k)

theorem purePowerProjection_idempotent (m n k : ℕ) :
    purePowerProjection m n k*purePowerProjection m n k=purePowerProjection m n k := by
  exact (map_mul (bipartitePowerTransport m n k) _ _).symm.trans
    (congrArg (bipartitePowerTransport m n k)
      (SymmetricSupport.symmetricProjector_idempotent (m*n) k))

theorem purePowerProjection_rank (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (purePowerProjection m n k).rank=pureSupportRank m n k := by
  change (Matrix.reindex (bipartitePowerCoordinates m n k) (bipartitePowerCoordinates m n k)
    (SymmetricSupport.symmetricProjector (m*n) k)).rank=_
  rw [Matrix.rank_reindex]
  exact SymmetricSupport.symmetricProjector_rank_choose_complement (m*n) k (Nat.mul_pos hm hn)

theorem pureSupportRank_pos (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) :
    0 < pureSupportRank m n k := by
  apply Nat.choose_pos
  have hmn := Nat.mul_pos hm hn
  omega

theorem pureSupportRank_le_dimension (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) :
    pureSupportRank m n k ≤ (m*n)^k := by
  rw [← purePowerProjection_rank m n k hm hn]
  have h := Matrix.rank_le_card_width (purePowerProjection m n k)
  simpa only [Fintype.card_prod,Fintype.card_fin,mul_pow] using h

theorem purePowerInput_density (m n k : ℕ) (z : Fin (m*n) → ℂ)
    (hz : SymmetricSupport.IsUnitVector z) : APPT.Quantum.IsDensity (purePowerInput m n k z) := by
  refine ⟨(SymmetricSupport.purePowerDensity_posSemidef (m*n) k z).submatrix
    (bipartitePowerCoordinates m n k).symm,?_⟩
  rw [purePowerInput,bipartitePowerTransport,reindex_trace]
  exact SymmetricSupport.unitVector_trace (m*n) k z hz

theorem purePowerInput_supported (m n k : ℕ) (z : Fin (m*n) → ℂ) :
    purePowerProjection m n k*purePowerInput m n k z*purePowerProjection m n k=
      purePowerInput m n k z := by
  unfold purePowerProjection purePowerInput
  rw [← map_mul,← map_mul,SymmetricSupport.purePowerDensity_supported]

theorem purePowerAverage_density (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) :
    APPT.Quantum.IsDensity (purePowerAverage m n k) := by
  refine ⟨(SymmetricSupport.symmetricState_posSemidef (m*n) k).submatrix
    (bipartitePowerCoordinates m n k).symm,?_⟩
  rw [purePowerAverage,bipartitePowerTransport,reindex_trace]
  exact SymmetricSupport.symmetricState_trace (m*n) k (Nat.mul_pos hm hn)

theorem purePowerAverage_purity (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (purePowerAverage m n k*purePowerAverage m n k).trace.re =
      (pureSupportRank m n k:ℝ)⁻¹ := by
  unfold purePowerAverage
  rw [← map_mul]
  change (Matrix.reindexAlgEquiv ℂ ℂ (bipartitePowerCoordinates m n k)
    (SymmetricSupport.symmetricState (m*n) k*SymmetricSupport.symmetricState (m*n) k)).trace.re=_
  rw [reindex_trace,SymmetricSupport.symmetricState_purity]
  have hcard : Fintype.card (Sym (Fin (m*n)) k)=pureSupportRank m n k := by
    have ht := projection_trace_eq_rank (SymmetricSupport.symmetricProjector (m*n) k)
      (SymmetricSupport.symmetricProjector_hermitian (m*n) k)
      (SymmetricSupport.symmetricProjector_idempotent (m*n) k)
    rw [SymmetricSupport.symmetricProjector_trace,
      SymmetricSupport.symmetricProjector_rank_choose_complement (m*n) k (Nat.mul_pos hm hn)] at ht
    exact_mod_cast ht
  rw [hcard]
  change ((↑((pureSupportRank m n k:ℝ)) : ℂ)⁻¹).re=_
  rw [← Complex.ofReal_inv,Complex.ofReal_re]

/-- The actual continuum of normalized pure iid inputs reduces to the actual
symmetric-state matrix, through a proved integral rather than a Haar premise. -/
theorem purePower_guarantee_le_average (m n k : ℕ) (hm : 0 < m) (hn : 0 < n)
    (M : Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ) (f : ℝ)
    (hf : ∀ z : Fin (m*n) → ℂ, SymmetricSupport.IsUnitVector z →
      f ≤ (M*purePowerInput m n k z).trace.re) :
    f ≤ (M*purePowerAverage m n k).trace.re := by
  let M' := (bipartitePowerTransport m n k).symm M
  have htrace (Y : Matrix (SymmetricSupport.Word (m*n) k) (SymmetricSupport.Word (m*n) k) ℂ) :
      (M'*Y).trace=(M*bipartitePowerTransport m n k Y).trace := by
    rw [← reindex_trace (bipartitePowerCoordinates m n k)]
    change (bipartitePowerTransport m n k (M'*Y)).trace=_
    rw [map_mul]
    simp only [M',AlgEquiv.apply_symm_apply]
  have h := SymmetricSupport.pure_guarantee_le_symmetricState (m*n) k (Nat.mul_pos hm hn) M' f (by
    intro z hz
    rw [htrace]
    exact hf z hz)
  simpa only [htrace,purePowerAverage] using h

/-- Full finite upper envelope for the actual unknown pure iid promise, all
original-space unitaries, and every physical finite PPT Kraus channel. -/
theorem purePower_fidelity_guarantee_upper (m n k K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hK : 0 < K) {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin K × Fin K) (Fin (m^k) × Fin (n^k)) ℂ)
    (hcomplete : ∑ j,(A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin (m^k) × Fin (n^k)) ℂ) (f : ℝ)
    (hf : ∀ z : Fin (m*n) → ℂ, SymmetricSupport.IsUnitVector z →
      f ≤ (Extraction.bellProjector (d := Fin K)*Extraction.krausApply A
        ((U : Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ)*
          purePowerInput m n k z*
          (U : Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ)ᴴ)).trace.re) :
    f ≤ min 1 (min ((m:ℝ)^k/K)
      (Real.sqrt (((m*n:ℕ):ℝ)^k / ((K:ℝ)^2*(pureSupportRank m n k:ℝ))))) := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  have havg := purePower_guarantee_le_average m n k hm hn (preprocessedEffect A U) f (by
    intro z hz
    rw [← preprocessedEffect_pairing]
    exact hf z hz)
  rw [← preprocessedEffect_pairing] at havg
  have hdensity := purePowerAverage_density m n k hm hn
  have hbound := ExtractionLocalCap.kraus_target_overlap_full_envelope A hcomplete hpt
    (purePowerAverage m n k) hdensity U
  rw [purePowerAverage_purity m n k hm hn] at hbound
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at hbound
  have heq : (pureSupportRank m n k:ℝ)⁻¹*((m:ℝ)^k*(n:ℝ)^k/(K:ℝ)^2) =
      (((m*n:ℕ):ℝ)^k/((K:ℝ)^2*(pureSupportRank m n k:ℝ))) := by
    push_cast
    rw [mul_pow]
    ring
  rw [heq] at hbound
  exact havg.trans hbound

/-- An actual fixed LO protocol simultaneously attains the feasible Bell rank
on all unknown pure iid inputs, in arbitrary finite local dimensions. -/
theorem purePower_fidelity_feasible_lower (m n k d K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hd : 0 < d) (hdk : d ≤ K)
    (hrank : pureSupportRank m n k ≤ (m^k/d)*(n^k/d)) :
    ∃ (U : Matrix.unitaryGroup (Fin (m^k) × Fin (n^k)) ℂ)
      (A : Fin (m^k/d) ⊕ Fin (m^k) → Matrix (Fin K) (Fin (m^k)) ℂ)
      (B : Fin (n^k/d) ⊕ Fin (n^k) → Matrix (Fin K) (Fin (n^k)) ℂ),
      (∑ j,(A j)ᴴ*A j=1) ∧ (∑ j,(B j)ᴴ*B j=1) ∧
      Extraction.PTConjugatePositive (Extraction.productKraus A B) ∧
      ∀ z : Fin (m*n) → ℂ, SymmetricSupport.IsUnitVector z →
        (Extraction.bellProjector (d := Fin K)*
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ)*
              purePowerInput m n k z*
              (U : Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ)ᴴ)).trace.re=(d:ℝ)/K := by
  obtain ⟨U,A,B,hA,hB,he⟩ := Extraction.finite_projection_fidelity_extractor
    (m^k) (n^k) d K hd hdk (purePowerProjection m n k)
    (purePowerProjection_hermitian m n k) (purePowerProjection_idempotent m n k)
    (by rwa [purePowerProjection_rank m n k hm hn])
  refine ⟨U,A,B,hA,hB,productKraus_PTConjugatePositive A B,?_⟩
  intro z hz
  exact he _ (purePowerInput_density m n k z hz) (purePowerInput_supported m n k z)

end SpectralProtocol