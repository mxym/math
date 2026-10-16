import SpectralProtocol.PureBell
import RankSupport.ExactEffect
import RankSupport.RankBounds

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- The actual iid input, using one fixed original-qubit coordinate relabelling. -/
noncomputable def rankBoundedTwoQubitInput (k : ℕ) (X : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ :=
  twoQubitTransport k (ExtractionSpectrum.tensorMatrix X k)

/-- The intrinsic minimal support projector is transported to the physical
balanced input spaces; its actual rank is retained, without a Weyl formula. -/
noncomputable def twoQubitRankBudgetProjection (k s : ℕ) :
    Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ :=
  twoQubitTransport k (ExtractionRankSupport.rankBudgetProjector 4 k s)

noncomputable def twoQubitRankBudgetRank (k s : ℕ) : ℕ :=
  (ExtractionRankSupport.rankBudgetProjector 4 k s).rank

theorem twoQubitRankBudgetProjection_hermitian (k s : ℕ) :
    (twoQubitRankBudgetProjection k s).IsHermitian :=
  (ExtractionRankSupport.rankBudgetProjector_isHermitian 4 k s).reindex (twoQubitCoordinates k)

theorem twoQubitRankBudgetProjection_idempotent (k s : ℕ) :
    twoQubitRankBudgetProjection k s*twoQubitRankBudgetProjection k s=
      twoQubitRankBudgetProjection k s := by
  exact (map_mul (twoQubitTransport k) _ _).symm.trans
    (congrArg (twoQubitTransport k) (ExtractionRankSupport.rankBudgetProjector_idempotent 4 k s))

theorem twoQubitRankBudgetProjection_rank (k s : ℕ) :
    (twoQubitRankBudgetProjection k s).rank=twoQubitRankBudgetRank k s := by
  change (Matrix.reindex (twoQubitCoordinates k) (twoQubitCoordinates k)
    (ExtractionRankSupport.rankBudgetProjector 4 k s)).rank=_
  rw [Matrix.rank_reindex]
  rfl

theorem twoQubitRankBudgetRank_pos (k s : ℕ) (hs : 1 ≤ s) :
    0 < twoQubitRankBudgetRank k s :=
  ExtractionRankSupport.rankBudgetProjector_rank_pos 4 k s (by decide) hs

theorem twoQubitRankBudgetRank_le (k s : ℕ) :
    twoQubitRankBudgetRank k s ≤ 4^k :=
  ExtractionRankSupport.rankBudgetProjector_rank_le_dimension 4 k s

theorem rankBoundedTwoQubitInput_density (k : ℕ) (X : Matrix (Fin 4) (Fin 4) ℂ)
    (hX : (X.PosSemidef ∧ X.trace=1)) : APPT.Quantum.IsDensity (rankBoundedTwoQubitInput k X) := by
  have ht := ExtractionSpectrum.tensorMatrix_density X hX k
  refine ⟨ht.1.submatrix (twoQubitCoordinates k).symm,?_⟩
  rw [rankBoundedTwoQubitInput,twoQubitTransport,reindex_trace]
  exact ht.2

theorem rankBoundedTwoQubitInput_supported (k s : ℕ) (X : Matrix (Fin 4) (Fin 4) ℂ)
    (hX : (X.PosSemidef ∧ X.trace=1)) (hRank : X.rank ≤ s) :
    twoQubitRankBudgetProjection k s*rankBoundedTwoQubitInput k X*twoQubitRankBudgetProjection k s=
      rankBoundedTwoQubitInput k X := by
  unfold twoQubitRankBudgetProjection rankBoundedTwoQubitInput
  rw [← map_mul,← map_mul,ExtractionRankSupport.rankBudgetProjector_tensorMatrix_support
    4 k s X hRank hX.1.isHermitian]

/-- Exact fidelity on the actual rank-constrained iid promise forces identity
on the whole intrinsic support. Density spanning is proved in the dependency. -/
theorem exact_rankBoundedTwoQubit_effect_fixes_projection (k s : ℕ) (hk : 0 < k)
    (M : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hM : (1-M).PosSemidef)
    (hfit : ∀ X : Matrix (Fin 4) (Fin 4) ℂ,(X.PosSemidef ∧ X.trace=1) → X.rank ≤ s →
      (M*rankBoundedTwoQubitInput k X).trace.re=1) :
    M*twoQubitRankBudgetProjection k s=twoQubitRankBudgetProjection k s := by
  let M' := (twoQubitTransport k).symm M
  have hM' : (1-M').PosSemidef := by
    have h := hM.submatrix (twoQubitCoordinates k)
    change (1-M.submatrix (twoQubitCoordinates k) (twoQubitCoordinates k)).PosSemidef
    simpa only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one_equiv] using h
  have hf' (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : (X.PosSemidef ∧ X.trace=1)) (hR : X.rank ≤ s) :
      (M'*ExtractionSpectrum.tensorMatrix X k).trace.re=1 := by
    have heq : (M'*ExtractionSpectrum.tensorMatrix X k).trace=
        (M*rankBoundedTwoQubitInput k X).trace := by
      rw [← reindex_trace (twoQubitCoordinates k)]
      change (twoQubitTransport k (M'*ExtractionSpectrum.tensorMatrix X k)).trace=_
      rw [map_mul]
      simp only [M',AlgEquiv.apply_symm_apply,rankBoundedTwoQubitInput]
    rw [heq]
    exact hfit X hX hR
  have hfix := ExtractionRankSupport.exact_rankBounded_iid_effect_mul_rankBudgetProjector
    4 k s hk M' hM' hf'
  have h := congrArg (twoQubitTransport k) hfix
  simpa only [map_mul,M',AlgEquiv.apply_symm_apply,twoQubitRankBudgetProjection] using h

/-- Exact achievability simultaneously for every actual density of rank at
most s. Only one original-space unitary and complete local channels are used. -/
theorem rankBounded_iid_integerBell_actual_extractor (k s : ℕ) :
    let h := integerBellYield k (twoQubitRankBudgetRank k s)
    ∃ (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
      (A : Fin (2^k/2^h) ⊕ Fin (2^k) → Matrix (Fin (2^h)) (Fin (2^k)) ℂ)
      (B : Fin (2^k/2^h) ⊕ Fin (2^k) → Matrix (Fin (2^h)) (Fin (2^k)) ℂ),
      (∑ j,(A j)ᴴ*A j=1) ∧ (∑ j,(B j)ᴴ*B j=1) ∧
      Extraction.PTConjugatePositive (Extraction.productKraus A B) ∧
      ∀ X : Matrix (Fin 4) (Fin 4) ℂ,(X.PosSemidef ∧ X.trace=1) → X.rank ≤ s →
        (Extraction.bellProjector (d := Fin (2^h))*
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)*
              rankBoundedTwoQubitInput k X*
              (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re=1 := by
  have hr : (twoQubitRankBudgetProjection k s).rank ≤ 4^k := by
    rw [twoQubitRankBudgetProjection_rank]
    exact twoQubitRankBudgetRank_le k s
  have hall := integerBellYield_actual_extractor k
    (twoQubitRankBudgetProjection k s) (twoQubitRankBudgetProjection_hermitian k s)
    (twoQubitRankBudgetProjection_idempotent k s) hr
  dsimp only at hall
  rw [twoQubitRankBudgetProjection_rank] at hall
  obtain ⟨U,A,B,hA,hB,hpt,he⟩ := hall
  refine ⟨U,A,B,hA,hB,hpt,?_⟩
  intro X hX hR
  exact he _ (rankBoundedTwoQubitInput_density k X hX)
    (rankBoundedTwoQubitInput_supported k s X hX hR)

/-- Every actual finite PPT Kraus protocol perfect on the entire rank-s iid
promise obeys the matching integer Bell bound. The support rank is intrinsic. -/
theorem rankBounded_iid_integerBell_optimal (k s h : ℕ) (hk : 0 < k) (hs : 1 ≤ s)
    {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin (2^h) × Fin (2^h)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hcomplete : ∑ j,(A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
    (hexact : ∀ X : Matrix (Fin 4) (Fin 4) ℂ,(X.PosSemidef ∧ X.trace=1) → X.rank ≤ s →
      (Extraction.bellProjector (d := Fin (2^h))*Extraction.krausApply A
        ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)*
          rankBoundedTwoQubitInput k X*
          (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re=1) :
    h ≤ integerBellYield k (twoQubitRankBudgetRank k s) := by
  letI : Nonempty (Fin (2^h)) := ⟨⟨0,by positivity⟩⟩
  let P := twoQubitRankBudgetProjection k s
  let M := preprocessedEffect A U
  have hfix : M*P=P := exact_rankBoundedTwoQubit_effect_fixes_projection k s hk M
    (one_sub_preprocessedEffect_posSemidef A hcomplete hpt U)
    (by intro X hX hR;rw [← preprocessedEffect_pairing];exact hexact X hX hR)
  have hsupport : ∀ Y : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ,
      APPT.Quantum.IsDensity Y → P*Y*P=Y →
      (Extraction.bellProjector (d := Fin (2^h))*Extraction.krausApply A
        ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)*Y*
          (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re=1 := by
    intro Y hY hPY
    rw [preprocessedEffect_pairing]
    have hMY : M*Y=Y := by
      calc
        M*Y=M*(P*Y*P) := congrArg (fun Z => M*Z) hPY.symm
        _=(M*P)*Y*P := by simp only [Matrix.mul_assoc]
        _=Y := by rw [hfix,hPY]
    change (M*Y).trace.re=1
    rw [hMY,hY.2,Complex.one_re]
  have hpos : 0 < P.rank := by
    rw [show P=twoQubitRankBudgetProjection k s from rfl,twoQubitRankBudgetProjection_rank]
    exact twoQubitRankBudgetRank_pos k s hs
  have hle : P.rank ≤ 4^k := by
    rw [show P=twoQubitRankBudgetProjection k s from rfl,twoQubitRankBudgetProjection_rank]
    exact twoQubitRankBudgetRank_le k s
  have hopt := integerBellYield_optimal k h P (twoQubitRankBudgetProjection_hermitian k s)
    (twoQubitRankBudgetProjection_idempotent k s) hpos hle A hcomplete hpt U hsupport
  simpa only [P,twoQubitRankBudgetProjection_rank] using hopt

theorem rankBounded_iid_integerBell_eq_paper_floor (k s : ℕ) (hs : 1 ≤ s) :
    integerBellYield k (twoQubitRankBudgetRank k s)=
      ⌊(k:ℝ)-(1/2:ℝ)*(Real.log (twoQubitRankBudgetRank k s:ℝ)/Real.log 2)⌋₊ :=
  integerBellYield_eq_paper_floor k _ (twoQubitRankBudgetRank_pos k s hs)
    (twoQubitRankBudgetRank_le k s)


/-- The intrinsic rank-s result recovers the previously counted pure support. -/
theorem twoQubitRankBudgetRank_one (k : ℕ) :
    twoQubitRankBudgetRank k 1=(k+3).choose 3 := by
  unfold twoQubitRankBudgetRank
  rw [ExtractionRankSupport.rankBudgetProjector_one_eq_symmetricProjector]
  simpa only [Nat.reduceSub,show k+4-1=k+3 by omega] using
    SymmetricSupport.symmetricProjector_rank_choose_complement 4 k (by decide)

theorem twoQubitRankBudgetProjection_one (k : ℕ) :
    twoQubitRankBudgetProjection k 1=twoQubitSymmetricProjection k := by
  unfold twoQubitRankBudgetProjection twoQubitSymmetricProjection
  rw [ExtractionRankSupport.rankBudgetProjector_one_eq_symmetricProjector]

theorem twoQubitRankBudgetRank_full (k s : ℕ) (hs : 4 ≤ s) :
    twoQubitRankBudgetRank k s=4^k :=
  ExtractionRankSupport.rankBudgetProjector_rank_eq_dimension 4 k s hs

/-- With no effective one-copy rank restriction the guaranteed exact yield is zero. -/
theorem rankBounded_iid_integerBell_fullrank_zero (k s : ℕ) (hs : 4 ≤ s) :
    integerBellYield k (twoQubitRankBudgetRank k s)=0 := by
  rw [twoQubitRankBudgetRank_full k s hs,integerBellYield,Nat.clog_pow 4 k (by decide),Nat.sub_self]

end SpectralProtocol