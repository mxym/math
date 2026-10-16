import SpectralProtocol.IntegerBellLimit
import RankSupport.FixedSpectrumOrbit
import RankSupport.FlatWitness

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

theorem density_rank_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) (htrace : X.trace=1) : 0 < X.rank := by
  by_contra! h
  have hdim : Module.finrank ℂ (LinearMap.range X.mulVecLin)=0 := Nat.eq_zero_of_le_zero h
  have hlin : X.mulVecLin=0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hdim)
  have hzero : X=0 := by
    ext i j
    change X i j=0
    have hj := congrArg (fun f : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) => f (Pi.single j 1) i) hlin
    simpa only [Matrix.mulVecLin_apply,LinearMap.zero_apply,Pi.zero_apply,
      Matrix.mulVec_single,MulOpposite.op_one,one_smul,Matrix.col,Matrix.transpose_apply] using hj
  have ht : (0:ℂ)=1 := by simpa only [hzero,Matrix.trace_zero] using htrace
  exact zero_ne_one ht

/-- The actual finite unitary orbit of a fixed density already forces the full
intrinsic rank support. No flatness, Haar law, or supplied spanning premise. -/
theorem exact_fixedTwoQubitOrbit_effect_fixes_projection (k : ℕ)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (M : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hM : (1-M).PosSemidef)
    (hfit : ∀ V : Matrix.unitaryGroup (Fin 4) ℂ,
      (M*rankBoundedTwoQubitInput k
        ((V : Matrix (Fin 4) (Fin 4) ℂ)*X*(V : Matrix (Fin 4) (Fin 4) ℂ)ᴴ)).trace.re=1) :
    M*twoQubitRankBudgetProjection k X.rank=twoQubitRankBudgetProjection k X.rank := by
  let M' := (twoQubitTransport k).symm M
  have hM' : (1-M').PosSemidef := by
    have h := hM.submatrix (twoQubitCoordinates k)
    change (1-M.submatrix (twoQubitCoordinates k) (twoQubitCoordinates k)).PosSemidef
    simpa only [Matrix.submatrix_sub,Pi.sub_apply,Matrix.submatrix_one_equiv] using h
  have hf' (V : Matrix.unitaryGroup (Fin 4) ℂ) :
      (M'*ExtractionSpectrum.tensorMatrix
        ((V : Matrix (Fin 4) (Fin 4) ℂ)*X*(V : Matrix (Fin 4) (Fin 4) ℂ)ᴴ) k).trace.re=1 := by
    have heq : (M'*ExtractionSpectrum.tensorMatrix
        ((V : Matrix (Fin 4) (Fin 4) ℂ)*X*(V : Matrix (Fin 4) (Fin 4) ℂ)ᴴ) k).trace=
        (M*rankBoundedTwoQubitInput k
          ((V : Matrix (Fin 4) (Fin 4) ℂ)*X*(V : Matrix (Fin 4) (Fin 4) ℂ)ᴴ)).trace := by
      rw [← reindex_trace (twoQubitCoordinates k)]
      change (twoQubitTransport k (M'*ExtractionSpectrum.tensorMatrix _ k)).trace=_
      rw [map_mul]
      simp only [M',AlgEquiv.apply_symm_apply,rankBoundedTwoQubitInput]
    rw [heq]
    exact hfit V
  have hfix := ExtractionRankSupport.exact_fixed_density_orbit_effect_mul_rankBudgetProjector
    4 k X hX M' hM' hf'
  have h := congrArg (twoQubitTransport k) hfix
  simpa only [map_mul,M',AlgEquiv.apply_symm_apply,twoQubitRankBudgetProjection] using h

theorem integerBellYield_optimal_of_effect_fixes_projection (k h : ℕ)
    (P : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) (hpos : 0 < P.rank) (hle : P.rank ≤ 4^k)
    {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin (2^h) × Fin (2^h)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hcomplete : ∑ j,(A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
    (hfix : preprocessedEffect A U*P=P) : h ≤ integerBellYield k P.rank := by
  apply integerBellYield_optimal k h P hP hPP hpos hle A hcomplete hpt U
  intro Y hY hPY
  rw [preprocessedEffect_pairing]
  have hMY : preprocessedEffect A U*Y=Y := by
    calc
      _=preprocessedEffect A U*(P*Y*P) := congrArg (fun Z => preprocessedEffect A U*Z) hPY.symm
      _=(preprocessedEffect A U*P)*Y*P := by simp only [Matrix.mul_assoc]
      _=Y := by rw [hfix,hPY]
  rw [hMY,hY.2,Complex.one_re]

/-- Every fixed nonflat spectrum has the same exact integer optimum as the
whole rank class. The proof covers all blocklengths, including zero. -/
theorem fixedSpectrum_iid_integerBell_optimal (k h : ℕ)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin (2^h) × Fin (2^h)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hcomplete : ∑ j,(A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
    (hexact : ∀ V : Matrix.unitaryGroup (Fin 4) ℂ,
      (Extraction.bellProjector (d := Fin (2^h))*Extraction.krausApply A
        ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)*
          rankBoundedTwoQubitInput k
            ((V : Matrix (Fin 4) (Fin 4) ℂ)*X*(V : Matrix (Fin 4) (Fin 4) ℂ)ᴴ)*
          (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re=1) :
    h ≤ integerBellYield k (twoQubitRankBudgetRank k X.rank) := by
  letI : Nonempty (Fin (2^h)) := ⟨⟨0,by positivity⟩⟩
  let P := twoQubitRankBudgetProjection k X.rank
  have hfix := exact_fixedTwoQubitOrbit_effect_fixes_projection k X hX (preprocessedEffect A U)
    (one_sub_preprocessedEffect_posSemidef A hcomplete hpt U)
    (by intro V;rw [← preprocessedEffect_pairing];exact hexact V)
  have hpos : 0 < P.rank := by
    rw [show P=twoQubitRankBudgetProjection k X.rank from rfl,twoQubitRankBudgetProjection_rank]
    exact twoQubitRankBudgetRank_pos k X.rank (density_rank_pos X hX.2)
  have hle : P.rank ≤ 4^k := by
    rw [show P=twoQubitRankBudgetProjection k X.rank from rfl,twoQubitRankBudgetProjection_rank]
    exact twoQubitRankBudgetRank_le k X.rank
  have hopt := integerBellYield_optimal_of_effect_fixes_projection k h P
    (twoQubitRankBudgetProjection_hermitian k X.rank)
    (twoQubitRankBudgetProjection_idempotent k X.rank) hpos hle A hcomplete hpt U hfix
  simpa only [P,twoQubitRankBudgetProjection_rank] using hopt

/-- One complete actual local protocol is exact on the full unknown-basis
orbit of any given density, with no auxiliary input system. -/
theorem fixedSpectrum_iid_integerBell_actual_extractor (k : ℕ)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    let h := integerBellYield k (twoQubitRankBudgetRank k X.rank)
    ∃ (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
      (A : Fin (2^k/2^h) ⊕ Fin (2^k) → Matrix (Fin (2^h)) (Fin (2^k)) ℂ)
      (B : Fin (2^k/2^h) ⊕ Fin (2^k) → Matrix (Fin (2^h)) (Fin (2^k)) ℂ),
      (∑ j,(A j)ᴴ*A j=1) ∧ (∑ j,(B j)ᴴ*B j=1) ∧
      Extraction.PTConjugatePositive (Extraction.productKraus A B) ∧
      ∀ V : Matrix.unitaryGroup (Fin 4) ℂ,
        (Extraction.bellProjector (d := Fin (2^h))*
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)*
              rankBoundedTwoQubitInput k
                ((V : Matrix (Fin 4) (Fin 4) ℂ)*X*(V : Matrix (Fin 4) (Fin 4) ℂ)ᴴ)*
              (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re=1 := by
  obtain ⟨U,A,B,hA,hB,hpt,he⟩ := rankBounded_iid_integerBell_actual_extractor k X.rank
  refine ⟨U,A,B,hA,hB,hpt,?_⟩
  intro V
  apply he
  · exact ExtractionRankSupport.fixed_density_unitary_conjugate_density 4 X hX V
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem fixedSpectrum_iid_integerBell_per_copy_limit
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    Filter.Tendsto (fun k : ℕ => (integerBellYield k (twoQubitRankBudgetRank k X.rank):ℝ)/(k:ℝ))
      Filter.atTop (nhds (1-Real.log (X.rank:ℝ)/Real.log 4)) :=
  rankBounded_iid_integerBell_per_copy_limit X.rank (density_rank_pos X hX.2)
    (by simpa only [Fintype.card_fin] using Matrix.rank_le_card_width X)

theorem twoQubitRankBudgetRank_min_four (k s : ℕ) :
    twoQubitRankBudgetRank k (min s 4)=twoQubitRankBudgetRank k s := by
  by_cases hs : s ≤ 4
  · rw [min_eq_left hs]
  · have h4 : 4 ≤ s := by omega
    rw [min_eq_right h4,twoQubitRankBudgetRank_full k 4 (le_refl 4),
      twoQubitRankBudgetRank_full k s h4]

/-- This strengthens the class converse to include blocklength zero. The
full-rank case and zero-blocklength boundary are handled explicitly. -/
theorem rankBounded_iid_integerBell_optimal_all_blocklength (k s h : ℕ) (hs : 1 ≤ s)
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
  obtain ⟨X,hX,hR,_⟩ := ExtractionRankSupport.exists_flat_rank_density
    4 (min s 4) (by omega) (min_le_right s 4)
  have hopt := fixedSpectrum_iid_integerBell_optimal k h X hX A hcomplete hpt U (by
    intro V
    apply hexact
    · exact ExtractionRankSupport.fixed_density_unitary_conjugate_density 4 X hX V
    · calc
        _ ≤ X.rank := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
        _ = min s 4 := hR
        _ ≤ s := min_le_left s 4)
  rwa [hR,twoQubitRankBudgetRank_min_four] at hopt


/-- The fixed arbitrary spectrum's exact optimum has the same integer-boundary
formula, with its intrinsic common-support rank derived from the input rank. -/
theorem fixedSpectrum_iid_integerBell_eq_paper_floor (k : ℕ)
    (X : Matrix (Fin 4) (Fin 4) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    integerBellYield k (twoQubitRankBudgetRank k X.rank)=
      ⌊(k:ℝ)-(1/2:ℝ)*(Real.log (twoQubitRankBudgetRank k X.rank:ℝ)/Real.log 2)⌋₊ :=
  rankBounded_iid_integerBell_eq_paper_floor k X.rank (density_rank_pos X hX.2)

end SpectralProtocol