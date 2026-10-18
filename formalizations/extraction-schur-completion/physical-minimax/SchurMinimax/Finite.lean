import SchurCompletion.GeneralRank
import MinimaxProfile.UniversalFinite
import MinimaxProfile.Minimax
import MinimaxProfile.PackingLimit

open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

def RankBudgetInput (D s : ℕ) :=
  {X : Matrix (Fin D) (Fin D) ℂ // X.PosSemidef ∧ X.trace=1 ∧ X.rank ≤ s}

def rankBudgetMinimax (m n k s K : ℕ) : ℝ :=
  minimaxValue (fun X : RankBudgetInput (m*n) s => tensorInput m n k X.val) K

def rankBudgetProjection (m n k s : ℕ) :
    Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ :=
  SpectralProtocol.bipartitePowerTransport m n k (rankBudgetProjector (m*n) k s)

def rankBudgetClassMinimax (m n k s K : ℕ)
    (C : KrausPPTProtocol (m^k) (n^k) K → Prop) : ℝ :=
  sSup {c : ℝ | ∃ V : KrausPPTProtocol (m^k) (n^k) K,
    C V ∧ ∀ X : RankBudgetInput (m*n) s, c ≤ V.fidelity (tensorInput m n k X.val)}

def physicalHaarAverage (m n k s : ℕ) (hsD : s ≤ m*n) :
    Matrix (Fin (m^k) × Fin (n^k)) (Fin (m^k) × Fin (n^k)) ℂ :=
  SpectralProtocol.bipartitePowerTransport m n k (flatHaarAverage (m*n) s k hsD)

theorem rankBudgetProjection_properties (m n k s : ℕ) :
    (rankBudgetProjection m n k s).IsHermitian ∧
    rankBudgetProjection m n k s*rankBudgetProjection m n k s=rankBudgetProjection m n k s ∧
    (rankBudgetProjection m n k s).rank=(rankBudgetProjector (m*n) k s).rank := by
  constructor
  · exact (rankBudgetProjector_isHermitian (m*n) k s).reindex _
  constructor
  · rw [rankBudgetProjection, ← map_mul, rankBudgetProjector_idempotent]
  · exact Matrix.rank_reindex _ _ _

theorem tensorInput_rankBudget_supported (m n k s : ℕ) (X : RankBudgetInput (m*n) s) :
    rankBudgetProjection m n k s*tensorInput m n k X.val*rankBudgetProjection m n k s =
      tensorInput m n k X.val := by
  have hleft := rankBudgetProjector_mul_tensorMatrix (m*n) k s X.val X.property.2.2
  have hright : tensorMatrix X.val k*rankBudgetProjector (m*n) k s=tensorMatrix X.val k := by
    have h := congrArg Matrix.conjTranspose hleft
    simpa only [Matrix.conjTranspose_mul, (rankBudgetProjector_isHermitian (m*n) k s).eq,
      ← tensorMatrix_conjTranspose, X.property.1.isHermitian.eq] using h
  rw [rankBudgetProjection, tensorInput, ← map_mul, ← map_mul, hleft, hright]

def rankBudgetOrbitInput (D s : ℕ) (hs : 0 < s) (hsD : s ≤ D) (U : OneCopyUnitary D) :
    RankBudgetInput D s :=
  ⟨(U : Matrix (Fin D) (Fin D) ℂ)*flatCoordinateDensity D s hsD*
    (U : Matrix (Fin D) (Fin D) ℂ)ᴴ,
    (fixed_density_unitary_conjugate_density D _ (flatCoordinateDensity_density D s hs hsD) U).1,
    (fixed_density_unitary_conjugate_density D _ (flatCoordinateDensity_density D s hs hsD) U).2,
    by
      apply (Matrix.rank_mul_le_left _ _).trans
      apply (Matrix.rank_mul_le_right _ _).trans
      exact (flatCoordinateDensity_rank D s hs hsD).le⟩

theorem physicalHaarAverage_density (m n k s : ℕ) (hs : 0 < s) (hsD : s ≤ m*n) :
    APPT.Quantum.IsDensity (physicalHaarAverage m n k s hsD) := by
  constructor
  · exact (flatHaarAverage_density (m*n) s k hs hsD).1.submatrix
      (SpectralProtocol.bipartitePowerCoordinates m n k).symm
  · rw [physicalHaarAverage, SpectralProtocol.bipartitePowerTransport, SpectralProtocol.reindex_trace]
    exact (flatHaarAverage_density (m*n) s k hs hsD).2

theorem physicalHaarAverage_purity (m n k s : ℕ) (hsD : s ≤ m*n) :
    (physicalHaarAverage m n k s hsD*physicalHaarAverage m n k s hsD).trace.re =
      (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re := by
  rw [physicalHaarAverage, ← map_mul]
  exact congrArg Complex.re (SpectralProtocol.reindex_trace _ _)

def fidelityLinear {a b K : ℕ} (V : KrausPPTProtocol a b K) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ →ₗ[ℝ] ℝ where
  toFun := V.fidelity
  map_add' X Y := by
    simp only [KrausPPTProtocol.fidelity, overlap, Extraction.krausApply,
      Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, Matrix.trace_add, Complex.add_re]
  map_smul' c X := by
    exact overlap_real_smul V.A V.U X c

theorem rankBudget_guarantee_le_haar (m n k s K : ℕ) (hs : 0 < s) (hsD : s ≤ m*n)
    (V : KrausPPTProtocol (m^k) (n^k) K) (c : ℝ)
    (hc : ∀ X : RankBudgetInput (m*n) s, c ≤ V.fidelity (tensorInput m n k X.val)) :
    c ≤ V.fidelity (physicalHaarAverage m n k s hsD) := by
  let L := (SpectralProtocol.bipartitePowerTransport m n k).toLinearMap.toContinuousLinearMap
  have hint := integrable_orbitTensor (m*n) k (flatCoordinateDensity (m*n) s hsD)
  have htrans : physicalHaarAverage m n k s hsD =
      ∫ U : OneCopyUnitary (m*n), tensorInput m n k
        (rankBudgetOrbitInput (m*n) s hs hsD U).val ∂unitaryHaar (m*n) := by
    exact (L.integral_comp_comm hint).symm
  have hi := L.integrable_comp hint
  have hfid := (fidelityLinear V).toContinuousLinearMap.integral_comp_comm hi
  have hfid' : (∫ U : OneCopyUnitary (m*n), V.fidelity
      (tensorInput m n k (rankBudgetOrbitInput (m*n) s hs hsD U).val) ∂unitaryHaar (m*n)) =
      V.fidelity (physicalHaarAverage m n k s hsD) := by
    rw [htrans]
    exact hfid
  have h := integral_mono (integrable_const c) ((fidelityLinear V).toContinuousLinearMap.integrable_comp hi)
    (fun U => hc (rankBudgetOrbitInput (m*n) s hs hsD U))
  have hh : c ≤ ∫ U : OneCopyUnitary (m*n), V.fidelity
      (tensorInput m n k (rankBudgetOrbitInput (m*n) s hs hsD U).val) ∂unitaryHaar (m*n) := by
    simp only [integral_const, probReal_univ, one_smul] at h
    change c ≤ ∫ U : OneCopyUnitary (m*n), V.fidelity
      (tensorInput m n k (rankBudgetOrbitInput (m*n) s hs hsD U).val) ∂unitaryHaar (m*n) at h
    exact h
  exact hh.trans_eq hfid'

theorem common_support_local_profile (a b d K : ℕ) (hd : 0 < d) (hK : 0 < K)
    (P : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) (hr : P.rank ≤ (a/d)*(b/d)) :
    ∃ V : KrausPPTProtocol a b K, V.IsProductLocal ∧
      ∀ X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
        APPT.Quantum.IsDensity X → P*X*P=X → V.fidelity X=profile d K := by
  obtain ⟨U,A,B,hA,hB,hV⟩ := Extraction.finite_projection_fidelity_extractor a b (min d K) K
    (lt_min hd hK) (min_le_right _ _) P hP hPP
    (smaller_dimension_feasible (lt_min hd hK) (min_le_left _ _) hr)
  refine ⟨localProtocol U A B hA hB, localProtocol_isProductLocal U A B hA hB, ?_⟩
  intro X hX hPX
  rw [localProtocol_fidelity, overlap, hV X hX hPX]
  unfold profile
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases h : d ≤ K
  · rw [min_eq_left h, min_eq_right ((div_le_one hKR).mpr (by exact_mod_cast h))]
  · rw [min_eq_right (le_of_not_ge h),
      min_eq_left ((one_le_div hKR).mpr (by exact_mod_cast (le_of_not_ge h)))]
    exact div_self hKR.ne'

/-- Actual finite physical minimax bounds for the entire rank-budget continuum.
The only class premise is inclusion of actual product-local protocols. -/
theorem rankBudget_class_minimax_finite (m n k s d K : ℕ) (hs : 0 < s) (hsD : s ≤ m*n)
    (hd : 0 < d) (hK : 0 < K)
    (hbudget : (rankBudgetProjector (m*n) k s).rank ≤ (m^k/d)*(n^k/d))
    (C : KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : ∀ V, V.IsProductLocal → C V) :
    profile d K ≤ rankBudgetClassMinimax m n k s K C ∧
      rankBudgetClassMinimax m n k s K C ≤ min 1 (min ((m : ℝ)^k/K)
        (Real.sqrt ((flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re *
          (((m*n : ℕ) : ℝ)^k/(K : ℝ)^2)))) := by
  have hP := rankBudgetProjection_properties m n k s
  obtain ⟨V,hlocal,hV⟩ := common_support_local_profile (m^k) (n^k) d K hd hK
    (rankBudgetProjection m n k s) hP.1 hP.2.1 (by rwa [hP.2.2])
  let S : Set ℝ := {c | ∃ V : KrausPPTProtocol (m^k) (n^k) K,
    C V ∧ ∀ X : RankBudgetInput (m*n) s, c ≤ V.fidelity (tensorInput m n k X.val)}
  have hlo : profile d K ∈ S := by
    refine ⟨V,hC V hlocal,fun X => ?_⟩
    exact (hV _ (tensorInput_density m n k X.val ⟨X.property.1,X.property.2.1⟩)
      (tensorInput_rankBudget_supported m n k s X)).ge
  have hup (c : ℝ) (hc : c ∈ S) : c ≤ min 1 (min ((m : ℝ)^k/K)
      (Real.sqrt ((flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re *
        (((m*n : ℕ) : ℝ)^k/(K : ℝ)^2)))) := by
    obtain ⟨W,hCW,hW⟩ := hc
    have h := rankBudget_guarantee_le_haar m n k s K hs hsD W c hW
    letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
    have hh := ExtractionLocalCap.kraus_target_overlap_full_envelope W.A W.complete W.ptPositive
      (physicalHaarAverage m n k s hsD) (physicalHaarAverage_density m n k s hs hsD) W.U
    apply h.trans
    simpa only [KrausPPTProtocol.fidelity, overlap, Fintype.card_fin,
      physicalHaarAverage_purity, Nat.cast_pow, Nat.cast_mul, mul_pow] using hh
  exact ⟨le_csSup ⟨_,hup⟩ hlo, csSup_le ⟨_,hlo⟩ hup⟩

end
end ExtractionSchur
