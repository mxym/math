import SchurMinimax.Packing
import LOCCInterface.Closure

open scoped BigOperators Topology ComplexOrder
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport MinimaxProfile
noncomputable section
set_option backward.isDefEq.respectTransparency false

inductive RankProtocolClass where
  | productLocal
  | finiteLOCC
  | closureLOCC
  | completelyPPT

def RankProtocolClass.Allows {a b K : ℕ} (C : RankProtocolClass) (V : KrausPPTProtocol a b K) : Prop :=
  match C with
  | .productLocal => V.IsProductLocal
  | .finiteLOCC => ExtractionLOCC.IsFiniteLOCCProtocol V
  | .closureLOCC => ExtractionLOCC.IsClosureLOCCProtocol V
  | .completelyPPT => True

theorem RankProtocolClass.allows_productLocal {a b K : ℕ} (C : RankProtocolClass)
    (V : KrausPPTProtocol a b K) (hV : V.IsProductLocal) : C.Allows V := by
  cases C with
  | productLocal => exact hV
  | finiteLOCC => exact ExtractionLOCC.productLocal_isFiniteLOCCProtocol V hV
  | closureLOCC => exact ExtractionLOCC.productLocal_isClosureLOCCProtocol V hV
  | completelyPPT => trivial

def rankBudgetPhysicalMinimax (C : RankProtocolClass) (m n k s K : ℕ) : ℝ :=
  rankBudgetClassMinimax m n k s K C.Allows

def rankBudgetEta (m n k s : ℕ) (hsD : s ≤ m*n) : ℝ :=
  Real.sqrt (((rankBudgetProjector (m*n) k s).rank : ℝ) *
    (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re)

theorem rankBudgetEta_ge_one (m n k s : ℕ) (hs : 0 < s) (hsD : s ≤ m*n) :
    1 ≤ rankBudgetEta m n k s hsD := by
  have h := haarOrbitAverage_rank_times_purity_ge_one (m*n) k (flatCoordinateDensity (m*n) s hsD)
    (flatCoordinateDensity_density (m*n) s hs hsD)
  have hh : 1 ≤ ((rankBudgetProjector (m*n) k s).rank : ℝ) *
      (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re := by
    simpa only [flatHaarAverage, flatCoordinateDensity_rank (m*n) s hs hsD] using h
  simpa only [rankBudgetEta, Real.sqrt_one] using Real.sqrt_le_sqrt hh

theorem rankBudgetEta_limit (m n s : ℕ) (hs : 0 < s) (hsD : s ≤ m*n) :
    Tendsto (fun k => rankBudgetEta m n k s hsD) atTop (𝓝 1) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (rankBudget_rank_times_purity_limit (m*n) s hs hsD)
  simpa only [rankBudgetEta, Function.comp_def, Real.sqrt_one] using h

theorem rankBudget_eta_collision_identity (m n k s : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hs : 0 < s) (hsD : s ≤ m*n) :
    rankBudgetEta m n k s hsD*rankBudgetCollisionWidth m n k s =
      Real.sqrt ((((m*n : ℕ) : ℝ)^k)*
        (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re) := by
  have hΩ := (flatHaarAverage_density (m*n) s k hs hsD).1
  have hΩ2 : (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).PosSemidef := by
    simpa only [hΩ.isHermitian.eq] using Matrix.posSemidef_self_mul_conjTranspose (flatHaarAverage (m*n) s k hsD)
  have hp : 0 ≤ (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re :=
    (RCLike.nonneg_iff.mp hΩ2.trace_nonneg).1
  have hr : (0 : ℝ) < (rankBudgetProjector (m*n) k s).rank := by
    exact_mod_cast rankBudget_rank_pos m n k s hm hn hs
  rw [rankBudgetEta, rankBudgetCollisionWidth, ← Real.sqrt_mul (mul_nonneg hr.le hp)]
  congr 1
  field_simp

theorem rankBudget_class_profile_bounds (m n k s K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hs : 0 < s) (hsD : s ≤ m*n) (hK : 0 < K)
    (C : KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : ∀ V, V.IsProductLocal → C V) :
    profile (rankBudgetPacking m n k s hm) K ≤ rankBudgetClassMinimax m n k s K C ∧
      rankBudgetClassMinimax m n k s K C ≤
        profile (rankBudgetEta m n k s hsD*rankBudgetWidth m n k s) K := by
  have hprops := rankBudgetPacking_properties m n k s hm hn hs
  have h := rankBudget_class_minimax_finite m n k s _ K hs hsD hprops.1 hK hprops.2.2 C hC
  refine ⟨h.1,h.2.trans ?_⟩
  have hη := rankBudgetEta_ge_one m n k s hs hsD
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hΩ := (flatHaarAverage_density (m*n) s k hs hsD).1
  have hp : 0 ≤ (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re := by
    have hΩ2 : (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).PosSemidef := by
      simpa only [hΩ.isHermitian.eq] using Matrix.posSemidef_self_mul_conjTranspose (flatHaarAverage (m*n) s k hsD)
    exact (RCLike.nonneg_iff.mp hΩ2.trace_nonneg).1
  have hsqrt : Real.sqrt ((flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re *
      (((m*n : ℕ) : ℝ)^k/(K : ℝ)^2)) =
      (rankBudgetEta m n k s hsD*rankBudgetCollisionWidth m n k s)/(K : ℝ) := by
    rw [rankBudget_eta_collision_identity m n k s hm hn hs hsD]
    have he : (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re *
        (((m*n : ℕ) : ℝ)^k/(K : ℝ)^2) =
        ((((m*n : ℕ) : ℝ)^k)*
          (flatHaarAverage (m*n) s k hsD*flatHaarAverage (m*n) s k hsD).trace.re)/(K : ℝ)^2 := by ring
    rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq hKR.le]
  rw [hsqrt]
  apply le_min (min_le_left _ _)
  by_cases ha : (m : ℝ)^k ≤ rankBudgetCollisionWidth m n k s
  · rw [rankBudgetWidth, min_eq_left ha]
    apply ((min_le_right _ _).trans (min_le_left _ _)).trans
    apply div_le_div_of_nonneg_right _ hKR.le
    have hp : 0 ≤ (m : ℝ)^k := by positivity
    nlinarith
  · rw [rankBudgetWidth, min_eq_right (le_of_not_ge ha)]
    exact (min_le_right _ _).trans (min_le_right _ _)

/-- Explicit finite relative error bound, uniform over every positive target.
All ranks, moments, physical channels and the Haar adversary are actual. -/
theorem rankBudget_physical_relative_bound (C : RankProtocolClass) (m n k s : ℕ)
    (hm : 0 < m) (hn : 0 < n) (hs : 0 < s) (hsD : s ≤ m*n) :
    0 ≤ worstRelativeError (rankBudgetPhysicalMinimax C m n k s) (rankBudgetWidth m n k s) ∧
      worstRelativeError (rankBudgetPhysicalMinimax C m n k s) (rankBudgetWidth m n k s) ≤
        max (1-(rankBudgetPacking m n k s hm : ℝ)/rankBudgetWidth m n k s)
          (rankBudgetEta m n k s hsD-1) := by
  have hprops := rankBudgetPacking_properties m n k s hm hn hs
  apply worstRelativeError_bounds (by positivity) hprops.2.1
    (rankBudgetWidth_pos m n k s hm hn hs) (rankBudgetEta_ge_one m n k s hs hsD)
  · intro K hK
    exact (rankBudget_class_profile_bounds m n k s K hm hn hs hsD hK C.Allows C.allows_productLocal).1
  · intro K hK
    exact (rankBudget_class_profile_bounds m n k s K hm hn hs hsD hK C.Allows C.allows_productLocal).2

/-- The entire manuscript minimax profile, with the supremum taken over all
positive integers K, for actual local, finite LOCC, closure LOCC, and cPPT
channels. No rate restriction or performance certificate is supplied. -/
theorem rankBudget_target_uniform_minimax (C : RankProtocolClass) (m n s : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n) :
    Tendsto (fun k => worstRelativeError (rankBudgetPhysicalMinimax C m n k s)
      (rankBudgetWidth m n k s)) atTop (𝓝 0) := by
  have hmp : 0 < m := by omega
  have hnp : 0 < n := hmp.trans_le hmn
  have hprops (k : ℕ) := rankBudgetPacking_properties m n k s hmp hnp hs
  apply target_uniform_relative_limit
    (d := fun k => (rankBudgetPacking m n k s hmp : ℝ))
    (w := fun k => rankBudgetWidth m n k s)
    (η := fun k => rankBudgetEta m n k s hsD.le)
    (F := fun k => rankBudgetPhysicalMinimax C m n k s)
    (fun k => by positivity) (fun k => (hprops k).2.1)
    (fun k => rankBudgetWidth_pos m n k s hmp hnp hs)
    (fun k => rankBudgetEta_ge_one m n k s hs hsD.le)
  · intro k K hK
    exact (rankBudget_class_profile_bounds m n k s K hmp hnp hs hsD.le hK C.Allows C.allows_productLocal).1
  · intro k K hK
    exact (rankBudget_class_profile_bounds m n k s K hmp hnp hs hsD.le hK C.Allows C.allows_productLocal).2
  · exact rankBudgetPacking_ratio_limit m n s hmp hmn hs hsD
  · exact rankBudgetEta_limit m n s hs hsD.le

/-- The same uniform relative law with its quantifiers expanded: the single
blocklength threshold precedes every target K, including arbitrarily large K. -/
theorem rankBudget_target_uniform_relative_error (C : RankProtocolClass) (m n s : ℕ)
    (hm : 2 ≤ m) (hmn : m ≤ n) (hs : 0 < s) (hsD : s < m*n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ K : ℕ, 0 < K →
      |rankBudgetPhysicalMinimax C m n k s K/profile (rankBudgetWidth m n k s) K-1| < ε := by
  have hmp : 0 < m := by omega
  have hnp : 0 < n := hmp.trans_le hmn
  have hratio := rankBudgetPacking_ratio_limit m n s hmp hmn hs hsD
  have heta := rankBudgetEta_limit m n s hs hsD.le
  have herr := (Tendsto.const_sub 1 hratio).max (heta.sub_const 1)
  have herr0 : Tendsto (fun k => max
      (1-(rankBudgetPacking m n k s hmp : ℝ)/rankBudgetWidth m n k s)
      (rankBudgetEta m n k s hsD.le-1)) atTop (𝓝 0) := by simpa using herr
  filter_upwards [(tendsto_order.1 herr0).2 ε hε] with k hk
  intro K hK
  have hprops := rankBudgetPacking_properties m n k s hmp hnp hs
  have hfinite := rankBudget_class_profile_bounds m n k s K hmp hnp hs hsD.le hK
    C.Allows C.allows_productLocal
  exact (relative_profile_bound (by positivity) hprops.2.1
    (rankBudgetWidth_pos m n k s hmp hnp hs) (rankBudgetEta_ge_one m n k s hs hsD.le)
    (by exact_mod_cast hK) hfinite.1 hfinite.2).trans_lt hk

/-- The cPPT class is exactly the pre-existing actual Kraus minimax value. -/
theorem rankBudget_completelyPPT_eq_minimaxValue (m n k s K : ℕ) :
    rankBudgetPhysicalMinimax .completelyPPT m n k s K=rankBudgetMinimax m n k s K := by
  unfold rankBudgetPhysicalMinimax rankBudgetClassMinimax rankBudgetMinimax minimaxValue
  congr 1
  ext c
  simp only [Set.mem_setOf_eq, guaranteedValues, RankProtocolClass.Allows, true_and]

theorem rankBudget_class_minimax_mono (m n k s K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hs : 0 < s) (hsD : s ≤ m*n) (hK : 0 < K)
    (C E : KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : ∀ V, V.IsProductLocal → C V) (hCE : ∀ V, C V → E V) :
    rankBudgetClassMinimax m n k s K C ≤ rankBudgetClassMinimax m n k s K E := by
  let S := fun Q : KrausPPTProtocol (m^k) (n^k) K → Prop =>
    {c : ℝ | ∃ V : KrausPPTProtocol (m^k) (n^k) K,
      Q V ∧ ∀ X : RankBudgetInput (m*n) s, c ≤ V.fidelity (tensorInput m n k X.val)}
  have hprops := rankBudgetPacking_properties m n k s hm hn hs
  have hP := rankBudgetProjection_properties m n k s
  obtain ⟨V,hLocal,hV⟩ := common_support_local_profile (m^k) (n^k)
    (rankBudgetPacking m n k s hm) K hprops.1 hK
    (rankBudgetProjection m n k s) hP.1 hP.2.1 (by rw [hP.2.2]; exact hprops.2.2)
  have hnonempty : (S C).Nonempty := by
    refine ⟨profile (rankBudgetPacking m n k s hm) K,V,hC V hLocal,fun X => ?_⟩
    exact (hV _ (tensorInput_density m n k X.val ⟨X.property.1,X.property.2.1⟩)
      (tensorInput_rankBudget_supported m n k s X)).ge
  have hbd : BddAbove (S E) := by
    refine ⟨1,?_⟩
    rintro c ⟨W,hW,hguar⟩
    let X := rankBudgetOrbitInput (m*n) s hs hsD 1
    have hX := tensorInput_density m n k X.val ⟨X.property.1,X.property.2.1⟩
    letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
    have hh := ExtractionLocalCap.kraus_target_overlap_full_envelope W.A W.complete W.ptPositive
      (tensorInput m n k X.val) hX W.U
    have hbound : W.fidelity (tensorInput m n k X.val) ≤ 1 := by
      exact hh.trans (min_le_left _ _)
    exact (hguar X).trans hbound
  apply csSup_le hnonempty
  rintro c ⟨W,hW,hguar⟩
  exact le_csSup hbd ⟨W,hCE W hW,hguar⟩

theorem rankBudget_physical_class_chain (m n k s K : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hs : 0 < s) (hsD : s ≤ m*n) (hK : 0 < K) :
    rankBudgetPhysicalMinimax .productLocal m n k s K ≤ rankBudgetPhysicalMinimax .finiteLOCC m n k s K ∧
    rankBudgetPhysicalMinimax .finiteLOCC m n k s K ≤ rankBudgetPhysicalMinimax .closureLOCC m n k s K ∧
    rankBudgetPhysicalMinimax .closureLOCC m n k s K ≤ rankBudgetPhysicalMinimax .completelyPPT m n k s K := by
  constructor
  · exact rankBudget_class_minimax_mono m n k s K hm hn hs hsD hK _ _
      RankProtocolClass.productLocal.allows_productLocal
      ExtractionLOCC.productLocal_isFiniteLOCCProtocol
  constructor
  · exact rankBudget_class_minimax_mono m n k s K hm hn hs hsD hK _ _
      RankProtocolClass.finiteLOCC.allows_productLocal
      ExtractionLOCC.finiteLOCC_isClosureLOCCProtocol
  · exact rankBudget_class_minimax_mono m n k s K hm hn hs hsD hK _ _
      RankProtocolClass.closureLOCC.allows_productLocal (by intro V hV; trivial)

end
end ExtractionSchur
