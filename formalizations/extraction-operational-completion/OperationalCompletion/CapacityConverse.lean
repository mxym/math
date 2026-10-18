import OperationalCompletion.SharpFidelity
import OperationalCompletion.EventualExact

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

def faithfulRate (m n : ℕ) (p : Fin (m*n) → ℝ) : ℝ :=
  min (Real.log m) ((Real.log m+Real.log n-entropy p)/2)

def eventualExactRate (m n : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) : ℝ :=
  min (Real.log m) ((Real.log m+Real.log n-Real.log X.rank)/2)

theorem localBeta_tendsto_zero (m : ℕ) (hm : 0<m) (K : ℕ → ℕ) (hK : ∀ k,0<K k)
    (R : ℝ) (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRA : Real.log m<R) : Tendsto (fun k => localBeta m k (K k)) atTop (nhds 0) := by
  have hB : 0<max 0 (R-Real.log m) := lt_max_of_lt_right (sub_pos.mpr hRA)
  have hu := positive_sequence_exponential_upper (fun k => localBeta m k (K k))
    (fun k => localBeta_pos m k (K k) hm (hK k)) _ (localBeta_log_rate m hm K hK R hR)
    (max 0 (R-Real.log m)/2) (by linarith)
  have hexp : Tendsto (fun k : ℕ => Real.exp (-(k:ℝ)*(max 0 (R-Real.log m)/2)))
      atTop (nhds 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const (show 0<max 0 (R-Real.log m)/2 by linarith)) using 1
    ext k
    congr 1
    ring
  apply squeeze_zero' (Eventually.of_forall (fun k => (localBeta_pos m k (K k) hm (hK k)).le)) _ hexp
  convert hu using 1
  ext k
  congr 2
  ring

/-- Strong converse above the complete faithful capacity, retaining both the
entropy obstruction and the smaller local dimension obstruction. -/
theorem ppt_above_faithful_rate (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (V : ∀ k,KrausPPTProtocol (m^k) (n^k) (K k))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (habove : faithfulRate m n hX.1.isHermitian.eigenvalues<R) :
    Tendsto (fun k => (V k).fidelity (tensorInput m n k X)) atTop (nhds 0) := by
  rcases (min_lt_iff.mp habove) with hlocal | hentropy
  · exact squeeze_zero' (Eventually.of_forall (fun k =>
      ((V k).fidelity_bounds (hK k) _ (tensorInput_density m n k X hX)).1))
      (Eventually.of_forall (fun k => KrausPPTProtocol.tensor_localBeta m n k (K k) (hK k) (V k) X hX))
      (localBeta_tendsto_zero m hm K hK R hR hlocal)
  · exact MinimaxProfile.KrausPPTProtocol.tensor_rate_strong_converse m n hm hn K hK V X hX R hR hentropy

theorem ppt_rank_obstruction_eventually (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hRank : Real.log m+Real.log n-2*R<Real.log X.rank) :
    ∀ᶠ k : ℕ in atTop,∀ V : KrausPPTProtocol (m^k) (n^k) (K k),
      V.fidelity (tensorInput m n k X)<1 := by
  classical
  letI : Nonempty (Fin (m*n)) := ⟨⟨0,Nat.mul_pos hm hn⟩⟩
  let p := hX.1.isHermitian.eigenvalues
  have hp : ∀ i,0≤p i := hX.1.eigenvalues_nonneg
  have hs : ∑ i,p i=1 := density_eigenvalues_sum X hX
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  let u := uniformLaw (ι := PositiveSupport p)
  let q := extendSupport p u
  have hq : ∀ i,0≤q i := extendSupport_nonneg p u (fun i => (uniformLaw_pos i).le)
  have hqs : ∑ i,q i=1 := by rw [extendSupport_sum]; exact uniformLaw_sum
  have hqH : entropy q=Real.log X.rank := by
    rw [extendSupport_entropy]
    have hh := divergence_uniformLaw u (uniformLaw_sum (ι := PositiveSupport p))
    rw [divergence_self] at hh
    have hr : Fintype.card (PositiveSupport p)=X.rank := density_positiveSupport_card_eq_rank X hX.1
    rw [hr] at hh
    linarith
  let c₀ := Real.log m+Real.log n-2*R
  let c₁ := (c₀+Real.log X.rank)/2
  have hc1 : c₀<c₁ := by dsimp [c₀,c₁]; linarith
  have hqgap : c₁<entropy q := by rw [hqH]; dsimp [c₁,c₀]; linarith
  have ht := iid_subset_tail_eventual_lower p q hp hs hq hqs (extendSupport_support p u)
    c₁ hqgap 1 (by norm_num)
  filter_upwards [ht,(tailCardinalityRate_tendsto m n hm hn K hK R hR).eventually_lt_const hc1,
    eventually_gt_atTop 0] with k htail hcut hk
  intro V
  obtain ⟨S,hS,herr⟩ := KrausPPTProtocol.tensor_error_tail m n k (K k) (hK k) V X hX
    (1/2) (by norm_num) (by norm_num)
  have hcard : (S.card:ℝ)≤Real.exp ((k:ℝ)*c₁) := by
    have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
    have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hKR : (0:ℝ)<K k := Nat.cast_pos.mpr (hK k)
    have hkR : (k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hk
    have he : (k:ℝ)*tailCardinalityRate m n K k=Real.log (4*tensorBudget m n k (K k)) := by
      unfold tailCardinalityRate
      field_simp
    have hquot : tensorBudget m n k (K k)/(1/2:ℝ)^2=
        Real.exp ((k:ℝ)*tailCardinalityRate m n K k) := by
      rw [he,Real.exp_log (by unfold tensorBudget; positivity)]
      ring
    rw [hquot] at hS
    exact hS.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcut.le (Nat.cast_nonneg k)))
  have hmass := htail S hcard
  have hpos : 0<1-wordMass p k S := (Real.exp_pos _).trans_le hmass
  change (1-1/2:ℝ)*(1-wordMass p k S)≤1-V.fidelity (tensorInput m n k X) at herr
  nlinarith

/-- Above the rank-sensitive eventual-exact capacity, no actual PPT protocol
can be exact at any sufficiently large block. The equality boundary remains
open to finite integer packing effects as in the manuscript. -/
theorem ppt_above_eventualExact_rate (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (habove : eventualExactRate m n X<R) :
    ∀ᶠ k : ℕ in atTop,∀ V : KrausPPTProtocol (m^k) (n^k) (K k),
      V.fidelity (tensorInput m n k X)<1 := by
  rcases (min_lt_iff.mp habove) with hlocal | hrank
  · filter_upwards [(localBeta_tendsto_zero m hm K hK R hR hlocal).eventually_lt_const
      (show (0:ℝ)<1 by norm_num)] with k hk
    intro V
    exact (KrausPPTProtocol.tensor_localBeta m n k (K k) (hK k) V X hX).trans_lt hk
  · exact ppt_rank_obstruction_eventually m n hm hn K hK R hR X hX (by linarith)

end
end OperationalCompletion
