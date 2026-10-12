import BapatSortedWedgeBound

set_option autoImplicit false
open MeasureTheory Filter BapatFiniteRank BapatRankTwo.MarkedInversions
open scoped Topology

namespace BapatRealExistence
noncomputable section

/-- The appended four rows cannot decrease the unnormalised pair score. -/
theorem appendSelectorRows_score_le {n : ℕ} (v : Fin n → Fin 4 → ℝ) (t c : ℝ) :
    realPairScore (rowRatios v t) ≤ realPairScore (rowRatios (appendSelectorRows v c) t) := by
  have he : rowRatios (appendSelectorRows v c) t =
      Fin.append (rowRatios v t) (rowRatios (selectorRows c) t) := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [rowRatios,appendSelectorRows]
  rw [he]
  exact realPairScore_append_le _ _

/-- A fixed quantitative margin absorbs the four selector rows. -/
theorem score_threshold {m : ℕ} (hm : 200≤m) {s : ℝ} (hs : (3/4:ℝ)*(m:ℝ)^2<s) :
    ((m+4:ℕ):ℝ)^4 < 2*s^2 := by
  have hm' : (200:ℝ)≤m := by exact_mod_cast hm
  have h0 : 0≤(m:ℝ)^2 := sq_nonneg _
  have hsize : ((m:ℝ)+4)^2 < (21/20:ℝ)*(m:ℝ)^2 := by nlinarith
  have hs0 : 0<s := by nlinarith
  have hsq : (((m:ℝ)+4)^2)^2 < ((21/20:ℝ)*(m:ℝ)^2)^2 :=
    (sq_lt_sq₀ (sq_nonneg _) (by positivity)).mpr hsize
  have hs' : ((3/4:ℝ)*(m:ℝ)^2)^2<s^2 :=
    (sq_lt_sq₀ (by positivity) hs0.le).mpr hs
  push_cast
  nlinarith [sq_nonneg ((m:ℝ)^2)]

/-- Choose a genuine finite canonical cloud whose augmented list has enough score. -/
theorem exists_canonical_cloud_score_gap :
    ∃ (m : ℕ) (v : Fin m → Fin 4 → ℝ) (t : ℝ),
      200≤m ∧ 1/2≤t ∧ t<3/4 ∧
      0<‖complexEval (formsProduct v) (canonicalComplex4 t)‖ ∧
      (∀ z, rowProductModulus v z≤‖complexEval (formsProduct v) (canonicalComplex4 t)‖) ∧
      ((m+4:ℕ):ℝ)^4 < 2*(realPairScore (rowRatios (appendSelectorRows v (selectorParameter t)) t))^2 := by
  obtain ⟨w,t,htbounds,ht,hw,hpos,hmax⟩ := exists_canonical_maximizing_cloud
  have hg := triangular_real_ratio_three_halves w hw t ht
  have ht' := (tendsto_order.mp ht).2 (3/4) (by norm_num : (1/2:ℝ)<3/4)
  obtain ⟨m,hm,hgm,htm⟩ := ((eventually_ge_atTop 200).and (hg.and ht')).exists
  let v := cloudRows (w m) m
  have he := empirical_pair_sum (w m) (by omega : m≠0) (fun x => realRowRatio (t m) x)
  have hscore : (3/4:ℝ)*(m:ℝ)^2 < realPairScore (rowRatios v (t m)) := by
    have hp : (0:ℝ)<(m:ℝ)^2 := by positivity
    have hg' := mul_lt_mul_of_pos_left hgm hp
    have hh : empiricalAverage (w m) m (fun x => empiricalAverage (w m) m
        (fun y => |realRowRatio (t m) x-realRowRatio (t m) y|)) =
      empiricalAverage (w m) m (fun x => empiricalAverage (w m) m
        (fun y => |realRowRatio (t m) y-realRowRatio (t m) x|)) := by
      congr 1; funext x; congr 1; funext y; exact abs_sub_comm _ _
    rw [hh,he] at hg'
    change (m:ℝ)^2*(3/2)<2*realPairScore (rowRatios v (t m)) at hg'
    linarith
  refine ⟨m,v,t m,hm,(htbounds m).1,htm,hpos m,hmax m,?_⟩
  exact score_threshold hm (hscore.trans_le (appendSelectorRows_score_le v (t m) (selectorParameter (t m))))

end
end BapatRealExistence
