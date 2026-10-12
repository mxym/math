import APPTReview.PrefixVertex
import APPTReview.OuterValues

open scoped BigOperators
namespace APPTReview

/-- The ordered-simplex relaxation has the two claimed upper branches.
All spectra in the halfspace are covered by exact gap coordinates and mass
transport; there is no assumption that a maximizer has a prescribed support. -/
theorem ordered_rectangular_cut_upper {D m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    (hD : D=m*n) (r q : Fin D) (hrq : r ≤ q)
    (hr : 2*(r.val+1)+m=m*m) (hL : (r.val+1)+(q.val+1)+m=D)
    (f : Fin D → ℝ) (hf : Antitone f) (hn : ∀ i, 0 ≤ f i) (hs : (∑ i,f i)=1)
    (hcut : (∑ i,prefixCut r q i*f i) ≤ 0) :
    spectralSquares f ≤ max (outerSpikePurity m n) (roundedPlateauPurity m n) := by
  let R : ℝ := ((r.val+1:ℕ):ℝ)
  let T : ℝ := ((q.val+1:ℕ):ℝ)
  let L : ℝ := R+T
  let C := max (outerSpikePurity m n) (roundedPlateauPurity m n)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hLP : 0 < L := add_pos hRpos hTpos
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmP : (0:ℝ) < m := by linarith
  have hnP : 0 < n := by omega
  have hDR : (D:ℝ)=(m:ℝ)*n := by exact_mod_cast hD
  have hLR : L=(m:ℝ)*n-m := by
    have he : R+T+(m:ℝ)=(D:ℝ) := by dsimp [R,T]; exact_mod_cast hL
    dsimp [L]
    linarith
  have hRR : R=(m:ℝ)*((m:ℝ)-1)/2 := by
    have he : 2*R+(m:ℝ)=(m:ℝ)*(m:ℝ) := by dsimp [R]; exact_mod_cast hr
    nlinarith
  have hbase : 1/L ≤ C := by
    rw [hLR]
    exact (outerSpike_dominates_uniform hm hmn).trans (le_max_left _ _)
  have hfull (k : Fin D) (hg : 0 < prefixCutValue r q k) :
      cutEdgePurity L (prefixCutHeight r q k) ((k.val+1:ℕ):ℝ) m ≤ C := by
    have hi : (1:ℝ) ≤ ((k.val+1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ k.val+1 by omega)
    by_cases hkr : k ≤ r
    · rw [show prefixCutHeight r q k=((k.val+1:ℕ):ℝ) by simp [prefixCutHeight,hkr]]
      have hu := cutEdge_early_full_bound L ((k.val+1:ℕ):ℝ) m hLP hi hmP.le
      have he : (L+3*(m:ℝ)+(m:ℝ)^2)/(L+2*(m:ℝ))^2=outerSpikePurity m n := by
        rw [hLR]
        unfold outerSpikePurity
        congr 1 <;> ring
      exact (hu.trans_eq he).trans (le_max_left _ _)
    · by_cases hkq : k ≤ q
      · rw [show prefixCutHeight r q k=R by simp [prefixCutHeight,hkr,hkq,R],hRR,hLR]
        exact (cutEdge_middle_le_rounded (by omega : 2 ≤ m) hnP (k.val+1)).trans (le_max_right _ _)
      · have hiL : ((k.val+1:ℕ):ℝ) < L := by
          have he := (prefixCutValue_pos_iff r q k hrq).mp hg
          dsimp [L,R,T]
          exact_mod_cast he
        rw [show prefixCutHeight r q k=L-((k.val+1:ℕ):ℝ) by simp [prefixCutHeight,hkr,hkq,L,R,T]]
        exact (cutEdge_late_bound L ((k.val+1:ℕ):ℝ) m hLP (by positivity) hiL hmP.le).trans hbase
  apply ordered_spectrum_cut_bound f (prefixCut r q) C hf hn hs hcut
  · intro k hg
    have hnon : prefixCutValue r q k ≤ 0 := hg
    have hlen := (prefixCutValue_nonpos_iff r q k hrq).mp hnon
    have hlenR : L ≤ ((k.val+1:ℕ):ℝ) := by dsimp [L,R,T]; exact_mod_cast hlen
    rw [uniformPrefix_squares]
    exact (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hLP hlenR).trans hbase
  · intro k l hgk hgl
    have hpos : 0 < prefixCutValue r q k := hgk
    have hnon : prefixCutValue r q l ≤ 0 := hgl
    have hklen := (prefixCutValue_pos_iff r q k hrq).mp hpos
    have hllen := (prefixCutValue_nonpos_iff r q l hrq).mp hnon
    have hkl : k ≤ l := by change k.val ≤ l.val; omega
    have hql : q ≤ l := by change q.val ≤ l.val; omega
    let i : ℝ := ((k.val+1:ℕ):ℝ)
    let j : ℝ := ((l.val+1:ℕ):ℝ)
    let s : ℝ := j-L
    have hiP : 0 < i := by dsimp [i]; positivity
    have hjP : 0 < j := by dsimp [j]; positivity
    have hLj : L ≤ j := by dsimp [L,R,T,j]; exact_mod_cast hllen
    have hjD : j ≤ (D:ℝ) := by dsimp [j]; exact_mod_cast (show l.val+1 ≤ D by omega)
    have hs0 : 0 ≤ s := sub_nonneg.mpr hLj
    have hsm : s ≤ (m:ℝ) := by dsimp [s]; linarith
    have hh : 0 < prefixCutHeight r q k := by
      rw [prefixCutValue_height r q k hrq] at hpos
      exact (div_pos_iff_of_pos_right hiP).mp hpos
    have hgln : -prefixCutValue r q l=s/j := by
      rw [prefixCutValue_late r q l hrq hql]
      dsimp [s,j,L,R,T]
      ring
    change spectralSquares (cutPair (prefixCutValue r q k) (-prefixCutValue r q l)
      (uniformPrefix k) (uniformPrefix l)) ≤ C
    rw [prefixCutValue_height r q k hrq,hgln]
    rw [uniformPrefix_crossing_purity k l hkl L (prefixCutHeight r q k) s hh hs0 (by dsimp [s,j]; ring)]
    have hb := cutEdgePurity_le_endpoints L (prefixCutHeight r q k) i s m hLP hh hiP.le
      (prefixCutHeight_room r q k hrq) hs0 hsm hmP
    exact hb.trans (max_le hbase (hfull k hpos))

end APPTReview
