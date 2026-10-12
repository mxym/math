import APPTReview.RectangularSpectrumVector

open scoped BigOperators
namespace APPTReview

/-- Equality among full-support cut vertices fixes the middle prefix rank. -/
theorem full_prefix_edge_maximizer {D m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    (hD : D=m*n) (r q : Fin D) (hrq : r ≤ q)
    (hr : 2*(r.val+1)+m=m*m) (hL : (r.val+1)+(q.val+1)+m=D)
    (hcutoff : m^3-m-2 ≤ n) (k : Fin D) (hg : 0 < prefixCutValue r q k) :
    let L : ℝ := ((r.val+1:ℕ):ℝ)+((q.val+1:ℕ):ℝ)
    cutEdgePurity L (prefixCutHeight r q k) ((k.val+1:ℕ):ℝ) m ≤ roundedPlateauPurity m n ∧
    (cutEdgePurity L (prefixCutHeight r q k) ((k.val+1:ℕ):ℝ) m=roundedPlateauPurity m n →
      r < k ∧ k ≤ q ∧ k.val+1=((m-1)*n+1)/2) := by
  dsimp only
  let R : ℝ := ((r.val+1:ℕ):ℝ)
  let T : ℝ := ((q.val+1:ℕ):ℝ)
  let L : ℝ := R+T
  have hRP : 0 < R := by dsimp [R]; positivity
  have hTP : 0 < T := by dsimp [T]; positivity
  have hLP : 0 < L := add_pos hRP hTP
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
  have hstrict := outerSpike_lt_roundedPlateau hm hmn hcutoff
  have hbase : 1/L < roundedPlateauPurity m n := by
    rw [hLR]
    exact (outerSpike_dominates_uniform hm hmn).trans_lt hstrict
  have hi : (1:ℝ) ≤ ((k.val+1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ k.val+1 by omega)
  change cutEdgePurity L (prefixCutHeight r q k) ((k.val+1:ℕ):ℝ) m ≤ roundedPlateauPurity m n ∧ _
  by_cases hkr : k ≤ r
  · rw [show prefixCutHeight r q k=((k.val+1:ℕ):ℝ) by simp [prefixCutHeight,hkr]]
    have hu := cutEdge_early_full_bound L ((k.val+1:ℕ):ℝ) m hLP hi hmP.le
    have he : (L+3*(m:ℝ)+(m:ℝ)^2)/(L+2*(m:ℝ))^2=outerSpikePurity m n := by
      rw [hLR]
      unfold outerSpikePurity
      congr 1 <;> ring
    have hlt := (hu.trans_eq he).trans_lt hstrict
    exact ⟨hlt.le,fun heq => (ne_of_lt hlt heq).elim⟩
  · by_cases hkq : k ≤ q
    · rw [show prefixCutHeight r q k=R by simp [prefixCutHeight,hkr,hkq,R],hRR,hLR]
      refine ⟨cutEdge_middle_le_rounded (by omega) hnP (k.val+1),?_⟩
      intro he
      change cutEdgePurity L ((m:ℝ)*((m:ℝ)-1)/2) ((k.val+1:ℕ):ℝ) m=roundedPlateauPurity m n at he
      rw [hLR] at he
      exact ⟨lt_of_not_ge hkr,hkq,(cutEdge_middle_eq_rounded_iff (by omega) hnP (k.val+1)).mp he⟩
    · have hiL : ((k.val+1:ℕ):ℝ) < L := by
        have he := (prefixCutValue_pos_iff r q k hrq).mp hg
        dsimp [L,R,T]
        exact_mod_cast he
      rw [show prefixCutHeight r q k=L-((k.val+1:ℕ):ℝ) by simp [prefixCutHeight,hkr,hkq,L,R,T]]
      have hlt := (cutEdge_late_bound L ((k.val+1:ℕ):ℝ) m hLP (by positivity) hiL hmP.le).trans_lt hbase
      exact ⟨hlt.le,fun heq => (ne_of_lt hlt heq).elim⟩

/-- All equality cases of the ordered halfspace relaxation, without a spectral ansatz. -/
theorem ordered_rectangular_cut_unique_spectrum {D m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    (hD : D=m*n) (r q : Fin D) (hrq : r ≤ q)
    (hr : 2*(r.val+1)+m=m*m) (hL : (r.val+1)+(q.val+1)+m=D)
    (hcutoff : m^3-m-2 ≤ n)
    (f : Fin D → ℝ) (hf : Antitone f) (hn : ∀ i, 0 ≤ f i) (hs : (∑ i,f i)=1)
    (hcut : (∑ i,prefixCut r q i*f i) ≤ 0) :
    spectralSquares f ≤ roundedPlateauPurity m n ∧
      (spectralSquares f=roundedPlateauPurity m n → f=roundedPlateauSpectrum m n) := by
  let R : ℝ := ((r.val+1:ℕ):ℝ)
  let T : ℝ := ((q.val+1:ℕ):ℝ)
  let L : ℝ := R+T
  let C := roundedPlateauPurity m n
  have hRP : 0 < R := by dsimp [R]; positivity
  have hTP : 0 < T := by dsimp [T]; positivity
  have hLP : 0 < L := add_pos hRP hTP
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmP : (0:ℝ) < m := by linarith
  have hDR : (D:ℝ)=(m:ℝ)*n := by exact_mod_cast hD
  have hLR : L=(m:ℝ)*n-m := by
    have he : R+T+(m:ℝ)=(D:ℝ) := by dsimp [R,T]; exact_mod_cast hL
    dsimp [L]
    linarith
  have hRR : R=(m:ℝ)*((m:ℝ)-1)/2 := by
    have he : 2*R+(m:ℝ)=(m:ℝ)*(m:ℝ) := by dsimp [R]; exact_mod_cast hr
    nlinarith
  have hbase : 1/L < C := by
    rw [hLR]
    exact (outerSpike_dominates_uniform hm hmn).trans_lt (outerSpike_lt_roundedPlateau hm hmn hcutoff)
  apply ordered_spectrum_cut_unique f (prefixCut r q) (roundedPlateauSpectrum m n) C hf hn hs hcut
  · intro k hg
    have hlen := (prefixCutValue_nonpos_iff r q k hrq).mp hg
    have hlenR : L ≤ ((k.val+1:ℕ):ℝ) := by dsimp [L,R,T]; exact_mod_cast hlen
    have hlt : spectralSquares (uniformPrefix k) < C := by
      rw [uniformPrefix_squares]
      exact (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hLP hlenR).trans_lt hbase
    exact ⟨hlt.le,fun he => (ne_of_lt hlt he).elim⟩
  · intro k l hgk hgl
    dsimp only
    let v := cutPair (prefixCutValue r q k) (-prefixCutValue r q l) (uniformPrefix k) (uniformPrefix l)
    change spectralSquares v ≤ C ∧ (spectralSquares v=C → v=roundedPlateauSpectrum m n)
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
    have hvalue : spectralSquares v=cutEdgePurity L (prefixCutHeight r q k) i s := by
      dsimp only [v]
      rw [prefixCutValue_height r q k hrq,hgln]
      exact uniformPrefix_crossing_purity k l hkl L (prefixCutHeight r q k) s hh hs0 (by dsimp [s,j]; ring)
    have hfull := full_prefix_edge_maximizer hm hmn hD r q hrq hr hL hcutoff k hpos
    dsimp only at hfull
    have hb := cutEdgePurity_le_endpoints L (prefixCutHeight r q k) i s m hLP hh hiP.le
      (prefixCutHeight_room r q k hrq) hs0 hsm hmP
    refine ⟨hvalue.le.trans (hb.trans (max_le hbase.le hfull.1)),?_⟩
    intro heq
    have hE : cutEdgePurity L (prefixCutHeight r q k) i s=C := hvalue.symm.trans heq
    have hsmeq : s=(m:ℝ) := by
      apply le_antisymm hsm
      by_contra hbad
      have hlt := cutEdgePurity_lt_of_short L (prefixCutHeight r q k) i s m C
        hLP hh hiP.le (prefixCutHeight_room r q k hrq) hs0 (lt_of_not_ge hbad) hmP hbase hfull.1
      exact ne_of_lt hlt hE
    have hEfull : cutEdgePurity L (prefixCutHeight r q k) i m=C := by simpa only [hsmeq] using hE
    have hinfo := hfull.2 hEfull
    have hjDR : j=(D:ℝ) := by dsimp only [s] at hsmeq; linarith
    have hlD : l.val+1=D := by
      have hc : (((l.val+1:ℕ):ℝ))=(D:ℝ) := hjDR
      exact_mod_cast hc
    dsimp only [v]
    rw [prefixCutValue_middle r q k (le_of_lt hinfo.1) hinfo.2.1,hgln]
    change cutPair (R/i) (s/j) (uniformPrefix k) (uniformPrefix l)=_
    rw [hRR,hsmeq,hjDR]
    exact full_middle_crossing_spectrum (by omega) hD k l hinfo.2.2 hlD

end APPTReview
