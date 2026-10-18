import OperationalCompletion.ReservedFamily
import OperationalCompletion.GridLimit
import MinimaxProfile.PureMinimax

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport SpectralProtocol MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem paperReservationDivisor_pos (m n k : ℕ) (hm : 0<m) (hn : 0<n) :
    0<paperReservationDivisor m n k :=
  reservationDivisor_pos _ _ (gridSectorCount_pos k) (pureSupportRank_pos m n k hm hn)

theorem log_gridSectorCount_div_sqrt :
    Tendsto (fun k : ℕ => Real.log (gridSectorCount k:ℝ)/Real.sqrt k) atTop (nhds 0) := by
  simpa only [gridSectorCount,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Real.log_pow,
    mul_div_assoc,Nat.cast_ofNat,mul_zero] using log_succ_div_sqrt_tendsto_zero.const_mul 2

theorem log_pureSupportRank_div_sqrt (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    Tendsto (fun k : ℕ => Real.log (pureSupportRank m n k:ℝ)/Real.sqrt k) atTop (nhds 0) := by
  have he (k : ℕ) : (symmetricProjector (m*n) k).rank=pureSupportRank m n k :=
    symmetricProjector_rank_choose_complement (m*n) k (Nat.mul_pos hm hn)
  simpa only [he] using symmetric_log_rank_div_sqrt (m*n) (Nat.mul_pos hm hn)

theorem paperReservationDivisor_log (m n k : ℕ) (hm : 0<m) (hn : 0<n) :
    Real.log (paperReservationDivisor m n k:ℝ)=
      Real.log 4+Real.log (gridSectorCount k:ℝ)+Real.log (pureSupportRank m n k:ℝ) := by
  have hJ : (0:ℝ)<gridSectorCount k := Nat.cast_pos.mpr (gridSectorCount_pos k)
  have hr : (0:ℝ)<pureSupportRank m n k := Nat.cast_pos.mpr (pureSupportRank_pos m n k hm hn)
  unfold paperReservationDivisor reservationDivisor
  push_cast
  rw [Real.log_mul (by positivity) (ne_of_gt hr),Real.log_mul (by norm_num) (ne_of_gt hJ)]

theorem paperReservationDivisor_log_div_sqrt (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    Tendsto (fun k : ℕ => Real.log (paperReservationDivisor m n k:ℝ)/Real.sqrt k)
      atTop (nhds 0) := by
  have hc : Tendsto (fun k : ℕ => Real.log 4/Real.sqrt k) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (hc.add log_gridSectorCount_div_sqrt).add (log_pureSupportRank_div_sqrt m n hm hn)
  simpa only [paperReservationDivisor_log m n _ hm hn,add_div,add_zero] using h

theorem div_nat_zero_of_div_sqrt_zero (f : ℕ → ℝ)
    (h : Tendsto (fun k : ℕ => f k/Real.sqrt k) atTop (nhds 0)) :
    Tendsto (fun k : ℕ => f k/k) atTop (nhds 0) := by
  have hh := h.mul (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards with k
  change (f k/Real.sqrt k)/Real.sqrt k=f k/k
  rw [div_div,←pow_two,Real.sq_sqrt (Nat.cast_nonneg k)]

theorem paperReservationDivisor_log_div_nat (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    Tendsto (fun k : ℕ => Real.log (paperReservationDivisor m n k:ℝ)/k) atTop (nhds 0) :=
  div_nat_zero_of_div_sqrt_zero _ (paperReservationDivisor_log_div_sqrt m n hm hn)

theorem nat_div_cap_eventually (m : ℕ) (hm : 0<m) (Q K : ℕ → ℕ)
    (hQ : ∀ k,0<Q k) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hsmall : Tendsto (fun k : ℕ => Real.log (Q k)/k) atTop (nhds 0))
    (hRm : R<Real.log m) : ∀ᶠ k : ℕ in atTop,K k≤m^k/Q k := by
  have hsum := hR.add hsmall
  simp only [add_zero] at hsum
  filter_upwards [hsum.eventually_lt_const hRm,eventually_gt_atTop 0] with k hrate hk
  have hkR : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hKR : (0:ℝ)<K k := Nat.cast_pos.mpr (hK k)
  have hQR : (0:ℝ)<Q k := Nat.cast_pos.mpr (hQ k)
  have hmR : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have hlogs : Real.log ((K k*Q k:ℕ):ℝ)<Real.log ((m^k:ℕ):ℝ) := by
    push_cast
    rw [Real.log_mul (ne_of_gt hKR) (ne_of_gt hQR),Real.log_pow]
    have hh := (div_lt_iff₀ hkR).mp (by simpa only [←add_div] using hrate)
    nlinarith
  have hlt : ((K k*Q k:ℕ):ℝ)<((m^k:ℕ):ℝ) :=
    (Real.log_lt_log_iff (by exact_mod_cast Nat.mul_pos (hK k) (hQ k))
      (by exact_mod_cast Nat.pow_pos hm)).mp hlogs
  exact (Nat.le_div_iff_mul_le (hQ k)).mpr (by exact_mod_cast hlt.le)

theorem reservationCap_eventually (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) (hRm : R<Real.log m) :
    ∀ᶠ k : ℕ in atTop,K k≤reservationLocal m n k m :=
  nat_div_cap_eventually m hm (paperReservationDivisor m n) K
    (fun k => paperReservationDivisor_pos m n k hm hn) hK R hR
    (paperReservationDivisor_log_div_nat m n hm hn) hRm

theorem reservationLocal_eventually_pos (m n : ℕ) (hm : 2≤m) (hn : 0<n) :
    ∀ᶠ k : ℕ in atTop,0<reservationLocal m n k m := by
  have h := reservationCap_eventually m n (by omega) hn (fun _ => 1) (fun _ => by omega)
    0 (by simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0)))
    (Real.log_pos (by exact_mod_cast hm : (1:ℝ)<m))
  exact h.mono (fun k hk => by omega)

theorem reservedLarge_ratio_bounds (a J r : ℕ) (ha : 0<a) (hJ : 0<J) (hr : 0<r) :
    1-(J:ℝ)/reservationDivisor J r≤(reservedLarge a J r:ℝ)/a ∧
      (reservedLarge a J r:ℝ)/a≤1 := by
  have haR : (0:ℝ)<a := Nat.cast_pos.mpr ha
  have hQR : (0:ℝ)<reservationDivisor J r := Nat.cast_pos.mpr (reservationDivisor_pos J r hJ hr)
  have hbudget : (reservedLarge a J r:ℝ)+(J:ℝ)*reservedSmall a J r=a := by
    exact_mod_cast reserved_dimensions_budget a J r hJ hr
  have hmul : (reservationDivisor J r:ℝ)*reservedSmall a J r≤a := by
    exact_mod_cast (Nat.mul_div_le a (reservationDivisor J r))
  have hs : (reservedSmall a J r:ℝ)≤(a:ℝ)/reservationDivisor J r :=
    (le_div_iff₀ hQR).mpr (by nlinarith)
  have hJs := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg J)
  have hd := div_le_div_of_nonneg_right hJs haR.le
  have he : ((J:ℝ)*((a:ℝ)/reservationDivisor J r))/a=(J:ℝ)/reservationDivisor J r := by
    field_simp
  have heL : (reservedLarge a J r:ℝ)/a=1-(J:ℝ)*reservedSmall a J r/a := by
    field_simp
    nlinarith [hbudget]
  constructor
  · rw [heL]
    rw [he] at hd
    linarith
  · exact (div_le_one haR).mpr (by exact_mod_cast Nat.sub_le a (J*reservedSmall a J r))

theorem reservation_fraction_tendsto_zero (m n : ℕ) (hm : 2≤m) (hn : 0<n) :
    Tendsto (fun k : ℕ => (gridSectorCount k:ℝ)/paperReservationDivisor m n k) atTop (nhds 0) := by
  have hmp : 0<m := by omega
  have he (k : ℕ) : (symmetricProjector (m*n) k).rank=pureSupportRank m n k :=
    symmetricProjector_rank_choose_complement (m*n) k (Nat.mul_pos hmp hn)
  have hrank : Tendsto (fun k : ℕ => (pureSupportRank m n k:ℝ)) atTop atTop := by
    simpa only [he] using symmetricProjector_rank_atTop (m*n) (by nlinarith)
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/4:ℝ)) atTop (nhds (1/4))).div_atTop hrank
  apply h.congr'
  filter_upwards with k
  have hJ : (gridSectorCount k:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr (gridSectorCount_pos k))
  have hr : (pureSupportRank m n k:ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr (pureSupportRank_pos m n k hmp hn))
  unfold paperReservationDivisor reservationDivisor
  push_cast
  field_simp

theorem reservationMainLocal_ratio_tendsto_one (m n a : ℕ) (hm : 2≤m) (hn : 0<n) (ha : 0<a) :
    Tendsto (fun k : ℕ => (reservationMainLocal m n k a:ℝ)/(a^k:ℕ)) atTop (nhds 1) := by
  have hlo := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 1)).sub
    (reservation_fraction_tendsto_zero m n hm hn)
  simp only [sub_zero] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
  · intro k
    exact (reservedLarge_ratio_bounds (a^k) (gridSectorCount k) (pureSupportRank m n k)
      (Nat.pow_pos ha) (gridSectorCount_pos k) (pureSupportRank_pos m n k (by omega) hn)).1
  · intro k
    exact (reservedLarge_ratio_bounds (a^k) (gridSectorCount k) (pureSupportRank m n k)
      (Nat.pow_pos ha) (gridSectorCount_pos k) (pureSupportRank_pos m n k (by omega) hn)).2

end
end OperationalCompletion
