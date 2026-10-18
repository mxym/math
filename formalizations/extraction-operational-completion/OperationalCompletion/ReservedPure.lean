import OperationalCompletion.ReservationLimit

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport SpectralProtocol MinimaxProfile Filter
namespace OperationalCompletion
noncomputable section

theorem reservationMainLocal_le (m n k a : ℕ) : reservationMainLocal m n k a≤a^k :=
  Nat.sub_le _ _

theorem reservationMainLocal_pos (m n k a : ℕ) (hm : 0<m) (hn : 0<n) (ha : 0<a) :
    0<reservationMainLocal m n k a := by
  change 0<reservedLarge (a^k) (gridSectorCount k) (pureSupportRank m n k)
  by_cases hs : 0<reservedSmall (a^k) (gridSectorCount k) (pureSupportRank m n k)
  · exact reservedLarge_pos _ _ _ (gridSectorCount_pos k) (pureSupportRank_pos m n k hm hn) hs
  · have hz : reservedSmall (a^k) (gridSectorCount k) (pureSupportRank m n k)=0 := by omega
    simpa only [reservedLarge,hz,mul_zero,Nat.sub_zero] using Nat.pow_pos ha (n:=k)

theorem balanced_reserved_rank_budget (m k : ℕ) (hm : 0<m) :
    pureSupportRank m m k≤reservationMainLocal m m k m*reservationMainLocal m m k m := by
  by_cases hs : 0<reservedSmall (m^k) (gridSectorCount k) (pureSupportRank m m k)
  · exact reserved_rank_le_product (m^k) (m^k) _ _ (gridSectorCount_pos k)
      (pureSupportRank_pos m m k hm hm) le_rfl hs
  · have hz : reservedSmall (m^k) (gridSectorCount k) (pureSupportRank m m k)=0 := by omega
    change pureSupportRank m m k≤reservedLarge _ _ _*reservedLarge _ _ _
    simp only [reservedLarge,hz,mul_zero,Nat.sub_zero]
    simpa only [mul_pow] using pureSupportRank_le_dimension m m k hm hm

def balancedReservationPacking (m k : ℕ) (hm : 0<m) : ℕ :=
  packingDimension (reservationMainLocal m m k m) (reservationMainLocal m m k m)
    (pureSupportRank m m k) (reservationMainLocal_pos m m k m hm hm hm)
    (balanced_reserved_rank_budget m k hm)

theorem balancedReservationPacking_eq_paper (m k : ℕ) (hm : 0<m)
    (ha : 0<reservationLocal m m k m) :
    balancedReservationPacking m k hm=paperReservedPacking m m k hm hm le_rfl ha := by
  rfl

def balancedReservedWidth (m k : ℕ) : ℝ :=
  (reservationMainLocal m m k m:ℝ)/Real.sqrt (pureSupportRank m m k:ℝ)

theorem balancedReservedWidth_pos (m k : ℕ) (hm : 0<m) : 0<balancedReservedWidth m k :=
  div_pos (Nat.cast_pos.mpr (reservationMainLocal_pos m m k m hm hm hm))
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (pureSupportRank_pos m m k hm hm)))

theorem balancedReservedWidth_budget (m k : ℕ) (hm : 0<m) :
    (pureSupportRank m m k:ℝ)*balancedReservedWidth m k^2=
      (reservationMainLocal m m k m:ℝ)*(reservationMainLocal m m k m:ℝ) := by
  have hr : (0:ℝ)<pureSupportRank m m k := Nat.cast_pos.mpr (pureSupportRank_pos m m k hm hm)
  rw [balancedReservedWidth,div_pow,Real.sq_sqrt hr.le]
  field_simp
  <;> ring

theorem balancedReservedWidth_ratio (m k : ℕ) (hm : 0<m) :
    balancedReservedWidth m k/balancedWidth m k=
      (reservationMainLocal m m k m:ℝ)/(m^k:ℕ) := by
  have hpow : (m:ℝ)^k≠0 := ne_of_gt (pow_pos (Nat.cast_pos.mpr hm) k)
  have hs : Real.sqrt (pureSupportRank m m k:ℝ)≠0 := ne_of_gt
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (pureSupportRank_pos m m k hm hm)))
  unfold balancedReservedWidth balancedWidth
  push_cast
  field_simp

theorem balancedReservedWidth_atTop (m : ℕ) (hm : 2≤m) :
    Tendsto (balancedReservedWidth m) atTop atTop := by
  have hratio := reservationMainLocal_ratio_tendsto_one m m m hm (by omega) (by omega)
  have h := Tendsto.pos_mul_atTop (by norm_num : (0:ℝ)<1) hratio (balancedWidth_atTop m hm)
  apply h.congr'
  filter_upwards with k
  have hw := balancedWidth_pos m k (by omega)
  have he := balancedReservedWidth_ratio m k (by omega)
  exact ((div_eq_iff hw.ne').mp he).symm

theorem balancedReservedWidth_div_local_tendsto_zero (m : ℕ) (hm : 2≤m) :
    Tendsto (fun k => balancedReservedWidth m k/(reservationMainLocal m m k m:ℝ))
      atTop (nhds 0) := by
  apply (balancedWidth_div_local_tendsto_zero m hm).congr'
  filter_upwards with k
  have hA : (reservationMainLocal m m k m:ℝ)≠0 :=
    ne_of_gt (Nat.cast_pos.mpr (reservationMainLocal_pos m m k m (by omega) (by omega) (by omega)))
  have hpow : (m:ℝ)^k≠0 := ne_of_gt (pow_pos (Nat.cast_pos.mpr (show 0<m by omega)) k)
  unfold balancedReservedWidth balancedWidth
  push_cast
  field_simp

theorem balancedReservationPacking_ratio_tendsto_one (m : ℕ) (hm : 2≤m) :
    Tendsto (fun k => (balancedReservationPacking m k (by omega):ℝ)/balancedWidth m k)
      atTop (nhds 1) := by
  have hp := packing_ratio_tendsto
    (a := fun k => reservationMainLocal m m k m) (b := fun k => reservationMainLocal m m k m)
    (r := pureSupportRank m m) (w := balancedReservedWidth m)
    (fun k => reservationMainLocal_pos m m k m (by omega) (by omega) (by omega))
    (fun k => reservationMainLocal_pos m m k m (by omega) (by omega) (by omega))
    (fun k => pureSupportRank_pos m m k (by omega) (by omega))
    (fun k => balanced_reserved_rank_budget m k (by omega))
    (fun k => balancedReservedWidth_pos m k (by omega))
    (fun k => balancedReservedWidth_budget m k (by omega))
    (balancedReservedWidth_atTop m hm) (balancedReservedWidth_div_local_tendsto_zero m hm)
    (balancedReservedWidth_div_local_tendsto_zero m hm)
  have hw := reservationMainLocal_ratio_tendsto_one m m m hm (by omega) (by omega)
  have h := hp.mul hw
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards with k
  change (balancedReservationPacking m k (by omega):ℝ)/balancedReservedWidth m k*
    ((reservationMainLocal m m k m:ℝ)/(m^k:ℕ))=_
  rw [←balancedReservedWidth_ratio m k (by omega)]
  have hs := ne_of_gt (balancedReservedWidth_pos m k (by omega))
  have hw := ne_of_gt (balancedWidth_pos m k (by omega))
  field_simp

theorem balancedReservationPacking_le_width (m k : ℕ) (hm : 0<m) :
    (balancedReservationPacking m k hm:ℝ)≤balancedWidth m k := by
  have hprops := packingDimension_properties (reservationMainLocal_pos m m k m hm hm hm)
    (balanced_reserved_rank_budget m k hm)
  have hdiv : reservationMainLocal m m k m/balancedReservationPacking m k hm≤
      m^k/balancedReservationPacking m k hm := Nat.div_le_div_right (reservationMainLocal_le m m k m)
  have hbudget : pureSupportRank m m k≤
      (m^k/balancedReservationPacking m k hm)*(m^k/balancedReservationPacking m k hm) :=
    hprops.2.2.trans (Nat.mul_le_mul hdiv hdiv)
  exact feasible_dimension_real_bound (pureSupportRank_pos m m k hm hm)
    (balancedWidth_pos m k hm).le (balancedWidth_budget m k hm) hbudget

/-- One already fixed family, uniform in every integer target and the entire
unknown pure-input continuum, attains the sharp balanced minimax profile. -/
theorem balanced_reserved_family_sharp (m : ℕ) (hm : 2≤m) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ K : ℕ,∀ hK : 0<K,
      (∀ z : Fin (m*m) → ℂ,IsUnitVector z →
        (1-ε)*profile (balancedWidth m k) K≤
          (reservedProtocol m m k K (by omega) (by omega) le_rfl hK).fidelity (purePowerInput m m k z)) ∧
      (∀ V : KrausPPTProtocol (m^k) (m^k) K,∀ c : ℝ,
        (∀ z : Fin (m*m) → ℂ,IsUnitVector z → c≤V.fidelity (purePowerInput m m k z)) →
          c≤profile (balancedWidth m k) K) := by
  have hm0 : 0<m := by omega
  have hratio := (balancedReservationPacking_ratio_tendsto_one m hm).eventually_const_lt
    (show 1-ε<(1:ℝ) by linarith)
  filter_upwards [hratio,reservationLocal_eventually_pos m m hm hm0,eventually_gt_atTop 0]
    with k hratio ha hk
  intro K hK
  constructor
  · intro z hz
    have hY := purePowerInput_density m m k z hz
    have h := (reservedProtocol_guarantees m m k K hm0 hm0 le_rfl hK hk ha).2
      (purePowerInput m m k z) hY.1 (purePowerInput_supported m m k z)
    have ht : (purePowerInput m m k z).trace.re=1 := by rw [hY.2]; rfl
    rw [ht,mul_one,←balancedReservationPacking_eq_paper m k hm0 ha] at h
    have hlo := profile_scale_lower (Nat.cast_nonneg (balancedReservationPacking m k hm0))
      (balancedReservationPacking_le_width m k hm0) (balancedWidth_pos m k hm0) (Nat.cast_pos.mpr hK)
    exact (mul_le_mul_of_nonneg_right hratio.le
      (profile_pos (balancedWidth_pos m k hm0) (Nat.cast_pos.mpr hK)).le).trans (hlo.trans h)
  · intro V c hc
    have h := purePower_fidelity_guarantee_upper m m k K hm0 hm0 hK
      V.A V.complete V.ptPositive V.U c hc
    exact h.trans_eq (balancedUpper_eq_profile m k K hm0 hK)

end
end OperationalCompletion
