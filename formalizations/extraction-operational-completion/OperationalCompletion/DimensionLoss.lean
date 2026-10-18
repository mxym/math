import OperationalCompletion.ReservedTriangular

open scoped BigOperators ComplexOrder Topology
open Matrix SpectralProtocol SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

theorem pureSupportRank_log_le (m n k : ℕ) (hm : 0<m) (hn : 0<n) :
    Real.log (pureSupportRank m n k:ℝ)≤((m*n-1:ℕ):ℝ)*Real.log (k+m*n) := by
  have hr : (0:ℝ)<pureSupportRank m n k := Nat.cast_pos.mpr (pureSupportRank_pos m n k hm hn)
  have hu : pureSupportRank m n k≤(k+m*n)^(m*n-1) := by
    unfold pureSupportRank
    exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hh := Real.log_le_log hr (show (pureSupportRank m n k:ℝ)≤((k+m*n:ℕ):ℝ)^(m*n-1) by exact_mod_cast hu)
  rw [Real.log_pow] at hh
  simpa only [Nat.cast_add,Nat.cast_mul] using hh

/-- All actual compression and pure-reservation overhead is bounded by an
explicit dimension expression; no unspecified polynomial constant remains. -/
theorem reservedTotalLoss_dimension_bound (m n k : ℕ) (hm : 0<m) (hn : 0<n)
    (hD : 2≤m*n) (hk : 0<k) :
    reservedTotalLoss m n k≤10*((m*n:ℕ):ℝ)^2*Real.log (k+m*n) := by
  let D := m*n
  let L := Real.log (k+D)
  have hDp : 0<D := Nat.mul_pos hm hn
  have hD1 : 1≤D := hDp
  have hDsq : 1≤D*D := Nat.mul_pos hDp hDp
  have hDR : (2:ℝ)≤D := by exact_mod_cast hD
  have hL : 0≤L := Real.log_nonneg (by exact_mod_cast (show 1≤k+D by omega))
  have hl1 : Real.log (k+1)≤L := by
    apply Real.log_le_log (by exact_mod_cast (show 0<k+1 by omega))
    exact_mod_cast (show k+1≤k+D by omega)
  have hl2 : Real.log (k+D*D)≤2*L := by
    have hh : (k+D*D:ℕ)≤(k+D)^2 := by nlinarith
    have hb := Real.log_le_log (by exact_mod_cast (show 0<k+D*D by omega))
      (show ((k+D*D:ℕ):ℝ)≤((k+D:ℕ):ℝ)^2 by exact_mod_cast hh)
    simpa only [Real.log_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_mul,L] using hb
  have hl4 : Real.log 4≤2*L := by
    have hh : (4:ℝ)≤((k+D:ℕ):ℝ)^2 := by
      have hkd : (2:ℝ)≤(k+D:ℕ) := by exact_mod_cast (show 2≤k+D by omega)
      nlinarith
    have hb := Real.log_le_log (by norm_num : (0:ℝ)<4) hh
    simpa only [Real.log_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_mul,L] using hb
  have hpure := pureSupportRank_log_le m n k hm hn
  have hc := compressionLoss_le D k hDp
  have hres : reservationLoss m n k = 3*Real.log 4+4*Real.log (k+1)+
      2*Real.log (pureSupportRank m n k:ℝ) := by
    rw [reservationLoss_expansion m n k hm hn,paperReservationDivisor_log m n k hm hn]
    simp only [gridSectorCount,Nat.cast_pow,Real.log_pow,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
    ring
  have hcoeff : (2*(D:ℝ)^2+3*D+8)≤10*(D:ℝ)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff hL
  have hc2 := mul_le_mul_of_nonneg_left hl2 (show 0≤((D*D-1:ℕ):ℝ) by positivity)
  have hc1 := mul_le_mul_of_nonneg_left hl1 (Nat.cast_nonneg D)
  rw [Nat.cast_sub hDsq,Nat.cast_mul,Nat.cast_one] at hc hc2
  rw [Nat.cast_sub hD1,Nat.cast_one] at hpure
  unfold reservedTotalLoss
  rw [hres]
  dsimp [L,D] at *
  push_cast at *
  nlinarith

def dimensionScale (D k : ℕ) : ℝ :=
  (D:ℝ)^2*Real.log ((k:ℝ)+D)/Real.sqrt ((k:ℝ)/D)

theorem dimensionScale_nonneg (D k : ℕ) (hD : 0<D) : 0≤dimensionScale D k := by
  unfold dimensionScale
  apply div_nonneg _ (Real.sqrt_nonneg _)
  exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1≤k+D by omega)))

theorem dimensionScale_sq (D k : ℕ) (hD : 0<D) :
    (dimensionScale D k)^2=(D:ℝ)^5*(Real.log ((k:ℝ)+D))^2/k := by
  by_cases hk : k=0
  · subst k; simp [dimensionScale]
  have hDR : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk
  unfold dimensionScale
  rw [div_pow,Real.sq_sqrt (div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg D))]
  field_simp
  <;> ring

theorem dimensionScale_tendsto (D : ℕ → ℕ) (hD : ∀ k,0<D k)
    (hDim : Tendsto (fun k : ℕ => (D k:ℝ)^5*(Real.log ((k:ℝ)+D k))^2/k)
      atTop (nhds 0)) : Tendsto (fun k => dimensionScale (D k) k) atTop (nhds 0) := by
  have hh := hDim.sqrt
  simp only [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards with k
  rw [←dimensionScale_sq _ _ (hD k),Real.sqrt_sq (dimensionScale_nonneg _ _ (hD k))]

theorem sqrt_block_div_dimension_tendsto (D : ℕ → ℕ) (hD : ∀ k,2≤D k)
    (hScale : Tendsto (fun k => dimensionScale (D k) k) atTop (nhds 0)) :
    Tendsto (fun k : ℕ => Real.sqrt ((k:ℝ)/D k)) atTop atTop := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  apply tendsto_atTop.mpr
  intro b
  let B := max 1 b
  have hB : 0<B := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)
  filter_upwards [hScale.eventually_lt_const (show (0:ℝ)<Real.log 2/B from div_pos hl hB),
    eventually_gt_atTop 0] with k hs hk
  have hDR : (2:ℝ)≤D k := by exact_mod_cast hD k
  have hspos : 0<Real.sqrt ((k:ℝ)/D k) := Real.sqrt_pos.mpr (by positivity)
  have hlog : Real.log 2≤Real.log ((k:ℝ)+D k) :=
    Real.log_le_log (by norm_num) (by nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k])
  have hnum : Real.log 2≤(D k:ℝ)^2*Real.log ((k:ℝ)+D k) := by
    nlinarith [mul_nonneg (show 0≤(D k:ℝ)^2-1 by nlinarith) (hl.le.trans hlog)]
  have hb : B≤Real.sqrt ((k:ℝ)/D k) := by
    by_contra hh
    have hb' : Real.sqrt ((k:ℝ)/D k)≤B := (lt_of_not_ge hh).le
    have hlow : Real.log 2/B≤dimensionScale (D k) k := by
      unfold dimensionScale
      apply (div_le_div_iff₀ hB hspos).mpr
      nlinarith
    exact (not_lt_of_ge hlow) hs
  exact (le_max_right 1 b).trans hb

end
end OperationalCompletion
