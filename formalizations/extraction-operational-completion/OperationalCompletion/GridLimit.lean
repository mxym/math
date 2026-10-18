import OperationalCompletion.GridCutoff

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem log_gridSectorCount_div_nat :
    Tendsto (fun k : ℕ => Real.log (gridSectorCount k:ℝ)/k) atTop (nhds 0) := by
  have h := polynomial_overhead_div_nat_tendsto_zero 0 2
  simpa only [gridSectorCount,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Real.log_pow,
    Nat.cast_ofNat,zero_add] using h

theorem gridCap_eventually (m : ℕ) (hm : 0<m) (K : ℕ → ℕ) (hK : ∀ k,0<K k)
    (R : ℝ) (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRm : R<Real.log m) : ∀ᶠ k : ℕ in atTop,K k≤gridLocalDimension m k := by
  have hsum := hR.add log_gridSectorCount_div_nat
  simp only [add_zero] at hsum
  filter_upwards [hsum.eventually_lt_const hRm,eventually_gt_atTop 0] with k hrate hk
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hKR : (0:ℝ)<K k := by exact_mod_cast hK k
  have hJR : (0:ℝ)<gridSectorCount k := by exact_mod_cast gridSectorCount_pos k
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hlogs : Real.log ((K k*gridSectorCount k:ℕ):ℝ)<Real.log ((m^k:ℕ):ℝ) := by
    push_cast
    rw [Real.log_mul (ne_of_gt hKR) (ne_of_gt hJR),Real.log_pow]
    have hh := (div_lt_iff₀ hkR).mp (by simpa only [←add_div] using hrate)
    nlinarith
  have hlt : ((K k*gridSectorCount k:ℕ):ℝ)<((m^k:ℕ):ℝ) :=
    (Real.log_lt_log_iff (by exact_mod_cast Nat.mul_pos (hK k) (gridSectorCount_pos k))
      (by exact_mod_cast Nat.pow_pos hm)).mp hlogs
  exact (Nat.le_div_iff_mul_le (gridSectorCount_pos k)).mpr (by exact_mod_cast hlt.le)

theorem secondOrder_rate (K : ℕ → ℕ) (C z : ℝ)
    (hsecond : Tendsto (fun k : ℕ => (Real.log (K k)-k*C)/Real.sqrt k)
      atTop (nhds z)) :
    Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds C) := by
  have hi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (hsecond.mul hi).add_const C
  simp only [mul_zero,zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hkR : (k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hk
  have hs : Real.sqrt (k:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk))
  change ((Real.log (K k)-k*C)/Real.sqrt k)/Real.sqrt k+C=Real.log (K k)/k
  rw [div_div,←pow_two,Real.sq_sqrt (Nat.cast_nonneg k)]
  field_simp
  <;> ring

/-- The fixed geometric family works at every target size, including above
the local dimensions; strict subcapacity rates make the first code level exact
in target dimension eventually, without a supplied cap assumption. -/
theorem grid_subcritical_rate (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R))
    (hRm : R<Real.log m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hH : entropy hX.1.isHermitian.eigenvalues<Real.log m+Real.log n-2*R) :
    Tendsto (fun k => (gridProtocol m n k (K k) hm hn hmn (hK k)).fidelity
      (tensorInput m n k X)) atTop (nhds 1) := by
  let p := hX.1.isHermitian.eigenvalues
  have hp : ∀ i,0≤p i := hX.1.eigenvalues_nonneg
  have hs : ∑ i,p i=1 := density_eigenvalues_sum X hX
  have hmass := empiricalEntropyMass_tendsto_one_moving p hp hs
    (fun k => gridSafeCutoff m n k (K k)) _ (gridSafeCutoff_tendsto m n hm hn K hK R hR) hH
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmass tendsto_const_nhds
  · filter_upwards [gridCap_eventually m hm K hK R hR hRm,eventually_gt_atTop 0] with k hcap hk
    exact gridProtocol_safe_mass m n k (K k) hm hn hmn (hK k) hk hcap X hX
  · exact Eventually.of_forall (fun k =>
      ((gridProtocol m n k (K k) hm hn hmn (hK k)).fidelity_bounds (hK k) _
        (tensorInput_density m n k X hX)).2)

end
end OperationalCompletion
