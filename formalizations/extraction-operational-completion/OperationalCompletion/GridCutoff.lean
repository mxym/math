import OperationalCompletion.GridFamily

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

theorem sourceCutoff_div_lower (D k a b d J : ℕ) (hd : 0<d) (hJ : 0<J)
    (hJa : J≤a) (hJb : J≤b) :
    sourceCutoff D k a b d-Real.log (4*(J:ℝ)^2)/k ≤
      sourceCutoff D k (a/J) (b/J) d := by
  have ha : 0<a := hJ.trans_le hJa
  have hb : 0<b := hJ.trans_le hJb
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hJR : (0:ℝ)<J := by exact_mod_cast hJ
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hprod := quarter_capacity_lower a b J hJ hJa hJb
  have hprod' : (a:ℝ)*b/(4*(J:ℝ)^2) ≤ ((a/J:ℕ):ℝ)*((b/J:ℕ):ℝ) := by
    simpa only [Nat.cast_mul] using hprod
  have hquot : ((a:ℝ)*b/(4*(d:ℝ)^2))/(4*(J:ℝ)^2) ≤
      ((a/J:ℕ):ℝ)*((b/J:ℕ):ℝ)/(4*(d:ℝ)^2) := by
    have hh := div_le_div_of_nonneg_right hprod' (show (0:ℝ)≤4*(d:ℝ)^2 by positivity)
    convert hh using 1 <;> ring
  have hlog : Real.log ((a:ℝ)*b/(4*(d:ℝ)^2))-Real.log (4*(J:ℝ)^2) ≤
      Real.log (((a/J:ℕ):ℝ)*((b/J:ℕ):ℝ)/(4*(d:ℝ)^2)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) hquot
  unfold sourceCutoff
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  linarith

def gridLoss (k : ℕ) : ℝ := Real.log (4*(gridSectorCount k:ℝ)^2)

def gridSafeCutoff (m n k K : ℕ) : ℝ := compressionCutoff m n k K-gridLoss k/k

theorem gridSafeCutoff_le_source (m n k K : ℕ) (hK : 0<K)
    (ha : gridSectorCount k≤m^k) (hb : gridSectorCount k≤n^k) :
    gridSafeCutoff m n k K ≤
      sourceCutoff (m*n) k (gridLocalDimension m k) (gridLocalDimension n k) K := by
  exact sourceCutoff_div_lower (m*n) k (m^k) (n^k) K (gridSectorCount k)
    hK (gridSectorCount_pos k) ha hb

theorem gridProtocol_safe_mass (m n k K : ℕ) (hm : 0<m) (hn : 0<n)
    (hmn : m≤n) (hK : 0<K) (hk : 0<k) (hKa : K≤gridLocalDimension m k)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    empiricalEntropyMass hX.1.isHermitian.eigenvalues k (gridSafeCutoff m n k K) ≤
      (gridProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X) := by
  have ha : gridSectorCount k≤m^k := by
    have hpositive : 1≤m^k/gridSectorCount k := by
      change 1≤gridLocalDimension m k
      omega
    have hmul := (Nat.le_div_iff_mul_le (gridSectorCount_pos k)).mp hpositive
    omega
  have hb : gridSectorCount k≤n^k := ha.trans (Nat.pow_le_pow_left hmn k)
  exact (empiricalEntropyMass_mono _ hX.1.eigenvalues_nonneg k
    (gridSafeCutoff_le_source m n k K hK ha hb)).trans
    (gridProtocol_first_mass m n k K hm hn hmn hK hk hKa X hX)

theorem gridLoss_expansion (k : ℕ) : gridLoss k=Real.log 4+4*Real.log ((k:ℝ)+1) := by
  unfold gridLoss gridSectorCount
  push_cast
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
  ring

theorem gridLoss_div_sqrt_tendsto_zero :
    Tendsto (fun k : ℕ => gridLoss k/Real.sqrt k) atTop (nhds 0) := by
  have hc : Tendsto (fun k : ℕ => Real.log 4/Real.sqrt k) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := hc.add (log_succ_div_sqrt_tendsto_zero.const_mul 4)
  simpa only [gridLoss_expansion,add_div,mul_div_assoc,mul_zero,add_zero] using h

theorem gridLoss_div_nat_tendsto_zero :
    Tendsto (fun k : ℕ => gridLoss k/k) atTop (nhds 0) := by
  have h := gridLoss_div_sqrt_tendsto_zero.mul
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards with k
  change (gridLoss k/Real.sqrt k)/Real.sqrt k=gridLoss k/k
  rw [div_div,←pow_two,Real.sq_sqrt (Nat.cast_nonneg k)]

theorem gridSafeCutoff_tendsto (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (R : ℝ)
    (hR : Tendsto (fun k : ℕ => Real.log (K k)/k) atTop (nhds R)) :
    Tendsto (fun k => gridSafeCutoff m n k (K k)) atTop
      (nhds (Real.log m+Real.log n-2*R)) := by
  simpa only [gridSafeCutoff,sub_zero] using
    (compressionCutoff_tendsto m n hm hn K hK R hR).sub gridLoss_div_nat_tendsto_zero

theorem gridSafeCutoff_gaussian (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (K : ℕ → ℕ) (hK : ∀ k,0<K k) (H z : ℝ)
    (hsecond : Tendsto (fun k : ℕ =>
      (Real.log (K k)-k*((Real.log m+Real.log n-H)/2))/Real.sqrt k) atTop (nhds z)) :
    Tendsto (fun k : ℕ => (k*gridSafeCutoff m n k (K k)-k*H)/Real.sqrt k)
      atTop (nhds (-2*z)) := by
  have h := (compressionCutoff_gaussian m n hm hn K hK H z hsecond).sub
    gridLoss_div_sqrt_tendsto_zero
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with k hk
  unfold gridSafeCutoff
  have hkR : (k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hk
  field_simp
  <;> ring

end
end OperationalCompletion
