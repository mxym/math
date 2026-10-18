import OperationalCompletion.DimensionLoss

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

theorem law_varentropy_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i,0≤p i) :
    0≤varentropy p := by
  unfold varentropy finiteVariance
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))

theorem variance_normalization_lower (D k : ℕ) (hD : 0<D)
    (V c : ℝ) (hc : 0<c) (hV : c≤(D:ℝ)*V) :
    Real.sqrt c*Real.sqrt ((k:ℝ)/D)≤Real.sqrt ((k:ℝ)*V) := by
  rw [←Real.sqrt_mul hc.le]
  apply Real.sqrt_le_sqrt
  have hf : c/(D:ℝ)≤V := (div_le_iff₀ (Nat.cast_pos.mpr hD)).mpr (by nlinarith)
  convert mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg k) using 1 <;> ring

theorem lyapunov_shrinking_bound (D k : ℕ) (hD : 0<D) (hk : 0<k)
    (T V c C : ℝ) (hT0 : 0≤T) (hV0 : 0<V) (hc : 0<c) (hC : 0≤C)
    (hV : c≤(D:ℝ)*V) (hT : (D:ℝ)*T≤C) :
    T/(V^(3/2:ℝ)*Real.sqrt k)≤(C/(c*Real.sqrt c))/Real.sqrt ((k:ℝ)/D) := by
  have hbase : 0<Real.sqrt ((k:ℝ)/D) := Real.sqrt_pos.mpr (by positivity)
  have hpow : V^(3/2:ℝ)=V*Real.sqrt V := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hV0,Real.rpow_one,←Real.sqrt_eq_rpow]
  have heq : V^(3/2:ℝ)*Real.sqrt k=V*Real.sqrt ((k:ℝ)*V) := by
    rw [hpow,Real.sqrt_mul (Nat.cast_nonneg k)]
    ring
  have hratio : T/V≤C/c := by
    apply (div_le_div_iff₀ hV0 hc).mpr
    have h1 := mul_le_mul_of_nonneg_left hV hT0
    have h2 := mul_le_mul_of_nonneg_right hT hV0.le
    nlinarith
  rw [heq,←div_div]
  calc
    _ ≤ (C/c)/Real.sqrt ((k:ℝ)*V) := div_le_div_of_nonneg_right hratio (Real.sqrt_nonneg _)
    _ ≤ (C/c)/(Real.sqrt c*Real.sqrt ((k:ℝ)/D)) :=
      div_le_div_of_nonneg_left (div_nonneg hC hc.le) (by positivity)
        (variance_normalization_lower D k hD V c hc hV)
    _ = _ := by rw [div_div]; ring

/-- The concrete D^5 log^2(k+D)=o(k) budget implies all three numerical
conditions, even when the actual variance decreases like 1/D. -/
theorem shrinking_variance_numerical_conditions (D : ℕ → ℕ) (hD : ∀ k,2≤D k)
    (T V L : ℕ → ℝ) (hT0 : ∀ k,0≤T k) (hV0 : ∀ k,0≤V k) (hL0 : ∀ k,0≤L k)
    (c C : ℝ) (hc : 0<c) (hC : 0≤C)
    (hV : ∀ᶠ k : ℕ in atTop,c≤(D k:ℝ)*V k)
    (hT : ∀ᶠ k : ℕ in atTop,(D k:ℝ)*T k≤C)
    (hL : ∀ᶠ k : ℕ in atTop,L k≤10*(D k:ℝ)^2*Real.log ((k:ℝ)+D k))
    (hDim : Tendsto (fun k : ℕ => (D k:ℝ)^5*(Real.log ((k:ℝ)+D k))^2/k)
      atTop (nhds 0)) :
    Tendsto (fun k : ℕ => T k/((V k)^(3/2:ℝ)*Real.sqrt k)) atTop (nhds 0) ∧
    Tendsto (fun k : ℕ => Real.sqrt ((k:ℝ)*V k)) atTop atTop ∧
    Tendsto (fun k : ℕ => L k/Real.sqrt ((k:ℝ)*V k)) atTop (nhds 0) := by
  have hDp : ∀ k,0<D k := fun k => by have := hD k; omega
  have hScale := dimensionScale_tendsto D hDp hDim
  have hbase := sqrt_block_div_dimension_tendsto D hD hScale
  have hsigma : Tendsto (fun k : ℕ => Real.sqrt ((k:ℝ)*V k)) atTop atTop := by
    have hb := hbase.atTop_mul_const (Real.sqrt_pos.mpr hc)
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hb.eventually (eventually_ge_atTop b),hV] with k hk hVk
    exact hk.trans (by simpa only [mul_comm] using variance_normalization_lower (D k) k (hDp k) (V k) c hc hVk)
  refine ⟨?_,hsigma,?_⟩
  · have hb := (tendsto_inv_atTop_zero.comp hbase).const_mul (C/(c*Real.sqrt c))
    simp only [mul_zero] at hb
    apply squeeze_zero' (Eventually.of_forall (fun k => div_nonneg (hT0 k)
      (mul_nonneg (Real.rpow_nonneg (hV0 k) _) (Real.sqrt_nonneg _)))) _ hb
    filter_upwards [hV,hT,eventually_gt_atTop 0] with k hVk hTk hk
    have hVpos : 0<V k := by
      have hdpos : (0:ℝ)<D k := Nat.cast_pos.mpr (hDp k)
      nlinarith
    simpa only [div_eq_mul_inv,Function.comp_def] using
      lyapunov_shrinking_bound (D k) k (hDp k) hk (T k) (V k) c C (hT0 k) hVpos hc hC hVk hTk
  · have hb := hScale.const_mul (10/Real.sqrt c)
    simp only [mul_zero] at hb
    apply squeeze_zero' (Eventually.of_forall (fun k => div_nonneg (hL0 k) (Real.sqrt_nonneg _))) _ hb
    filter_upwards [hL,hV,eventually_gt_atTop 0] with k hLk hVk hk
    have hdpos : (0:ℝ)<D k := Nat.cast_pos.mpr (hDp k)
    have hnum : 0≤10*(D k:ℝ)^2*Real.log ((k:ℝ)+D k) := (hL0 k).trans hLk
    have hbasepos : 0<Real.sqrt ((k:ℝ)/D k) := Real.sqrt_pos.mpr (by positivity)
    calc
      _ ≤ (10*(D k:ℝ)^2*Real.log ((k:ℝ)+D k))/Real.sqrt ((k:ℝ)*V k) :=
        div_le_div_of_nonneg_right hLk (Real.sqrt_nonneg _)
      _ ≤ (10*(D k:ℝ)^2*Real.log ((k:ℝ)+D k))/
          (Real.sqrt c*Real.sqrt ((k:ℝ)/D k)) :=
        div_le_div_of_nonneg_left hnum (by positivity)
          (variance_normalization_lower (D k) k (hDp k) (V k) c hc hVk)
      _ = _ := by unfold dimensionScale; field_simp <;> ring

/-- The manuscript's concrete D^5 log^2(k+D)=o(k) example, connected to the
actual same-family extraction fidelity. Only integer sector feasibility remains
an output-budget hypothesis; the CLT and overhead conditions are conclusions. -/
theorem triangular_reserved_gaussian_shrinking_variance (m n K : ℕ → ℕ)
    (hm : ∀ k,0<m k) (hn : ∀ k,0<n k) (hmn : ∀ k,m k≤n k)
    (hD : ∀ k,2≤m k*n k) (hK : ∀ k,0<K k)
    (hKa : ∀ᶠ k : ℕ in atTop,K k≤reservationLocal (m k) (n k) k (m k))
    (X : (k : ℕ) → Matrix (Fin (m k*n k)) (Fin (m k*n k)) ℂ)
    (hX : ∀ k,(X k).PosSemidef ∧ (X k).trace=1)
    (c C : ℝ) (hc : 0<c) (hC : 0≤C)
    (hV : ∀ᶠ k : ℕ in atTop,c≤((m k*n k:ℕ):ℝ)*varentropy (hX k).1.isHermitian.eigenvalues)
    (hT : ∀ᶠ k : ℕ in atTop,((m k*n k:ℕ):ℝ)*thirdInformationMoment (hX k).1.isHermitian.eigenvalues≤C)
    (hDim : Tendsto (fun k : ℕ => ((m k*n k:ℕ):ℝ)^5*
      (Real.log ((k:ℝ)+(m k*n k:ℕ)))^2/k) atTop (nhds 0)) :
    Tendsto (fun k =>
      (reservedProtocol (m k) (n k) k (K k) (hm k) (hn k) (hmn k) (hK k)).fidelity
        (tensorInput (m k) (n k) k (X k))-
      gaussianCDF 1 (((k:ℝ)*(Real.log (m k)+Real.log (n k))-2*Real.log (K k)-
        k*entropy (hX k).1.isHermitian.eigenvalues)/
        Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues))) atTop (nhds 0) := by
  have hconds := shrinking_variance_numerical_conditions (fun k => m k*n k) hD
    (fun k => thirdInformationMoment (hX k).1.isHermitian.eigenvalues)
    (fun k => varentropy (hX k).1.isHermitian.eigenvalues)
    (fun k => reservedTotalLoss (m k) (n k) k)
    (fun k => thirdAbsoluteMoment_nonneg _ _ (hX k).1.eigenvalues_nonneg)
    (fun k => law_varentropy_nonneg _ (hX k).1.eigenvalues_nonneg)
    (fun k => reservedTotalLoss_nonneg (m k) (n k) k (hm k) (hn k))
    c C hc hC hV hT (by
      filter_upwards [eventually_gt_atTop 0] with k hk
      simpa only [Nat.cast_add,Nat.cast_mul] using
        reservedTotalLoss_dimension_bound (m k) (n k) k (hm k) (hn k) (hD k) hk) hDim
  have hv : ∀ᶠ k : ℕ in atTop,0<varentropy (hX k).1.isHermitian.eigenvalues := by
    filter_upwards [hV] with k hk
    have hdpos : (0:ℝ)<(m k*n k:ℕ) := Nat.cast_pos.mpr (Nat.mul_pos (hm k) (hn k))
    have hn0 := law_varentropy_nonneg _ (hX k).1.eigenvalues_nonneg
    nlinarith
  exact triangular_reserved_gaussian_error m n K hm hn hmn hK hKa X hX hv
    hconds.1 hconds.2.1 hconds.2.2

end
end OperationalCompletion
