import OperationalCompletion.ReservedTriangular
import OperationalCompletion.ReservedOptimum

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

/-- The finite Gaussian bound for the genuine physical supremum, with an
actual common-family witness establishing nonemptiness of the protocol class. -/
theorem reserved_optimum_gaussian_error (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (hk : 0<k) (hK : 0<K) (hKa : K≤reservationLocal m n k m)
    (C : KrausPPTProtocol (m^k) (n^k) K → Prop)
    (hC : C (reservedProtocol m n k K hm hn hmn hK))
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues) (t : ℝ) (ht : 0≤t) :
    |protocolOptimum C (tensorInput m n k X)-
      gaussianCDF 1 (((k:ℝ)*(Real.log m+Real.log n)-2*Real.log K-
        k*entropy hX.1.isHermitian.eigenvalues)/
        Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))| ≤
      informationBerryEsseenError hX.1.isHermitian.eigenvalues k+
      gaussianPeak*max
        (reservedTotalLoss m n k/Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))
        (t/Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))+Real.exp (-t/2) := by
  apply gaussian_sandwich_error
  · exact div_nonneg (reservedTotalLoss_nonneg m n k hm hn) (Real.sqrt_nonneg _)
  · exact div_nonneg ht (Real.sqrt_nonneg _)
  · exact (Real.exp_pos _).le
  · have hlo := reservedProtocol_berryEsseen m n k K hm hn hmn hk hK hKa X hX hv
    have hge := protocolOptimum_ge hK C _ (tensorInput_density m n k X hX) _ hC
    convert hlo.trans hge using 1 <;> ring_nf
  · apply protocolOptimum_le C _ _ hC
    intro V _
    convert protocol_berryEsseen_upper m n k K hm hn hk hK V X hX hv t using 1 <;> ring_nf

theorem triangular_reserved_optimum_gaussian_error (m n K : ℕ → ℕ)
    (hm : ∀ k,0<m k) (hn : ∀ k,0<n k) (hmn : ∀ k,m k≤n k)
    (hK : ∀ k,0<K k)
    (hKa : ∀ᶠ k : ℕ in atTop,K k≤reservationLocal (m k) (n k) k (m k))
    (C : ∀ k,KrausPPTProtocol ((m k)^k) ((n k)^k) (K k) → Prop)
    (hC : ∀ k,C k (reservedProtocol (m k) (n k) k (K k) (hm k) (hn k) (hmn k) (hK k)))
    (X : (k : ℕ) → Matrix (Fin (m k*n k)) (Fin (m k*n k)) ℂ)
    (hX : ∀ k,(X k).PosSemidef ∧ (X k).trace=1)
    (hv : ∀ᶠ k : ℕ in atTop,0<varentropy (hX k).1.isHermitian.eigenvalues)
    (hLyap : Tendsto (fun k : ℕ => thirdInformationMoment (hX k).1.isHermitian.eigenvalues/
      ((varentropy (hX k).1.isHermitian.eigenvalues)^(3/2:ℝ)*Real.sqrt k)) atTop (nhds 0))
    (hSigma : Tendsto (fun k : ℕ => Real.sqrt ((k:ℝ)*
      varentropy (hX k).1.isHermitian.eigenvalues)) atTop atTop)
    (hLoss : Tendsto (fun k : ℕ => reservedTotalLoss (m k) (n k) k/
      Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues)) atTop (nhds 0)) :
    Tendsto (fun k => protocolOptimum (C k) (tensorInput (m k) (n k) k (X k))-
      gaussianCDF 1 (((k:ℝ)*(Real.log (m k)+Real.log (n k))-2*Real.log (K k)-
        k*entropy (hX k).1.isHermitian.eigenvalues)/
        Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues))) atTop (nhds 0) := by
  let s := fun k : ℕ => Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues)
  have hB : Tendsto (fun k => informationBerryEsseenError (hX k).1.isHermitian.eigenvalues k)
      atTop (nhds 0) := by
    simpa only [mul_zero,informationBerryEsseenError,mul_div_assoc] using hLyap.const_mul berryEsseenConstant
  have ht := Real.tendsto_sqrt_atTop.comp hSigma
  have hdiv : Tendsto (fun k => Real.sqrt (s k)/s k) atTop (nhds 0) := by
    apply (tendsto_inv_atTop_zero.comp ht).congr'
    filter_upwards [hv,eventually_gt_atTop 0] with k hvk hk
    have hs : 0<s k := Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) hvk)
    have hr := Real.sq_sqrt hs.le
    have htpos := Real.sqrt_pos.mpr hs
    change (Real.sqrt (s k))⁻¹ = Real.sqrt (s k) / s k
    field_simp
    nlinarith
  have htail : Tendsto (fun k => Real.exp (-Real.sqrt (s k)/2)) atTop (nhds 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (ht.atTop_mul_const (by norm_num : (0:ℝ)<1/2)) using 1
    ext k; dsimp [Function.comp_def,s]; congr 1 <;> ring
  have hbound := (hB.add ((hLoss.max hdiv).const_mul gaussianPeak)).add htail
  simp only [max_self,mul_zero,add_zero] at hbound
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hbound
  filter_upwards [hKa,hv,eventually_gt_atTop 0] with k hcap hvk hk
  exact reserved_optimum_gaussian_error (m k) (n k) k (K k) (hm k) (hn k) (hmn k) hk
    (hK k) hcap (C k) (hC k) (X k) (hX k) hvk _ (Real.sqrt_nonneg _)

end
end OperationalCompletion
