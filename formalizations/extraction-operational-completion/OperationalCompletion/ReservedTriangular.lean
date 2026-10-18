import OperationalCompletion.ReservedQuantile
import Deviation.QuantitativeTriangular

open scoped BigOperators ComplexOrder Topology
open Matrix SymmetricSupport MinimaxProfile Filter ExtractionSpectrum ExtractionDeviation
namespace OperationalCompletion
noncomputable section

theorem reservedTotalLoss_nonneg (m n k : ℕ) (hm : 0<m) (hn : 0<n) :
    0≤reservedTotalLoss m n k := by
  have hQ : (1:ℝ)≤paperReservationDivisor m n k := by
    exact_mod_cast paperReservationDivisor_pos m n k hm hn
  have hl : 0≤reservationLoss m n k := by
    unfold reservationLoss
    apply Real.log_nonneg
    nlinarith
  exact add_nonneg (compressionLoss_nonneg _ _ (Nat.mul_pos hm hn)) hl

/-- Finite Gaussian error for the very same family used for all mixed inputs
and the sharp pure-state guarantee. The reservation loss is retained. -/
theorem reservedProtocol_gaussian_error (m n k K : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (hk : 0<k) (hK : 0<K) (hKa : K≤reservationLocal m n k m)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1)
    (hv : 0<varentropy hX.1.isHermitian.eigenvalues) (t : ℝ) (ht : 0≤t) :
    |(reservedProtocol m n k K hm hn hmn hK).fidelity (tensorInput m n k X)-
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
  · convert reservedProtocol_berryEsseen m n k K hm hn hmn hk hK hKa X hX hv using 1 <;> ring_nf
  · convert protocol_berryEsseen_upper m n k K hm hn hk hK
      (reservedProtocol m n k K hm hn hmn hK) X hX hv t using 1 <;> ring_nf

/-- Genuine growing-dimension Gaussian approximation for the single reserved
family. Variances may shrink; only the computed numerical ratios are assumed. -/
theorem triangular_reserved_gaussian_error (m n K : ℕ → ℕ)
    (hm : ∀ k,0<m k) (hn : ∀ k,0<n k) (hmn : ∀ k,m k≤n k)
    (hK : ∀ k,0<K k)
    (hKa : ∀ᶠ k : ℕ in atTop,K k≤reservationLocal (m k) (n k) k (m k))
    (X : (k : ℕ) → Matrix (Fin (m k*n k)) (Fin (m k*n k)) ℂ)
    (hX : ∀ k,(X k).PosSemidef ∧ (X k).trace=1)
    (hv : ∀ k,0<varentropy (hX k).1.isHermitian.eigenvalues)
    (hLyap : Tendsto (fun k : ℕ => thirdInformationMoment (hX k).1.isHermitian.eigenvalues/
      ((varentropy (hX k).1.isHermitian.eigenvalues)^(3/2:ℝ)*Real.sqrt k)) atTop (nhds 0))
    (hSigma : Tendsto (fun k : ℕ => Real.sqrt ((k:ℝ)*
      varentropy (hX k).1.isHermitian.eigenvalues)) atTop atTop)
    (hLoss : Tendsto (fun k : ℕ => reservedTotalLoss (m k) (n k) k/
      Real.sqrt ((k:ℝ)*varentropy (hX k).1.isHermitian.eigenvalues)) atTop (nhds 0)) :
    Tendsto (fun k =>
      (reservedProtocol (m k) (n k) k (K k) (hm k) (hn k) (hmn k) (hK k)).fidelity
        (tensorInput (m k) (n k) k (X k))-
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
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hs : 0<s k := Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) (hv k))
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
  filter_upwards [hKa,eventually_gt_atTop 0] with k hcap hk
  exact reservedProtocol_gaussian_error (m k) (n k) k (K k) (hm k) (hn k) (hmn k) hk
    (hK k) hcap (X k) (hX k) (hv k) _ (Real.sqrt_nonneg _)

end
end OperationalCompletion
