/- Quantitative inversion of the internally proved finite information Berry--Esseen bound. -/
import Deviation.InformationBerryEsseen
import Deviation.InformationQuantile

open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- An exact quantitative inversion lemma for the attained quantile of an
actual finite distribution. Its Gaussian approximation is a reusable input to
this analytic lemma; the information-spectrum endpoint below proves that input
by the complete internal Berry--Esseen chain. -/
theorem finiteQuantile_gaussian_bracket (p f : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (μ s B : ℝ) (hspos : 0<s) (hB : 0≤B)
    (herror : ∀ x,|finiteCDF p f x-gaussianCDF 1 ((x-μ)/s)|≤B)
    (ε : ℝ) (hε : 0<ε) (hε' : ε<1) (hlo : B<ε) (hhi : ε+B<1) :
    gaussianQuantile 1 one_ne_zero (ε-B) (by linarith) (by linarith)≤
      (finiteQuantile p f hs ε hε'.le-μ)/s ∧
    (finiteQuantile p f hs ε hε'.le-μ)/s≤
      gaussianQuantile 1 one_ne_zero (ε+B) (by linarith) hhi := by
  let Q := finiteQuantile p f hs ε hε'.le
  let qlo := gaussianQuantile 1 one_ne_zero (ε-B) (by linarith) (by linarith)
  let qhi := gaussianQuantile 1 one_ne_zero (ε+B) (by linarith) hhi
  have hL : qlo≤(Q-μ)/s := by
    apply (gaussianCDF_strictMono 1 one_ne_zero).le_iff_le.mp
    rw [show gaussianCDF 1 qlo=ε-B from gaussianCDF_quantile _ _ _ _ _]
    have he := (abs_le.mp (herror Q)).2
    have hc := finiteQuantile_cdf p f hs ε hε'.le
    linarith
  have hU : (Q-μ)/s≤qhi := by
    have hc : ε≤finiteCDF p f (μ+s*qhi) := by
      have he := (abs_le.mp (herror (μ+s*qhi))).1
      rw [show (μ+s*qhi-μ)/s=qhi by field_simp; ring] at he
      rw [show gaussianCDF 1 qhi=ε+B from gaussianCDF_quantile _ _ _ _ _] at he
      linarith
    have hQ := (finiteQuantile_le_iff p f hp hs ε hε'.le hε (μ+s*qhi)).mpr hc
    apply (div_le_iff₀ hspos).mpr
    dsimp [Q]
    nlinarith
  exact ⟨hL,hU⟩

def informationBerryEsseenError (p : ι → ℝ) (k : ℕ) : ℝ :=
  berryEsseenConstant*thirdInformationMoment p/((varentropy p)^(3/2:ℝ)*Real.sqrt k)

omit [Nonempty ι] in
theorem informationBerryEsseenError_nonneg (p : ι → ℝ) (hp : ∀ i,0≤p i)
    (hv : 0<varentropy p) (k : ℕ) : 0 ≤ informationBerryEsseenError p k := by
  have hT : 0≤thirdInformationMoment p := thirdAbsoluteMoment_nonneg p (selfInformation p) hp
  unfold informationBerryEsseenError
  exact div_nonneg (mul_nonneg berryEsseenConstant_pos.le hT) (by positivity)

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Finite-block Gaussian quantile brackets for the actual iid information
spectrum. The approximation error is computed from the actual third moment;
no Berry--Esseen or spectral approximation is a caller hypothesis. -/
theorem informationQuantile_berryEsseen_bracket (p : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (hv : 0<varentropy p) (k : ℕ) (hk : 0<k)
    (ε : ℝ) (hε : 0<ε) (hε' : ε<1)
    (hlo : informationBerryEsseenError p k<ε) (hhi : ε+informationBerryEsseenError p k<1) :
    gaussianQuantile 1 one_ne_zero (ε-informationBerryEsseenError p k)
      (by linarith) (by have h := informationBerryEsseenError_nonneg p hp hv k; linarith)≤
      (informationQuantile p hs ε hε'.le k-k*entropy p)/Real.sqrt ((k:ℝ)*varentropy p) ∧
    (informationQuantile p hs ε hε'.le k-k*entropy p)/Real.sqrt ((k:ℝ)*varentropy p)≤
      gaussianQuantile 1 one_ne_zero (ε+informationBerryEsseenError p k)
        (by have h := informationBerryEsseenError_nonneg p hp hv k; linarith) hhi := by
  exact finiteQuantile_gaussian_bracket (iidLaw p k) (wordInformation p k)
    (iidLaw_nonneg p hp k) (iidLaw_sum p hs k) (k*entropy p)
    (Real.sqrt ((k:ℝ)*varentropy p)) (informationBerryEsseenError p k)
    (Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr hk) hv))
    (informationBerryEsseenError_nonneg p hp hv k)
    (information_iid_berryEsseen p hp hs hv k hk) ε hε hε' hlo hhi

end
end ExtractionDeviation
