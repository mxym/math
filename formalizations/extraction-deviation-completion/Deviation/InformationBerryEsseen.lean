import Deviation.BerryEsseen

open scoped BigOperators NNReal ENNReal Topology ComplexOrder
open MeasureTheory ProbabilityTheory Filter Set ExtractionSpectrum Matrix

namespace ExtractionDeviation
noncomputable section

theorem berryEsseenConstant_pos : 0<berryEsseenConstant :=
  lt_of_lt_of_le (by norm_num : (0:ℝ)<1) berryEsseenConstant_ge_one

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The full finite iid information-spectrum Berry--Esseen inequality,
uniform in every real threshold and every finite alphabet, retaining zero
spectral weights. All probability inputs are instantiated internally. -/
theorem information_iid_berryEsseen (p : ι → ℝ) (hp : ∀ i,0≤p i)
    (hs : ∑ i,p i=1) (hv : 0<varentropy p) (k : ℕ) (hk : 0<k) (x : ℝ) :
    |iidInformationEvent p k x-gaussianCDF 1 ((x-k*entropy p)/
      Real.sqrt ((k:ℝ)*varentropy p))|≤
        berryEsseenConstant*thirdInformationMoment p/((varentropy p)^(3/2:ℝ)*Real.sqrt k) := by
  have h := finite_iid_berryEsseen p (selfInformation p) hp hs hv k hk
    ((x-k*entropy p)/Real.sqrt ((k:ℝ)*varentropy p))
  rw [standardizedInformationMeasure_Iic p hp hs hv k hk x,
    lyapunovRatio_eq p (selfInformation p) hv k hk] at h
  apply h.trans_eq
  rw [variance_three_halves _ hv]
  exact (mul_div_assoc _ _ _).symm

/-- The density endpoint uses the actual complex Hermitian eigenvalues and
the already proved exact tensor spectral-weight bridge. It requires neither
full rank nor a prescribed minimum nonzero eigenvalue. -/
theorem density_information_berryEsseen {D : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X.PosSemidef ∧ X.trace=1) (hv : 0<varentropy hX.1.isHermitian.eigenvalues)
    (k : ℕ) (hk : 0<k) (x : ℝ) :
    |informationMass (iidLaw hX.1.isHermitian.eigenvalues k) x-
      gaussianCDF 1 ((x-k*entropy hX.1.isHermitian.eigenvalues)/
        Real.sqrt ((k:ℝ)*varentropy hX.1.isHermitian.eigenvalues))|≤
      berryEsseenConstant*thirdInformationMoment hX.1.isHermitian.eigenvalues/
        ((varentropy hX.1.isHermitian.eigenvalues)^(3/2:ℝ)*Real.sqrt k) := by
  rw [informationMass_iidLaw _ (fun i => hX.1.eigenvalues_nonneg i) k]
  exact information_iid_berryEsseen hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) hv k hk x

end
end ExtractionDeviation
