import APPTReview.RectangularClassification

open scoped BigOperators ComplexOrder
namespace APPTReview

theorem rectangular_even_spectrum_control :
    roundedPlateauSpectrum (D:=232) 4 58 ⟨86,by decide⟩=(5/870:ℝ) ∧
    roundedPlateauSpectrum (D:=232) 4 58 ⟨87,by decide⟩=(3/870:ℝ) := by
  norm_num [roundedPlateauSpectrum,plateauDenominator]

theorem rectangular_odd_spectrum_control :
    roundedPlateauSpectrum (D:=236) 4 59 ⟨88,by decide⟩=(5/886:ℝ) ∧
    roundedPlateauSpectrum (D:=236) 4 59 ⟨89,by decide⟩=(3/886:ℝ) := by
  norm_num [roundedPlateauSpectrum,plateauDenominator]

theorem rectangular_floor_spectrum_rejected :
    roundedPlateauSpectrum (D:=236) 4 59 ⟨88,by decide⟩ ≠ (3/884:ℝ) := by
  norm_num [roundedPlateauSpectrum,plateauDenominator]

theorem rectangular_reference_physical_control :
    APPT.Quantum.IsDensity (roundedPlateauMatrix 4 58) ∧
    APPT.Quantum.AbsolutelyPPT (roundedPlateauMatrix 4 58) ∧
    APPT.Quantum.purity (roundedPlateauMatrix 4 58)=(2/435:ℝ) := by
  have h := roundedPlateauMatrix_properties (m:=4) (n:=58) (by decide) (by decide)
  norm_num [roundedPlateauPurity,plateauScaledPurity,plateauDenominator] at h
  exact h

end APPTReview
