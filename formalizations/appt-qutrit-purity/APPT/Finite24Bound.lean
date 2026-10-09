import APPT.Finite24
import APPT.FiniteSpectrumGaps

open scoped BigOperators
namespace APPT.Finite24

theorem spectrum_eq_tailSum (g : Fin 24 → ℝ) :
    spectrum g = APPT.FiniteSpectrum.tailSum g := by
  funext i
  fin_cases i <;>
    simp [spectrum, APPT.FiniteSpectrum.tailSum, Fin.sum_univ_succ] <;> ring

theorem spectrum_gaps (y : Fin 24 → ℝ) :
    spectrum (APPT.FiniteSpectrum.gaps y) = y := by
  rw [spectrum_eq_tailSum]
  funext i
  exact APPT.FiniteSpectrum.tailSum_gaps y i

theorem outer_gaps (y : Fin 24 → ℝ) :
    outer (APPT.FiniteSpectrum.gaps y) = ![y 0, y 1, y 2, y 18, y 19, y 20, y 21, y 22, y 23] := by
  rw [outer, spectrum_gaps]

theorem arbitrary_spectrum_bound (y : Fin 24 → ℝ)
    (horder : Antitone y) (hpos : ∀ i, 0 ≤ y i)
    (hnormalized : ∑ i, y i = 1)
    (hA : (APPT.matA (![ y 0, y 1, y 2, y 18, y 19, y 20, y 21, y 22, y 23 ])).PosSemidef)
    (hB : (APPT.matB (![ y 0, y 1, y 2, y 18, y 19, y 20, y 21, y 22, y 23 ])).PosSemidef) :
    (∑ i, (y i)^2) ≤ (32/676 : ℝ) := by
  have hg := APPT.FiniteSpectrum.gaps_nonneg y horder hpos
  have hA' : (APPT.matA (outer (APPT.FiniteSpectrum.gaps y))).PosSemidef := by
    simpa only [outer_gaps] using hA
  have hB' : (APPT.matB (outer (APPT.FiniteSpectrum.gaps y))).PosSemidef := by
    simpa only [outer_gaps] using hB
  have hT : total (APPT.FiniteSpectrum.gaps y) = 1 := by
    simpa only [total, spectrum_gaps] using hnormalized
  have h := normalized_bound (APPT.FiniteSpectrum.gaps y) hg hA' hB' hT
  simpa only [squareTotal, spectrum_gaps] using h

end APPT.Finite24
