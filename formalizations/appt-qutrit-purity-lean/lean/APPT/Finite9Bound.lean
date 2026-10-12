import APPT.Finite9
import APPT.FiniteSpectrumGaps

open scoped BigOperators

namespace APPT.Finite9

theorem spectrum_eq_tailSum (g : Fin 9 → ℝ) :
    spectrum g = APPT.FiniteSpectrum.tailSum g := by
  funext i
  fin_cases i <;>
    simp [spectrum, APPT.FiniteSpectrum.tailSum, Fin.sum_univ_succ] <;> ring

/-- Exact inverse from an arbitrary nine-entry spectrum to the certificate's gap coordinates. -/
theorem spectrum_gaps (y : Fin 9 → ℝ) :
    spectrum (APPT.FiniteSpectrum.gaps y) = y := by
  rw [spectrum_eq_tailSum]
  funext i
  exact APPT.FiniteSpectrum.tailSum_gaps y i

theorem outer_gaps (y : Fin 9 → ℝ) :
    outer (APPT.FiniteSpectrum.gaps y) = y := by
  rw [outer, spectrum_gaps]
  funext i
  fin_cases i <;> rfl

/-- The D=9 purity bound for arbitrary sorted, nonnegative, normalized spectra satisfying
the two real-matrix PSD conditions. No quantum-semantic equivalence is assumed or renamed. -/
theorem arbitrary_spectrum_bound (y : Fin 9 → ℝ)
    (horder : Antitone y) (hpos : ∀ i, 0 ≤ y i)
    (hnormalized : ∑ i, y i = 1)
    (hA : (APPT.matA y).PosSemidef) (hB : (APPT.matB y).PosSemidef) :
    (∑ i, (y i)^2) ≤ (17 : ℝ) / 121 := by
  have hg := APPT.FiniteSpectrum.gaps_nonneg y horder hpos
  have hA' : (APPT.matA (outer (APPT.FiniteSpectrum.gaps y))).PosSemidef := by
    simpa only [outer_gaps] using hA
  have hB' : (APPT.matB (outer (APPT.FiniteSpectrum.gaps y))).PosSemidef := by
    simpa only [outer_gaps] using hB
  have hT : total (APPT.FiniteSpectrum.gaps y) = 1 := by
    simpa only [total, spectrum_gaps] using hnormalized
  have h := normalized_bound (APPT.FiniteSpectrum.gaps y) hg hA' hB' hT
  simpa only [squareTotal, spectrum_gaps] using h

end APPT.Finite9
