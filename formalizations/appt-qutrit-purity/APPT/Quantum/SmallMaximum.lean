import APPT.Quantum.SpectralMoments
import APPT.Quantum.Attainment
import APPT.SpectrumBound9
import APPT.SpectrumBound12
import APPT.SpectrumBound15
import APPT.SpectrumBound18
import APPT.SpectrumBound21

open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

/-- An *unconditional* actual-state upper bound for all qutrit-qudit
systems with 3 ≤ n ≤ 7, using the five exact finite spectral certificates
and the genuine APPT-to-corner PSD implication. No quantum bridge is assumed. -/
theorem appt_purity_upper_small (n : ℕ) (hn : 3 ≤ n) (h7 : n ≤ 7)
    (A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ)
    (hA : IsDensity A) (hP : AbsolutelyPPT A) :
    purity A ≤ (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 := by
  interval_cases n
  · have h := APPT.spectrum_bound_9
      (sortedSpectrum 3 A hA.1.1)
      (sortedSpectrum_antitone 3 A hA.1.1)
      (sortedSpectrum_nonneg 3 A hA.1)
      (sortedSpectrum_sum_one 3 A hA)
      (sortedSpectrum_cornerConditions 3 (by norm_num) A hA.1.1 hP)
    rw [purity_eq_sortedSpectrum 3 A hA.1.1]
    convert h using 1 <;> norm_num
  · have h := APPT.spectrum_bound_12
      (sortedSpectrum 4 A hA.1.1)
      (sortedSpectrum_antitone 4 A hA.1.1)
      (sortedSpectrum_nonneg 4 A hA.1)
      (sortedSpectrum_sum_one 4 A hA)
      (sortedSpectrum_cornerConditions 4 (by norm_num) A hA.1.1 hP)
    rw [purity_eq_sortedSpectrum 4 A hA.1.1]
    convert h using 1 <;> norm_num
  · have h := APPT.spectrum_bound_15
      (sortedSpectrum 5 A hA.1.1)
      (sortedSpectrum_antitone 5 A hA.1.1)
      (sortedSpectrum_nonneg 5 A hA.1)
      (sortedSpectrum_sum_one 5 A hA)
      (sortedSpectrum_cornerConditions 5 (by norm_num) A hA.1.1 hP)
    rw [purity_eq_sortedSpectrum 5 A hA.1.1]
    convert h using 1 <;> norm_num
  · have h := APPT.spectrum_bound_18
      (sortedSpectrum 6 A hA.1.1)
      (sortedSpectrum_antitone 6 A hA.1.1)
      (sortedSpectrum_nonneg 6 A hA.1)
      (sortedSpectrum_sum_one 6 A hA)
      (sortedSpectrum_cornerConditions 6 (by norm_num) A hA.1.1 hP)
    rw [purity_eq_sortedSpectrum 6 A hA.1.1]
    convert h using 1 <;> norm_num
  · have h := APPT.spectrum_bound_21
      (sortedSpectrum 7 A hA.1.1)
      (sortedSpectrum_antitone 7 A hA.1.1)
      (sortedSpectrum_nonneg 7 A hA.1)
      (sortedSpectrum_sum_one 7 A hA)
      (sortedSpectrum_cornerConditions 7 (by norm_num) A hA.1.1 hP)
    rw [purity_eq_sortedSpectrum 7 A hA.1.1]
    convert h using 1 <;> norm_num

/-- Both inequality and APPT attainment for every 3 ≤ n ≤ 7. -/
theorem appt_purity_maximum_small (n : ℕ) (hn : 3 ≤ n) (h7 : n ≤ 7) :
    (∀ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
       IsDensity A → AbsolutelyPPT A →
       purity A ≤ (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2) ∧
    ∃ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A ∧ AbsolutelyPPT A ∧
      purity A = (3*(n : ℝ)+8)/(3*(n : ℝ)+2)^2 := by
  constructor
  · exact fun A hA hP => appt_purity_upper_small n hn h7 A hA hP
  · exact exists_shortState n (by omega)

end APPT.Quantum
