import APPT.UniformSpectrumGaps
import APPT.Uniform
import APPT.Compression

open scoped BigOperators
namespace APPT

/-- The uniform certificate applied to an arbitrary ordered outer spectrum. -/
theorem outer_population_bound (y : Fin 9 → ℝ) (t z : ℝ)
    (hy : Antitone y) (hn : ∀ i, 0 ≤ y i)
    (hA : (matA y).PosSemidef) (hB : (matB y).PosSemidef)
    (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 18 ≤ t+z)
    (hT : (∑ i, y i)+t*y 2+z*y 3=1) :
    (∑ i, (y i)^2)+t*(y 2)^2+z*(y 3)^2 ≤ 9/(8*(9+t+z)) := by
  have h := Uniform.normalized_bound (gaps9 y) t z (gaps9_nonneg y hy hn)
    (by simpa only [outer_gaps9] using hA)
    (by simpa only [outer_gaps9] using hB) ht hz (by linarith)
    (by simpa only [Uniform.total, spectrum_gaps9, outer_gaps9] using hT)
  simpa only [Uniform.squareTotal, spectrum_gaps9, outer_gaps9] using h

/-- Any number M≥18 of middle eigenvalues can be compressed exactly. -/
theorem arbitrary_middle_bound {M : ℕ} (hM : 18 ≤ M)
    (y : Fin 9 → ℝ) (x : Fin M → ℝ)
    (hy : Antitone y) (hn : ∀ i, 0 ≤ y i)
    (hx : ∀ i, y 3 ≤ x i ∧ x i ≤ y 2)
    (hA : (matA y).PosSemidef) (hB : (matB y).PosSemidef)
    (hT : (∑ i, y i)+(∑ i, x i)=1) :
    (∑ i, (y i)^2)+(∑ i, (x i)^2) ≤ 9/(8*(9+(M : ℝ))) := by
  obtain ⟨t,z,ht,hz,htz,hs,hsq⟩ :=
    endpoint_compression x (y 2) (y 3) (hy (by decide)) hx
  have hMr : (18 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hp := outer_population_bound y t z hy hn hA hB ht hz
    (by linarith) (by rw [hs] at hT; linarith)
  have hd : (9 : ℝ)+t+z=9+(M : ℝ) := by linarith
  rw [hd] at hp
  linarith

end APPT
