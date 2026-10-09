import APPT.SpectrumReindex
import APPT.UniformSpectrumGaps
import APPT.Compression

open scoped BigOperators
namespace APPT

/-- The precise input needed from the (separately compiled) 1635-term
uniform certificate. This is a *proposition*, not an axiom or proved result.
Any final theorem must supply a proof of it. -/
def UniformCertificateBound : Prop :=
  ∀ (g : Fin 9 → ℝ) (t z : ℝ),
    (∀ i, 0 ≤ g i) →
    (matA (Uniform.outer g)).PosSemidef →
    (matB (Uniform.outer g)).PosSemidef →
    0 ≤ t → 0 ≤ z → 0 ≤ t + z - 18 →
    Uniform.total g t z = 1 →
    Uniform.squareTotal g t z ≤ 9 / (8 * (9 + t + z))

/-- The uniform inequality for arbitrary sorted nine outer eigenvalues.
Uses no unproved theorem: the certificate is an explicit parameter. -/
theorem outer_population_of_uniform (hUniform : UniformCertificateBound)
    (y : Fin 9 → ℝ) (t z : ℝ)
    (hy : Antitone y) (hn : ∀ i, 0 ≤ y i)
    (hA : (matA y).PosSemidef) (hB : (matB y).PosSemidef)
    (ht : 0 ≤ t) (hz : 0 ≤ z) (hw : 18 ≤ t + z)
    (hT : (∑ i, y i) + t * y 2 + z * y 3 = 1) :
    (∑ i, (y i)^2) + t * (y 2)^2 + z * (y 3)^2 ≤
      9 / (8 * (9 + t + z)) := by
  have h := hUniform (gaps9 y) t z (gaps9_nonneg y hy hn)
    (by simpa only [outer_gaps9] using hA)
    (by simpa only [outer_gaps9] using hB)
    ht hz (by linarith)
    (by simpa only [Uniform.total, spectrum_gaps9, outer_gaps9] using hT)
  simpa only [Uniform.squareTotal, spectrum_gaps9, outer_gaps9] using h

/-- Exact endpoint compression for arbitrary many middle eigenvalues,
conditionally on the *named, explicit* unproved uniform certificate. -/
theorem arbitrary_middle_of_uniform (hUniform : UniformCertificateBound)
    {M : ℕ} (hM : 18 ≤ M)
    (y : Fin 9 → ℝ) (x : Fin M → ℝ)
    (hy : Antitone y) (hn : ∀ i, 0 ≤ y i)
    (hx : ∀ i, y 3 ≤ x i ∧ x i ≤ y 2)
    (hA : (matA y).PosSemidef) (hB : (matB y).PosSemidef)
    (hT : (∑ i, y i) + (∑ i, x i) = 1) :
    (∑ i, (y i)^2) + (∑ i, (x i)^2) ≤
      9 / (8 * (9 + (M : ℝ))) := by
  obtain ⟨t,z,ht,hz,htz,hs,hsq⟩ :=
    endpoint_compression x (y 2) (y 3) (hy (by decide)) hx
  have hMr : (18 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hp := outer_population_of_uniform hUniform y t z hy hn hA hB ht hz
    (by linarith) (by rw [hs] at hT; linarith)
  have hd : (9 : ℝ) + t + z = 9 + (M : ℝ) := by linarith
  rw [hd] at hp
  linarith

/-- The complete large-dimension ordered-spectrum reduction. The only
remaining analytic hypothesis is precisely `UniformCertificateBound`, and
the two matrices are still explicitly assumed PSD. This is **not yet** a
theorem about APPT density operators; the quantum necessity bridge is separate. -/
theorem ordered_large_of_uniform (hUniform : UniformCertificateBound)
    {M : ℕ} (hM : 18 ≤ M)
    (lam : Fin (3 + (M + 6)) → ℝ) (hlam : Antitone lam)
    (hn : ∀ i, 0 ≤ lam i) (hT : (∑ i, lam i) = 1)
    (hA : (matA (lam ∘ outerIndex M)).PosSemidef)
    (hB : (matB (lam ∘ outerIndex M)).PosSemidef) :
    (∑ i, (lam i)^2) ≤ 9 / (8 * (9 + (M : ℝ))) := by
  have hy : Antitone (lam ∘ outerIndex M) :=
    hlam.comp_monotone (outerIndex_monotone M)
  have hx : ∀ i : Fin M,
      (lam ∘ outerIndex M) 3 ≤ (lam ∘ middleIndex) i ∧
      (lam ∘ middleIndex) i ≤ (lam ∘ outerIndex M) 2 := by
    intro i
    constructor
    · apply hlam
      simp [Function.comp_def, outerIndex, middleIndex, Fin.le_iff_val_le_val]
      omega
    · apply hlam
      simp [Function.comp_def, outerIndex, middleIndex, Fin.le_iff_val_le_val]
  have hs := split_outer_middle lam
  have hss := split_outer_middle (fun i => (lam i)^2)
  have hp := arbitrary_middle_of_uniform hUniform hM
    (lam ∘ outerIndex M) (lam ∘ middleIndex)
    hy (fun i => hn _) hx hA hB
    (by simpa only [Function.comp_def] using hs.symm.trans hT)
  simpa only [Function.comp_def, ← hss] using hp

end APPT
