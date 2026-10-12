import APPTReview.ComplementSufficiency
import APPTReview.BoundarySpectrum

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Exact second moment of the rank-(D-1) uniform spectrum. -/
theorem uniform_hole_square_sum {D : ℕ} (hD : 1<D) (f : Fin D → ℝ)
    (hf : ∀ i, f i=if i.val=D-1 then 0 else 1/((D:ℝ)-1)) :
    (∑ i, (f i)^2)=1/((D:ℝ)-1) := by
  let last : Fin D := ⟨D-1,by omega⟩
  have he (i : Fin D) : (f i)^2=if i=last then 0 else (1/((D:ℝ)-1))^2 := by
    rw [hf]
    have hi : i=last ↔ i.val=D-1 := by constructor <;> intro h; exact congrArg Fin.val h; exact Fin.ext h
    simp only [hi]
    split_ifs <;> simp
  simp_rw [he]
  have hs := sum_except_real last ((1/((D:ℝ)-1))^2)
  have hs' : (∑ i : Fin D, if i=last then 0 else (1/((D:ℝ)-1))^2) =
      ((D:ℝ)-1)*(1/((D:ℝ)-1))^2 := by simpa [eq_comm] using hs
  rw [hs']
  have hdR : (1:ℝ)<D := by exact_mod_cast hD
  have hz : (D:ℝ)-1≠0 := by linarith
  field_simp

/-- The missing converse: an actual density with this spectrum is APPT. -/
theorem density_appt_of_uniform_singular_spectrum {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} (hρ : APPT.Quantum.IsDensity A)
    (hs : ∀ i : Fin (Fintype.card (Fin m × Fin n)),
      hρ.1.isHermitian.eigenvalues₀ i=
        if i.val=Fintype.card (Fin m × Fin n)-1 then 0
        else 1/((Fintype.card (Fin m × Fin n):ℝ)-1)) :
    APPT.Quantum.AbsolutelyPPT A := by
  have hD : 1<m*n := by nlinarith
  apply density_appt_of_purity_ball hD hρ
  rw [purity_eq_ordered_eigenvalues hρ.1.isHermitian]
  have he := uniform_hole_square_sum (by simpa using hD) hρ.1.isHermitian.eigenvalues₀ hs
  exact (by simpa using he.le)

/-- Full necessary-and-sufficient classification for actual singular density matrices. -/
theorem singular_density_appt_iff_spectrum {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hdet : A.det=0) :
    APPT.Quantum.AbsolutelyPPT A ↔
      ∀ i : Fin (Fintype.card (Fin m × Fin n)),
        hρ.1.isHermitian.eigenvalues₀ i=
          if i.val=Fintype.card (Fin m × Fin n)-1 then 0
          else 1/((Fintype.card (Fin m × Fin n):ℝ)-1) :=
  ⟨fun ha => density_appt_singular_spectrum hm hmn hρ ha hdet,
   density_appt_of_uniform_singular_spectrum hm hmn hρ⟩

theorem singular_appt_purity {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (ha : APPT.Quantum.AbsolutelyPPT A) (hdet : A.det=0) :
    APPT.Quantum.purity A=1/((m:ℝ)*n-1) := by
  rw [purity_eq_ordered_eigenvalues hρ.1.isHermitian]
  have he := uniform_hole_square_sum
    (by simp only [Fintype.card_prod,Fintype.card_fin]; nlinarith : 1<Fintype.card (Fin m × Fin n))
    hρ.1.isHermitian.eigenvalues₀ (density_appt_singular_spectrum hm hmn hρ ha hdet)
  simpa using he

/-- Singularity is essential to the equivalence; the purity ball is only sufficient in general. -/
theorem singular_density_appt_iff_purity {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (hdet : A.det=0) :
    APPT.Quantum.AbsolutelyPPT A ↔ APPT.Quantum.purity A=1/((m:ℝ)*n-1) :=
  ⟨fun ha => singular_appt_purity hm hmn hρ ha hdet,
   fun he => density_appt_of_purity_ball (by nlinarith) hρ he.le⟩

end APPTReview
