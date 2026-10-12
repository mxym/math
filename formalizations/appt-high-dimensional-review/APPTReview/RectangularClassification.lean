import APPTReview.RectangularCutEquality

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Every actual APPT optimizer in the rectangular region has the stated
ordered spectrum. All physical cut and convex-equality hypotheses are discharged. -/
theorem density_appt_rectangular_spectrum {m n : ℕ} (hm : 3 ≤ m)
    (hcutoff : m^3-m-2 ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A)
    (heq : APPT.Quantum.purity A=roundedPlateauPurity m n) :
    hρ.1.isHermitian.eigenvalues₀=roundedPlateauSpectrum m n := by
  have hmn := rectangular_cutoff_implies_dimensions hm hcutoff
  let D := Fintype.card (Fin m × Fin n)
  let R := Fintype.card (UpperPair m)
  have hcard : 2*R+m=m*m := upperPair_card m
  have hplace : 2*R+m ≤ D := pairPlacementBound hmn
  have hR : 0 < R := by nlinarith
  let r : Fin D := ⟨R-1,by omega⟩
  let q : Fin D := ⟨D-R-m-1,by omega⟩
  have hr : r.val+1=R := by dsimp [r]; omega
  have hq : q.val+1+R+m=D := by dsimp [q]; omega
  have hrq : r ≤ q := by change R-1 ≤ D-R-m-1; omega
  have hcut := density_appt_ordered_prefix_cut hm hmn hρ happt r q hr hq
  have hn (i : Fin D) : 0 ≤ hρ.1.isHermitian.eigenvalues₀ i := by
    have h := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using h
  have hres := ordered_rectangular_cut_unique_spectrum hm hmn
    (show D=m*n by simp [D]) r q hrq (by omega) (by omega) hcutoff
    hρ.1.isHermitian.eigenvalues₀ hρ.1.isHermitian.eigenvalues₀_antitone hn
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) hcut
  apply hres.2
  change (∑ i,(hρ.1.isHermitian.eigenvalues₀ i)^2)=roundedPlateauPurity m n
  rw [← purity_eq_ordered_eigenvalues hρ.1.isHermitian]
  exact heq

/-- The target moment is established using actual attainment, not an assumed
normalization of a proposed spectral vector. -/
theorem roundedPlateauSpectrum_squares {m n : ℕ} (hm : 3 ≤ m)
    (hcutoff : m^3-m-2 ≤ n) :
    spectralSquares (roundedPlateauSpectrum (D:=Fintype.card (Fin m × Fin n)) m n)=
      roundedPlateauPurity m n := by
  have hmn := rectangular_cutoff_implies_dimensions hm hcutoff
  obtain ⟨A,hA,hP,hp⟩ := roundedPlateauPurity_mem (by omega : 2 ≤ m) hmn
  have hf := density_appt_rectangular_spectrum hm hcutoff hA hP hp.symm
  have he := purity_eq_ordered_eigenvalues hA.1.isHermitian
  rw [hf] at he
  exact he.symm.trans hp.symm

/-- Complete ordered-spectrum equality classification among physical APPT states. -/
theorem density_appt_rectangular_maximizer_iff {m n : ℕ} (hm : 3 ≤ m)
    (hcutoff : m^3-m-2 ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    APPT.Quantum.purity A=roundedPlateauPurity m n ↔
      hρ.1.isHermitian.eigenvalues₀=roundedPlateauSpectrum m n := by
  refine ⟨density_appt_rectangular_spectrum hm hcutoff hρ happt,?_⟩
  intro hf
  rw [purity_eq_ordered_eigenvalues hρ.1.isHermitian,hf]
  exact roundedPlateauSpectrum_squares hm hcutoff

/-- One fixed physical representative of the maximizing unitary orbit. -/
noncomputable def roundedPlateauMatrix (m n : ℕ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  Matrix.diagonal (fun p => (roundedPlateauSpectrum m n ((spectralLabel (Fin m × Fin n)).symm p) : ℂ))

theorem eigenvalue_diagonal_eq_rounded {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} (hA : A.IsHermitian)
    (hf : hA.eigenvalues₀=roundedPlateauSpectrum m n) :
    Matrix.diagonal (fun p => (hA.eigenvalues p : ℂ))=roundedPlateauMatrix m n := by
  unfold roundedPlateauMatrix
  congr 1
  funext p
  have he := eigenvalues_spectralLabel hA ((spectralLabel (Fin m × Fin n)).symm p)
  simp only [Equiv.apply_symm_apply] at he
  rw [he,hf]

/-- The actual matrix is a global unitary conjugate of the fixed representative. -/
theorem hermitian_eq_unitary_rounded {m n : ℕ}
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ} (hA : A.IsHermitian)
    (hf : hA.eigenvalues₀=roundedPlateauSpectrum m n) :
    ∃ U : Matrix.unitaryGroup (Fin m × Fin n) ℂ,
      A=(U : Matrix _ _ ℂ)*roundedPlateauMatrix m n*(U : Matrix _ _ ℂ)ᴴ := by
  refine ⟨hA.eigenvectorUnitary,?_⟩
  have he := hA.spectral_theorem
  simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
    RCLike.ofReal_eq_complex_ofReal,Function.comp_def,eigenvalue_diagonal_eq_rounded hA hf] using he

/-- The fixed representative is itself a trace-one APPT state at the maximum. -/
theorem roundedPlateauMatrix_properties {m n : ℕ} (hm : 3 ≤ m)
    (hcutoff : m^3-m-2 ≤ n) :
    APPT.Quantum.IsDensity (roundedPlateauMatrix m n) ∧
    APPT.Quantum.AbsolutelyPPT (roundedPlateauMatrix m n) ∧
    APPT.Quantum.purity (roundedPlateauMatrix m n)=roundedPlateauPurity m n := by
  have hmn := rectangular_cutoff_implies_dimensions hm hcutoff
  obtain ⟨A,hA,hP,hp⟩ := roundedPlateauPurity_mem (by omega : 2 ≤ m) hmn
  have hf := density_appt_rectangular_spectrum hm hcutoff hA hP hp.symm
  have hd := eigenvalue_diagonal_eq_rounded hA.1.isHermitian hf
  have ha := eigenvalue_diagonal_appt hA.1.isHermitian hP
  rw [hd] at ha
  have hden := APPT.Quantum.isDensity_unitaryConjugate hA (star hA.1.isHermitian.eigenvectorUnitary)
  have hz := hA.1.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hden' : APPT.Quantum.IsDensity (Matrix.diagonal (fun p => (hA.1.isHermitian.eigenvalues p : ℂ))) := by
    simpa only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal,Function.comp_def] using (hz ▸ hden)
  rw [hd] at hden'
  obtain ⟨U,hU⟩ := hermitian_eq_unitary_rounded hA.1.isHermitian hf
  have hu := APPT.Quantum.purity_unitaryConjugate (roundedPlateauMatrix m n) U
  rw [← hU] at hu
  exact ⟨hden',ha,hu.symm.trans hp.symm⟩

/-- All and only maximizing physical APPT states form this single unitary orbit.
No orbit, spectral characterization, or maximizing hypothesis is supplied on the right. -/
theorem appt_rectangular_maximizer_iff_unitary {m n : ℕ} (hm : 3 ≤ m)
    (hcutoff : m^3-m-2 ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) :
    (APPT.Quantum.AbsolutelyPPT A ∧ APPT.Quantum.purity A=roundedPlateauPurity m n) ↔
      ∃ U : Matrix.unitaryGroup (Fin m × Fin n) ℂ,
        A=(U : Matrix _ _ ℂ)*roundedPlateauMatrix m n*(U : Matrix _ _ ℂ)ᴴ := by
  constructor
  · rintro ⟨hP,hp⟩
    exact hermitian_eq_unitary_rounded hρ.1.isHermitian
      (density_appt_rectangular_spectrum hm hcutoff hρ hP hp)
  · rintro ⟨U,rfl⟩
    have hc := roundedPlateauMatrix_properties hm hcutoff
    exact ⟨APPT.Quantum.absolutelyPPT_conjugate hc.2.1 U,
      (APPT.Quantum.purity_unitaryConjugate _ U).trans hc.2.2⟩

/-- The orbit classification expressed directly using the original IsGreatest objective. -/
theorem appt_rectangular_isGreatest_iff_unitary {m n : ℕ} (hm : 3 ≤ m)
    (hcutoff : m^3-m-2 ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) :
    (APPT.Quantum.AbsolutelyPPT A ∧ IsGreatest (apptPurityValues m n) (APPT.Quantum.purity A)) ↔
      ∃ U : Matrix.unitaryGroup (Fin m × Fin n) ℂ,
        A=(U : Matrix _ _ ℂ)*roundedPlateauMatrix m n*(U : Matrix _ _ ℂ)ᴴ := by
  have hg := appt_rectangular_purity_isGreatest hm hcutoff
  rw [← appt_rectangular_maximizer_iff_unitary hm hcutoff hρ]
  constructor
  · rintro ⟨hP,hA⟩
    exact ⟨hP,le_antisymm (hg.2 hA.1) (hA.2 hg.1)⟩
  · rintro ⟨hP,hEq⟩
    exact ⟨hP,hEq.symm ▸ hg⟩

end APPTReview
