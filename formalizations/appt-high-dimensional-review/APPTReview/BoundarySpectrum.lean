import APPTReview.PaperEntropy

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- A zero least entry and the physical rank-two determinant force a uniform
nonzero tail. The sorting and normalization assumptions are explicitly scalar. -/
theorem ordered_singular_spectrum {D : ℕ} (hD : 4 ≤ D) (f : Fin D → ℝ)
    (hf : Antitone f) (hs : (∑ i, f i)=1)
    (hz : f (rankTwoLabels hD (0,0))=0)
    (hd : (f (rankTwoLabels hD (1,0))-f (rankTwoLabels hD (0,1)))^2 ≤
      4*f (rankTwoLabels hD (0,0))*f (rankTwoLabels hD (1,1))) :
    ∀ i, f i = if i.val = D-1 then 0 else 1/((D : ℝ)-1) := by
  obtain ⟨d,rfl⟩ : ∃ d, D=d+4 := ⟨D-4, by omega⟩
  have he : f (0 : Fin (d+4)) = f (rankTwoLabels hD (0,1)) := by
    rw [hz] at hd
    change (f 0-f (rankTwoLabels hD (0,1)))^2 ≤ _ at hd
    nlinarith [sq_nonneg (f 0-f (rankTwoLabels hD (0,1)))]
  have heq (i : Fin (d+3)) : f i.castSucc=f 0 := by
    apply le_antisymm (hf (Fin.zero_le _))
    rw [he]
    apply hf
    change i.val ≤ d+4-2
    omega
  have hlast : rankTwoLabels hD (0,0)=Fin.last (d+3) := by
    apply Fin.ext
    simp [rankTwoLabels]
  rw [hlast] at hz
  rw [Fin.sum_univ_castSucc, hz] at hs
  simp_rw [heq] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    add_zero] at hs
  have hvalue : f 0=1/(((d+4 : ℕ) : ℝ)-1) := by
    apply (eq_div_iff (by have hn : (0 : ℝ) ≤ d := Nat.cast_nonneg d; push_cast; linarith : (((d+4 : ℕ) : ℝ)-1) ≠ 0)).2
    push_cast at hs ⊢
    nlinarith
  intro i
  split_ifs with hi
  · have hilast : i=Fin.last (d+3) := by
      apply Fin.ext
      change i.val=d+3
      omega
    simpa [hilast] using hz
  · have hilo : i ≤ rankTwoLabels hD (0,1) := by
      change i.val ≤ d+4-2
      omega
    have hfi : f i=f 0 := le_antisymm (hf (Fin.zero_le _))
      (he.symm ▸ hf hilo)
    exact hfi.trans hvalue

/-- Every singular APPT density matrix has exactly the uniform rank-(mn-1)
spectrum. The hypothesis is matrix singularity, not a guessed spectral zero. -/
theorem density_appt_singular_spectrum {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A)
    (hdet : A.det=0) :
    ∀ i : Fin (Fintype.card (Fin m × Fin n)),
      hρ.1.isHermitian.eigenvalues₀ i =
        if i.val=Fintype.card (Fin m × Fin n)-1 then 0
        else 1/((Fintype.card (Fin m × Fin n) : ℝ)-1) := by
  classical
  have hD : 4 ≤ Fintype.card (Fin m × Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
  let lam := hρ.1.isHermitian.eigenvalues₀
  have hn (i) : 0 ≤ lam i := by
    have hi := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using hi
  have hd := hρ.1.isHermitian.det_eq_prod_eigenvalues
  rw [hdet] at hd
  obtain ⟨j,hj,hzero⟩ := Finset.prod_eq_zero_iff.mp hd.symm
  have hjr : hρ.1.isHermitian.eigenvalues j=0 := by
    have hh := congrArg Complex.re hzero
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Complex.zero_re] using hh
  let q := (spectralLabel (Fin m × Fin n)).symm j
  have hq : lam q=0 := by
    have he := eigenvalues_spectralLabel hρ.1.isHermitian q
    change hρ.1.isHermitian.eigenvalues ((spectralLabel _) ((spectralLabel _).symm j))=lam q at he
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans hjr
  have hz : lam (rankTwoLabels hD (0,0))=0 := by
    apply le_antisymm _ (hn _)
    calc
      _ ≤ lam q := hρ.1.isHermitian.eigenvalues₀_antitone (by
        change q.val ≤ Fintype.card (Fin m × Fin n)-1; omega)
      _ = 0 := hq
  exact ordered_singular_spectrum hD lam hρ.1.isHermitian.eigenvalues₀_antitone
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2) hz
    (appt_sorted_rankTwo_determinant hm hmn hρ.1.isHermitian happt hD)

end APPTReview