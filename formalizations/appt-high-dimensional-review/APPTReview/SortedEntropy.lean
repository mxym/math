import APPTReview.SortedStar

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The explicitly ordered exceptional head, using a positive lower-tail pivot. -/
noncomputable def sortedHeadA {k D : ℕ} (hD : 3*(k+1)+1 ≤ D)
    (lam : Fin D → ℝ) (t : ℝ) (i : Fin (k+1)) : ℝ :=
  lam (starSlotLabel hD (.inr (.inr (.inr i))))/t-1

noncomputable def sortedHeadBeta {k D : ℕ} (hD : 3*(k+1)+1 ≤ D)
    (lam : Fin D → ℝ) (t : ℝ) (i : Fin (k+2)) : ℝ :=
  1-lam ⟨D-(1+i.val), by omega⟩/t

/-- Scalar normalization of the shifted-star inequality. The physical theorem
below proves its budget from APPT and supplies every sign and ordering fact. -/
theorem sorted_entropyHead_from_budget {k D : ℕ} (hD : 3*(k+1)+1 ≤ D)
    (lam : Fin D → ℝ) (hf : Antitone lam) (hn : ∀ i, 0 ≤ lam i)
    (t : ℝ) (ht : 0 < t)
    (pivot : Fin D) (hp : t=lam pivot)
    (hlo : k+1 ≤ pivot.val) (hhi : pivot.val ≤ D-(2*(k+1)+1))
    (hs : (∑ i : Fin (k+1),
      (lam (starSlotLabel hD (.inr (.inr (.inr i)))) -
       lam (starSlotLabel hD (.inr (.inr (.inl i)))))^2) ≤
      4*lam (starSlotLabel hD (.inl ()))*t) :
    entropyHead (sortedHeadA hD lam t) (sortedHeadBeta hD lam t) ≤ 2 := by
  let a := sortedHeadA hD lam t
  let beta := sortedHeadBeta hD lam t
  have ha (i : Fin (k+1)) : 0 ≤ a i := by
    have hl : t ≤ lam (starSlotLabel hD (.inr (.inr (.inr i)))) := by
      rw [hp]
      apply hf
      change i.val ≤ pivot.val
      omega
    dsimp [a, sortedHeadA]
    exact sub_nonneg.mpr ((le_div_iff₀ ht).2 (by simpa using hl))
  have ha0 (i : Fin (k+1)) : a i ≤ a 0 := by
    have hl : lam (starSlotLabel hD (.inr (.inr (.inr i)))) ≤
        lam (starSlotLabel hD (.inr (.inr (.inr (0 : Fin (k+1)))))) := by
      apply hf
      change 0 ≤ i.val
      omega
    exact sub_le_sub_right (div_le_div_of_nonneg_right hl ht.le) 1
  have hb (i : Fin (k+2)) : 0 ≤ beta i := by
    have hl : lam ⟨D-(1+i.val), by omega⟩ ≤ t := by
      rw [hp]
      apply hf
      change pivot.val ≤ D-(1+i.val)
      omega
    dsimp [beta, sortedHeadBeta]
    exact sub_nonneg.mpr ((div_le_iff₀ ht).2 (by simpa using hl))
  have hba : Antitone beta := by
    intro i j hij
    have hl : lam ⟨D-(1+i.val), by omega⟩ ≤ lam ⟨D-(1+j.val), by omega⟩ := by
      apply hf
      change D-(1+j.val) ≤ D-(1+i.val)
      have hijv : i.val ≤ j.val := hij
      omega
    exact sub_le_sub_left (div_le_div_of_nonneg_right hl ht.le) 1
  have hy : beta 0 ≤ 1 := by
    have hn' := div_nonneg (hn ⟨D-1, by omega⟩) ht.le
    dsimp [beta, sortedHeadBeta]
    simpa using sub_le_self 1 hn'
  have he (i : Fin (k+1)) :
      t*(a i+beta i.succ) =
        lam (starSlotLabel hD (.inr (.inr (.inr i)))) -
        lam (starSlotLabel hD (.inr (.inr (.inl i)))) := by
    dsimp [a, beta, sortedHeadA, sortedHeadBeta, starSlotLabel]
    have hi : D-(1+i.succ.val)=D-(2+i.val) := by simp; omega
    field_simp [ne_of_gt ht]
    ring
  have he0 : t*(1-beta 0)=lam (starSlotLabel hD (.inl ())) := by
    dsimp [beta, sortedHeadBeta, starSlotLabel]
    field_simp [ne_of_gt ht]
    ring
  have hs' : t^2 * (∑ i, (a i+beta i.succ)^2) ≤ 4*t^2*(1-beta 0) := by
    simp_rw [← he, mul_pow] at hs
    rw [← Finset.mul_sum] at hs
    rw [← he0] at hs
    nlinarith
  have ht2 : 0 < t^2 := sq_pos_of_pos ht
  have budget : (∑ i, (a i+beta i.succ)^2) ≤ 4*(1-beta 0) := by nlinarith
  exact entropyHead_le_two a beta ha ha0 hb hba hy budget

/-- Full physical-to-nonlinear-head theorem for the actual ordered spectrum.
Only dimension, density and all-global-unitary APPT hypotheses are required. -/
theorem density_appt_sorted_entropyHead {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    let hD : 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) := by
      simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
    let lam := hρ.1.isHermitian.eigenvalues₀
    let t := lam ⟨Fintype.card (Fin (k+2) × Fin n)-(2*(k+1)+1), by omega⟩
    entropyHead (sortedHeadA hD lam t) (sortedHeadBeta hD lam t) ≤ 2 := by
  classical
  dsimp only
  have hD : 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
  let lam := hρ.1.isHermitian.eigenvalues₀
  let pivot : Fin (Fintype.card (Fin (k+2) × Fin n)) :=
    ⟨Fintype.card (Fin (k+2) × Fin n)-(2*(k+1)+1), by omega⟩
  have hfour : 4 ≤ Fintype.card (Fin (k+2) × Fin n) := by omega
  have ht : 0 < lam pivot := ordered_pivot_positive hfour lam
    hρ.1.isHermitian.eigenvalues₀_antitone (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
    (appt_sorted_rankTwo_linear (by omega) hmn hρ.1.isHermitian happt hfour)
    pivot (by dsimp [pivot]; omega)
  have hn (i) : 0 ≤ lam i := by
    have hi := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using hi
  exact sorted_entropyHead_from_budget hD lam hρ.1.isHermitian.eigenvalues₀_antitone hn
    (lam pivot) ht pivot rfl (by dsimp [pivot]; omega) (by dsimp [pivot]; exact le_rfl) (appt_sorted_shifted_star (h:=k+1) (by omega) hmn hρ happt hD)

end APPTReview
