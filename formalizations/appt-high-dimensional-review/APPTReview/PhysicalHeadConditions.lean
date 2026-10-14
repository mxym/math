import APPTReview.PaperEntropy
import APPTReview.EntropyHeadStability

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

theorem sorted_entropyHead_conditions_from_budget {k D : ℕ} (hD : 3*(k+1)+1 ≤ D)
    (lam : Fin D → ℝ) (hf : Antitone lam) (hn : ∀ i, 0 ≤ lam i)
    (t : ℝ) (ht : 0 < t)
    (pivot : Fin D) (hp : t=lam pivot)
    (hlo : k+1 ≤ pivot.val) (hhi : pivot.val ≤ D-(2*(k+1)+1))
    (hs : (∑ i : Fin (k+1),
      (lam (starSlotLabel hD (.inr (.inr (.inr i)))) -
       lam (starSlotLabel hD (.inr (.inr (.inl i)))))^2) ≤
      4*lam (starSlotLabel hD (.inl ()))*t) :
    EntropyHeadConditions (sortedHeadA hD lam t) (sortedHeadBeta hD lam t) := by
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
  exact ⟨ha,ha0,hb,hba,hy,budget⟩

theorem density_appt_head_conditions_at_pivot {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A)
    (p : Fin (Fintype.card (Fin (k+2) × Fin n)))
    (hlo : k+1 ≤ p.val)
    (hhi : p.val ≤ Fintype.card (Fin (k+2) × Fin n)-(2*(k+1)+1)) :
    let hD : 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) := by
      simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
    let lam := hρ.1.isHermitian.eigenvalues₀
    EntropyHeadConditions (sortedHeadA hD lam (lam p)) (sortedHeadBeta hD lam (lam p)) := by
  classical
  dsimp only
  have hD : 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
  have hfour : 4 ≤ Fintype.card (Fin (k+2) × Fin n) := by omega
  let lam := hρ.1.isHermitian.eigenvalues₀
  have hf : Antitone lam := hρ.1.isHermitian.eigenvalues₀_antitone
  have hn (i) : 0 ≤ lam i := by
    have hi := hρ.1.eigenvalues_nonneg (spectralLabel _ i)
    simpa only [eigenvalues_spectralLabel] using hi
  have ht : 0 < lam p := ordered_pivot_positive hfour lam hf
    (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
    (appt_sorted_rankTwo_linear (by omega) hmn hρ.1.isHermitian happt hfour)
    p (by omega)
  have hs := appt_sorted_shifted_star (h:=k+1) (by omega) hmn hρ happt hD
  dsimp only at hs
  have hb : lam ⟨Fintype.card (Fin (k+2) × Fin n)-(2*(k+1)+1), by omega⟩ ≤ lam p :=
    hf hhi
  have hs' : (∑ i : Fin (k+1),
      (lam (starSlotLabel hD (.inr (.inr (.inr i)))) -
       lam (starSlotLabel hD (.inr (.inr (.inl i)))))^2) ≤
      4*lam (starSlotLabel hD (.inl ()))*lam p :=
    hs.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) (hn _)))
  exact sorted_entropyHead_conditions_from_budget hD lam hf hn (lam p) ht p rfl hlo hhi hs'

theorem density_appt_paper_head_conditions {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    let hD : 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) := by
      simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
    let lam := hρ.1.isHermitian.eigenvalues₀
    let b := lam (paperPivot hmn)
    EntropyHeadConditions (sortedHeadA hD lam b) (sortedHeadBeta hD lam b) := by
  have hp := paper_pivot_rank_bounds hmn
  exact density_appt_head_conditions_at_pivot hmn hρ happt (paperPivot hmn)
    (by simpa [paperPivot] using hp.1) (by simpa [paperPivot] using hp.2.1)


end APPTReview
