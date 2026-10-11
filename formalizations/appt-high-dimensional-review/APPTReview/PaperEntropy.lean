import APPTReview.SortedEntropy

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Actual ordered APPT eigenvalues control the nonlinear head at every valid
lower-tail pivot. No permutation, graph constraint, or sign premise is supplied. -/
theorem density_appt_entropyHead_at_pivot {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A)
    (p : Fin (Fintype.card (Fin (k+2) × Fin n)))
    (hlo : k+1 ≤ p.val)
    (hhi : p.val ≤ Fintype.card (Fin (k+2) × Fin n)-(2*(k+1)+1)) :
    let hD : 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) := by
      simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
    let lam := hρ.1.isHermitian.eigenvalues₀
    entropyHead (sortedHeadA hD lam (lam p)) (sortedHeadBeta hD lam (lam p)) ≤ 2 := by
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
  exact sorted_entropyHead_from_budget hD lam hf hn (lam p) ht p rfl hlo hhi hs'

/-- The paper pivot lies in the admissible range in every rectangular dimension.
All cardinal inequalities, including the floor in m(m+1)/2, are discharged here. -/
theorem paper_pivot_rank_bounds {k n : ℕ} (hmn : k+2 ≤ n) :
    let D := (k+2)*n
    let S := (k+2)*(k+3)/2
    k+1 ≤ D-S ∧ D-S ≤ D-(2*(k+1)+1) ∧ D-S < D := by
  dsimp only
  have hmul := Nat.mul_le_mul_left (k+2) hmn
  have hdiv := Nat.div_mul_le_self ((k+2)*(k+3)) 2
  have hlow : 2*(2*(k+1)+1) ≤ (k+2)*(k+3) := by nlinarith
  have hslo : 2*(k+1)+1 ≤ (k+2)*(k+3)/2 := by omega
  have hshi : (k+2)*(k+3)/2+(k+1) ≤ (k+2)*n := by nlinarith
  omega

def paperPivot {k n : ℕ} (hmn : k+2 ≤ n) :
    Fin (Fintype.card (Fin (k+2) × Fin n)) :=
  ⟨Fintype.card (Fin (k+2) × Fin n)-(k+2)*(k+3)/2,
    by simpa using (paper_pivot_rank_bounds hmn).2.2⟩

/-- Entropy proof E9 for the genuine sorted spectrum with EXACTLY the pivot
b=lambda_(D-m(m+1)/2+1) of the paper (indices there are one-based).
The only hypotheses are local dimensions, density, and all-unitary APPT. -/
theorem density_appt_paper_entropyHead {k n : ℕ} (hmn : k+2 ≤ n)
    {A : Matrix (Fin (k+2) × Fin n) (Fin (k+2) × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    let hD : 3*(k+1)+1 ≤ Fintype.card (Fin (k+2) × Fin n) := by
      simp only [Fintype.card_prod, Fintype.card_fin]; nlinarith
    let lam := hρ.1.isHermitian.eigenvalues₀
    let b := lam (paperPivot hmn)
    entropyHead (sortedHeadA hD lam b) (sortedHeadBeta hD lam b) ≤ 2 := by
  have hp := paper_pivot_rank_bounds hmn
  exact density_appt_entropyHead_at_pivot hmn hρ happt (paperPivot hmn)
    (by simpa [paperPivot] using hp.1) (by simpa [paperPivot] using hp.2.1)

end APPTReview