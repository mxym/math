import BapatDefs

open scoped BigOperators ComplexOrder

set_option autoImplicit false

namespace BapatRankTwo

theorem inversions_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    inversions σ = inversions σ.symm := by
  unfold inversions
  apply Finset.card_bij (fun p _ => (σ p.2, σ p.1))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    simpa using And.intro hp.2 hp.1
  · intro p hp q hq he
    have h1 := σ.injective (congrArg Prod.fst he)
    have h2 := σ.injective (congrArg Prod.snd he)
    exact Prod.ext h2 h1
  · intro q hq
    refine ⟨(σ.symm q.2, σ.symm q.1), ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    simpa using And.intro hq.2 hq.1

theorem permutationWeight_star_of_isHermitian {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (σ : Equiv.Perm (Fin n)) :
    star (∏ i, A i (σ i)) = ∏ i, A i (σ.symm i) := by
  rw [star_prod]
  simp_rw [hA.apply]
  simpa using Equiv.prod_comp σ (fun i => A i (σ.symm i))

/-- Hermitian matrices have real q-permanents at real q; the proof reindexes
the full sum by inverse permutation, which preserves the actual inversion count. -/
theorem qPermanent_star_of_isHermitian {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (q : ℝ) :
    star (qPermanent A (q : ℂ)) = qPermanent A (q : ℂ) := by
  classical
  letI : Fintype (Equiv.Perm (Fin n)) := fintypePerm
  unfold qPermanent
  simp only [star_sum, star_mul, star_pow, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ∑ σ : Equiv.Perm (Fin n),
        (q : ℂ) ^ inversions σ.symm * ∏ i, A i (σ.symm i) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [← Complex.star_def, permutationWeight_star_of_isHermitian hA,
        inversions_symm σ]
      exact mul_comm _ _
    _ = _ := by
      exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
        (fun σ => (q : ℂ) ^ inversions σ * ∏ i, A i (σ i))

theorem qPermanent_eq_ofReal_eval {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (q : ℝ) :
    qPermanent A (q : ℂ) = (((realQPolynomial A).eval q : ℝ) : ℂ) := by
  rw [realQPolynomial_eval]
  exact (Complex.conj_eq_iff_re.mp (qPermanent_star_of_isHermitian hA q)).symm

end BapatRankTwo
