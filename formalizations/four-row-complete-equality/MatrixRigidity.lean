import CriticalProducts
open scoped BigOperators ComplexConjugate
namespace FourRowTradeoff
noncomputable section

/-- A genuine outer product, with nonzero factors and equimodular columns. -/
def IsFlatRankOne (A : Mat) : Prop :=
  ∃ u v : Row, (∀ i, u i ≠ 0) ∧ (∀ j, v j ≠ 0) ∧
    (∀ j, Complex.normSq (v j) = Complex.normSq (v 0)) ∧
    ∀ i j, A i j = u i * v j

/-- Exactly one nonzero entry in each row and each column. -/
def IsMonomial (A : Mat) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), ∀ i,
    A i (σ i) ≠ 0 ∧ ∀ j, j ≠ σ i → A i j = 0

def DisjointRows (A : Mat) : Prop :=
  ∀ i j, i ≠ j → ∀ k, A i k = 0 ∨ A j k = 0

theorem monomial_of_disjoint_rows (A : Mat) (hn : NonzeroRows A)
    (hd : DisjointRows A) : IsMonomial A := by
  classical
  choose f hf using hn
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hij
    rcases hd i j hij (f i) with h | h
    · exact hf i h
    · exact hf j (by simpa only [he] using h)
  let σ : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨σ, ?_⟩
  intro i
  refine ⟨hf i, ?_⟩
  intro j hj
  obtain ⟨r, hr⟩ := σ.surjective j
  have hir : i ≠ r := by
    intro he
    subst r
    exact hj hr.symm
  rcases hd i r hir j with h | h
  · exact h
  · exact False.elim (hf r (by simpa only [show f r = j from hr] using h))

theorem flat_nonzero_rows (A : Mat) (h : IsFlatRankOne A) : NonzeroRows A := by
  obtain ⟨u,v,hu,hv,_,hA⟩ := h
  intro i
  exact ⟨0, by rw [hA]; exact mul_ne_zero (hu i) (hv 0)⟩

theorem monomial_nonzero_rows (A : Mat) (h : IsMonomial A) : NonzeroRows A := by
  obtain ⟨σ,hσ⟩ := h
  exact fun i => ⟨σ i, (hσ i).1⟩

/-- An intersecting row pair with constant products has full support. -/
theorem full_support_of_intersection (A : Mat) (hp : ConstantRowProducts A)
    (i j k : Fin 4) (hij : i ≠ j) (hi : A i k ≠ 0) (hj : A j k ≠ 0) :
    ∀ l, A i l ≠ 0 ∧ A j l ≠ 0 := by
  intro l
  have hprod : A i l * conj (A j l) = A i k * conj (A j k) :=
    (hp i j hij l).trans (hp i j hij k).symm
  have hnprod : A i l * conj (A j l) ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hi (by simpa using hj)
  constructor
  · intro h; exact hnprod (by simp [h])
  · intro h; exact hnprod (by simp [h])

theorem full_support_of_not_disjoint (A : Mat) (hn : NonzeroRows A)
    (hp : ConstantRowProducts A) (hd : ¬ DisjointRows A) :
    ∀ i j, A i j ≠ 0 := by
  classical
  simp only [DisjointRows, not_forall, not_or] at hd
  obtain ⟨i,j,hij,k,hi,hj⟩ := hd
  have hifull := full_support_of_intersection A hp i j k hij hi hj
  intro r l
  by_cases hri : r = i
  · subst r; exact (hifull l).1
  · obtain ⟨t,hrt⟩ := hn r
    exact (full_support_of_intersection A hp r i t hri hrt (hifull t).1 l).1

theorem product_normSq_constant (A : Mat) (hp : ConstantRowProducts A)
    (i j : Fin 4) (hij : i ≠ j) (k : Fin 4) :
    Complex.normSq (A i k) * Complex.normSq (A j k) =
      Complex.normSq (A i 0) * Complex.normSq (A j 0) := by
  simpa only [Complex.normSq_mul, Complex.normSq_conj] using
    congrArg Complex.normSq (hp i j hij k)

/-- Three fully supported rows force the first row to be equimodular. -/
theorem first_row_equimodular (A : Mat) (hp : ConstantRowProducts A)
    (hf : ∀ i j, A i j ≠ 0) :
    ∀ k, Complex.normSq (A 0 k) = Complex.normSq (A 0 0) := by
  intro k
  have h01 := product_normSq_constant A hp 0 1 (by decide) k
  have h02 := product_normSq_constant A hp 0 2 (by decide) k
  have h12 := product_normSq_constant A hp 1 2 (by decide) k
  have hne : Complex.normSq (A 1 0)*Complex.normSq (A 2 0) ≠ 0 := by
    apply mul_ne_zero <;> intro h
    · exact hf 1 0 (Complex.normSq_eq_zero.mp h)
    · exact hf 2 0 (Complex.normSq_eq_zero.mp h)
  have hs : Complex.normSq (A 0 k)^2 *
      (Complex.normSq (A 1 0)*Complex.normSq (A 2 0)) =
      Complex.normSq (A 0 0)^2 *
      (Complex.normSq (A 1 0)*Complex.normSq (A 2 0)) := by
    calc
      _ = Complex.normSq (A 0 k)^2 *
          (Complex.normSq (A 1 k)*Complex.normSq (A 2 k)) := by rw [h12]
      _ = (Complex.normSq (A 0 k)*Complex.normSq (A 1 k)) *
          (Complex.normSq (A 0 k)*Complex.normSq (A 2 k)) := by ring
      _ = _ := by rw [h01,h02]; ring
  have hs' := mul_right_cancel₀ hne hs
  exact le_antisymm
    ((sq_le_sq₀ (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)).mp hs'.le)
    ((sq_le_sq₀ (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)).mp hs'.symm.le)

/-- Constant conjugate products recover an actual rank-one factorization. -/
theorem flat_of_full_support (A : Mat) (hp : ConstantRowProducts A)
    (hf : ∀ i j, A i j ≠ 0) : IsFlatRankOne A := by
  have hv := first_row_equimodular A hp hf
  refine ⟨fun i => A i 0 / A 0 0, A 0,
    (fun i => div_ne_zero (hf i 0) (hf 0 0)), hf 0, hv, ?_⟩
  intro i k
  by_cases hi : i = 0
  · subst i; simp [div_self (hf 0 0)]
  · apply mul_right_cancel₀ (show conj (A 0 k) ≠ 0 by simpa using hf 0 k)
    have hm : A 0 k * conj (A 0 k) = A 0 0 * conj (A 0 0) := by
      rw [Complex.mul_conj, Complex.mul_conj, hv k]
    calc
      A i k * conj (A 0 k) = A i 0 * conj (A 0 0) := hp i 0 hi k
      _ = (A i 0 / A 0 0) * (A 0 0 * conj (A 0 0)) := by
        rw [← mul_assoc, div_mul_cancel₀ _ (hf 0 0)]
      _ = (A i 0 / A 0 0) * (A 0 k * conj (A 0 k)) := by rw [hm]
      _ = ((A i 0 / A 0 0) * A 0 k) * conj (A 0 k) := by ring

/-- The critical structural dichotomy is proved, not assumed. -/
theorem constant_products_dichotomy (A : Mat) (hn : NonzeroRows A)
    (hp : ConstantRowProducts A) : IsFlatRankOne A ∨ IsMonomial A := by
  classical
  by_cases hd : DisjointRows A
  · exact Or.inr (monomial_of_disjoint_rows A hn hd)
  · exact Or.inl (flat_of_full_support A hp (full_support_of_not_disjoint A hn hp hd))

#print axioms constant_products_dichotomy
end
end FourRowTradeoff
