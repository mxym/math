import Entry002
open Entry002 Module
def MaximalOnlyTarget : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
  ∀ (b : Basis (Fin 2) ℤ (conductorOrder K 1))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ), 0 ≤ D →
  ∃ B : ℕ,
    (∀ x : PrimeVertex (conductorOrder K 1),
      {y | (primeGraph b e D).Reachable x y}.Finite ∧
      {y | (primeGraph b e D).Reachable x y}.ncard ≤ B) ∧
    (∀ (n : ℕ) (w : Fin n → PrimeVertex (conductorOrder K 1)),
      Function.Injective w →
      (∀ i j : Fin n, j.val = i.val + 1 → (primeGraph b e D).Adj (w i) (w j)) →
      n ≤ B) ∧
    (∀ w : ℕ → PrimeVertex (conductorOrder K 1), Function.Injective w →
      (∀ t, (primeGraph b e D).Adj (w t) (w (t + 1))) → False)

example (h : MaximalOnlyTarget) : MainTarget := h
