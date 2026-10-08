import Entry002
open Entry002 Module
def NcardOnlyTarget : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
  ∀ (f : ℕ), 0 < f →
  ∀ (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ), 0 ≤ D →
  ∃ B : ℕ,
    (∀ x : PrimeVertex (conductorOrder K f),
      {y | (primeGraph b e D).Reachable x y}.ncard ≤ B) ∧
    (∀ (n : ℕ) (w : Fin n → PrimeVertex (conductorOrder K f)),
      Function.Injective w →
      (∀ i j : Fin n, j.val = i.val + 1 → (primeGraph b e D).Adj (w i) (w j)) →
      n ≤ B) ∧
    (∀ w : ℕ → PrimeVertex (conductorOrder K f), Function.Injective w →
      (∀ t, (primeGraph b e D).Adj (w t) (w (t + 1))) → False)

example (h : NcardOnlyTarget) : MainTarget := h
