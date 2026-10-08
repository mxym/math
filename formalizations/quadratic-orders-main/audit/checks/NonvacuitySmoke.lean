import Entry002.Orders
open Entry002 Module
example : Nonempty (CoeffSpace ≃ₗ[ℝ] Plane) :=
  ⟨(WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm⟩
example (K : Type) [Field K] [NumberField K] (hK : finrank ℚ K = 2)
    (f : ℕ) (hf : 0 < f) : Nonempty (Basis (Fin 2) ℤ (conductorOrder K f)) :=
  ⟨conductorOrderBasis K f hK hf⟩
example (K : Type) [Field K] [NumberField K] (hK : finrank ℚ K = 2) :
    Nonempty (Basis (Fin 2) ℤ (conductorOrder K 2)) :=
  ⟨conductorOrderBasis K 2 hK (by norm_num)⟩
