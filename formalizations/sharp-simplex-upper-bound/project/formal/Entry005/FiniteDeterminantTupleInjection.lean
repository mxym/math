import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic

noncomputable section
open scoped BigOperators

namespace Entry005

/-- Repeated atom indices give repeated actual columns and therefore zero determinant. -/
theorem tuple_determinant_eq_zero_of_not_injective {ι : Type*} {d : ℕ}
    (v : ι → Fin d → ℝ) (σ : Fin d → ι) (hσ : ¬Function.Injective σ) :
    (Matrix.of (fun i j => v (σ j) i)).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hσ
  apply Matrix.det_zero_of_column_eq hne
  intro k
  simp only [Matrix.of_apply, hij]

/-- Even with arbitrary tuple weights, only injective atom tuples contribute. -/
theorem fintype_weighted_determinant_tuple_sum_eq_injection_sum {ι : Type*} [Fintype ι]
    {d : ℕ} (v : ι → Fin d → ℝ) (weight : (Fin d → ι) → ℝ) :
    (∑ σ : Fin d → ι, weight σ * |(Matrix.of (fun i j => v (σ j) i)).det|) =
      ∑ σ : Fin d ↪ ι, weight σ * |(Matrix.of (fun i j => v (σ j) i)).det| := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype Function.Injective]
  have hbad : (∑ σ : {σ : Fin d → ι // ¬Function.Injective σ},
      weight σ.val * |(Matrix.of (fun i j => v (σ.val j) i)).det|) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    rw [tuple_determinant_eq_zero_of_not_injective v σ.val σ.property,
      abs_zero, mul_zero]
  rw [hbad, add_zero]
  apply Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin d) ι)
  intro σ
  rfl

theorem fintype_determinant_tuple_sum_eq_injection_sum {ι : Type*} [Fintype ι]
    {d : ℕ} (v : ι → Fin d → ℝ) :
    (∑ σ : Fin d → ι, |(Matrix.of (fun i j => v (σ j) i)).det|) =
      ∑ σ : Fin d ↪ ι, |(Matrix.of (fun i j => v (σ j) i)).det| := by
  simpa only [one_mul] using
    fintype_weighted_determinant_tuple_sum_eq_injection_sum v (fun _ => 1)

theorem finite_tuple_determinant_eq_zero_of_not_injective {d m : ℕ}
    (v : Fin m → Fin d → ℝ) (σ : Fin d → Fin m) (hσ : ¬Function.Injective σ) :
    (Matrix.of (fun i j => v (σ j) i)).det = 0 :=
  tuple_determinant_eq_zero_of_not_injective v σ hσ

theorem finite_weighted_determinant_tuple_sum_eq_injection_sum {d m : ℕ}
    (v : Fin m → Fin d → ℝ) (weight : (Fin d → Fin m) → ℝ) :
    (∑ σ : Fin d → Fin m, weight σ * |(Matrix.of (fun i j => v (σ j) i)).det|) =
      ∑ σ : Fin d ↪ Fin m, weight σ * |(Matrix.of (fun i j => v (σ j) i)).det| :=
  fintype_weighted_determinant_tuple_sum_eq_injection_sum v weight

theorem finite_determinant_tuple_sum_eq_injection_sum {d m : ℕ}
    (v : Fin m → Fin d → ℝ) :
    (∑ σ : Fin d → Fin m, |(Matrix.of (fun i j => v (σ j) i)).det|) =
      ∑ σ : Fin d ↪ Fin m, |(Matrix.of (fun i j => v (σ j) i)).det| :=
  fintype_determinant_tuple_sum_eq_injection_sum v

end Entry005
