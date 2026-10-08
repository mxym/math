import Mathlib.GroupTheory.Perm.Finite
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Chollet

variable {G X : Type*} [Group G] [Fintype G] [Fintype X]
  [MulAction G X]

def finiteOrbitSum (u : X → ℝ) (x : X) : ℝ :=
  ∑ g : G, u (g • x)

private theorem finiteOrbitSum_smul (u : X → ℝ) (g : G) (x : X) :
    finiteOrbitSum (G := G) u (g • x) = finiteOrbitSum (G := G) u x := by
  simp only [finiteOrbitSum]
  calc
    (∑ h : G, u (h • (g • x))) =
      ∑ h : G, u ((h * g) • x) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [mul_smul]
    _ = ∑ h : G, u (h • x) :=
      Equiv.sum_comp (Equiv.mulRight g) (fun h : G => u (h • x))

private theorem finiteOrbitSum_weighted_reindex
    (u : X → ℝ) (g : G) :
    (∑ x : X, u (g • x) * finiteOrbitSum (G := G) u x) =
      ∑ x : X, u x * finiteOrbitSum (G := G) u x := by
  let e : X ≃ X :=
    { toFun := fun x => g • x
      invFun := fun x => g⁻¹ • x
      left_inv := fun x => inv_smul_smul g x
      right_inv := fun x => smul_inv_smul g x }
  calc
    (∑ x : X, u (g • x) * finiteOrbitSum (G := G) u x) =
      ∑ x : X, u (g • x) * finiteOrbitSum (G := G) u (g • x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [finiteOrbitSum_smul]
    _ = ∑ x : X, u x * finiteOrbitSum (G := G) u x :=
      Equiv.sum_comp e (fun x : X => u x * finiteOrbitSum (G := G) u x)

theorem finiteOrbit_correlation_nonneg (u : X → ℝ) :
    0 ≤ ∑ x : X, u x * finiteOrbitSum (G := G) u x := by
  let T : ℝ := ∑ x : X, u x * finiteOrbitSum (G := G) u x
  have hid :
      (∑ x : X, (finiteOrbitSum (G := G) u x)^2) =
        (Fintype.card G : ℝ) * T := by
    calc
      (∑ x : X, (finiteOrbitSum (G := G) u x)^2) =
        ∑ x : X, (∑ g : G, u (g • x)) * finiteOrbitSum (G := G) u x := by
          apply Finset.sum_congr rfl
          intro x _
          simp [finiteOrbitSum, pow_two]
      _ = ∑ x : X, ∑ g : G, u (g • x) * finiteOrbitSum (G := G) u x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
      _ = ∑ g : G, ∑ x : X, u (g • x) * finiteOrbitSum (G := G) u x := by
          rw [Finset.sum_comm]
      _ = ∑ g : G, T := by
          apply Finset.sum_congr rfl
          intro g _
          exact finiteOrbitSum_weighted_reindex u g
      _ = (Fintype.card G : ℝ) * T := by
          simp [T, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hpos : 0 ≤ (∑ x : X, (finiteOrbitSum (G := G) u x)^2) := by
    apply Finset.sum_nonneg
    intro x _
    positivity
  have hcard : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty G)
  change 0 ≤ T
  nlinarith [hid]

end Chollet

#print axioms Chollet.finiteOrbit_correlation_nonneg
