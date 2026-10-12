import AbsolutePencil

/-!
# Equality rigidity: zero of the symmetric cubic V

The polynomial V is the exact nonnegative determinant SOS
term in Theorem 2.  This module classifies ALL nonnegative
zeroes without importing any equality-case hypotheses.
-/
namespace ComplexPencilEquality
open ComplexPencilCert

theorem V_zero_support
    (X Y Z : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hZ : 0 ≤ Z) (hV : V X Y Z = 0) :
    (X=Y ∧ Y=Z) ∨ (X=0 ∧ Y=0) ∨
    (X=0 ∧ Z=0) ∨ (Y=0 ∧ Z=0) := by
  have hs :
      X*(Y-Z)^2+Y*(Z-X)^2+Z*(X-Y)^2=0 := by
    rw [← V_sos]
    exact hV
  have ha : 0 ≤ X*(Y-Z)^2 := mul_nonneg hX (sq_nonneg _)
  have hb : 0 ≤ Y*(Z-X)^2 := mul_nonneg hY (sq_nonneg _)
  have hc : 0 ≤ Z*(X-Y)^2 := mul_nonneg hZ (sq_nonneg _)
  have hz1 : X*(Y-Z)^2=0 := by linarith
  have hz2 : Y*(Z-X)^2=0 := by linarith
  have hz3 : Z*(X-Y)^2=0 := by linarith
  by_cases h0 : X=0
  · by_cases h1 : Y=0
    · exact Or.inr (Or.inl ⟨h0,h1⟩)
    · have hSq : (Z-X)^2=0 :=
        (mul_eq_zero.mp hz2).resolve_left h1
      have hZ0 : Z=0 := by nlinarith [hSq]
      exact Or.inr (Or.inr (Or.inl ⟨h0,hZ0⟩))
  · have hSq : (Y-Z)^2=0 :=
      (mul_eq_zero.mp hz1).resolve_left h0
    have hYZ : Y=Z := by nlinarith [hSq]
    by_cases h1 : Y=0
    · exact Or.inr (Or.inr (Or.inr ⟨h1, hYZ ▸ h1⟩))
    · have hSq2 : (Z-X)^2=0 :=
        (mul_eq_zero.mp hz2).resolve_left h1
      have hXZ : X=Z := by nlinarith [hSq2]
      exact Or.inl ⟨hXZ.trans hYZ.symm, hYZ⟩

theorem V_all_positive_equal
    (X Y Z : ℝ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (hV : V X Y Z = 0) :
    X=Y ∧ Y=Z := by
  rcases V_zero_support X Y Z (le_of_lt hX)
      (le_of_lt hY) (le_of_lt hZ) hV with h | h | h | h
  · exact h
  · exact False.elim (not_le_of_gt hX (by rw [h.1]))
  · exact False.elim (not_le_of_gt hX (by rw [h.1]))
  · exact False.elim (not_le_of_gt hY (by rw [h.1]))

#print axioms ComplexPencilEquality.V_zero_support

end ComplexPencilEquality
