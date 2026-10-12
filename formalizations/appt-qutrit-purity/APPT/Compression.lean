import APPT.Core

open scoped BigOperators
namespace APPT

/-- Exact endpoint population compression; no integrality is imposed on t and z. -/
theorem endpoint_compression {M : ℕ} (x : Fin M → ℝ) (a b : ℝ)
    (hab : b ≤ a) (hx : ∀ i, b ≤ x i ∧ x i ≤ a) :
    ∃ t z : ℝ, 0 ≤ t ∧ 0 ≤ z ∧ t + z = (M : ℝ) ∧
      (∑ i, x i) = t*a + z*b ∧
      (∑ i, (x i)^2) ≤ t*a^2 + z*b^2 := by
  have hlo : (M : ℝ)*b ≤ ∑ i, x i := by
    calc
      (M : ℝ)*b = ∑ _i : Fin M, b := by simp
      _ ≤ ∑ i, x i := Finset.sum_le_sum (fun i _ => (hx i).1)
  have hhi : (∑ i, x i) ≤ (M : ℝ)*a := by
    calc
      (∑ i, x i) ≤ ∑ _i : Fin M, a :=
        Finset.sum_le_sum (fun i _ => (hx i).2)
      _ = (M : ℝ)*a := by simp
  have hsq : (∑ i, (x i)^2) ≤
      (a+b)*(∑ i, x i) - (M : ℝ)*a*b := by
    calc
      (∑ i, (x i)^2) ≤ ∑ i, ((a+b)*x i-a*b) := by
        apply Finset.sum_le_sum
        intro i _
        have h := mul_nonneg (sub_nonneg.mpr (hx i).2)
          (sub_nonneg.mpr (hx i).1)
        nlinarith
      _ = (a+b)*(∑ i, x i) - (M : ℝ)*a*b := by
        simp [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  by_cases he : a = b
  · subst a
    have heq : (∑ i, x i) = (M : ℝ)*b := le_antisymm hhi hlo
    refine ⟨0, (M : ℝ), le_rfl, Nat.cast_nonneg M, by ring, ?_, ?_⟩
    · simpa using heq
    · rw [heq] at hsq
      nlinarith
  · have hd : 0 < a-b := sub_pos.mpr (lt_of_le_of_ne hab (Ne.symm he))
    let t : ℝ := ((∑ i, x i)-(M : ℝ)*b)/(a-b)
    let z : ℝ := (M : ℝ)-t
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) (le_of_lt hd)
    have hta : t*(a-b) = (∑ i, x i)-(M : ℝ)*b := by
      dsimp [t]
      exact div_mul_cancel₀ _ (ne_of_gt hd)
    have htM : t ≤ (M : ℝ) := by
      dsimp [t]
      apply (div_le_iff₀ hd).mpr
      nlinarith
    have hz : 0 ≤ z := sub_nonneg.mpr htM
    have htz : t+z = (M : ℝ) := by dsimp [z]; ring
    have heq : (∑ i, x i) = t*a+z*b := by dsimp [z]; nlinarith [hta]
    refine ⟨t,z,ht,hz,htz,heq,?_⟩
    rw [heq] at hsq
    have hid : (a+b)*(t*a+z*b)-(M : ℝ)*a*b = t*a^2+z*b^2 := by
      rw [← htz]
      ring
    rwa [hid] at hsq

end APPT
