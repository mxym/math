import OperationalCompletion.NestedProjection

open scoped BigOperators
namespace OperationalCompletion

def weightedDifference (J : ℕ) (w F : ℕ → ℝ) : ℝ :=
  ∑ j : Fin J, w j * (F (j+1)-F j)

/-- Summation by parts includes the two boundary terms, even for zero levels. -/
theorem weightedDifference_abel (J : ℕ) (w F : ℕ → ℝ) :
    weightedDifference J w F = w J*F J - w 0*F 0 +
      ∑ j : Fin J, (w j-w (j+1))*F (j+1) := by
  induction J with
  | zero => simp [weightedDifference]
  | succ J ih =>
    unfold weightedDifference at ih ⊢
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last]
    rw [ih]
    ring

theorem weightedDifference_mono (J : ℕ) (w F G : ℕ → ℝ)
    (hw : 0 ≤ w J) (hdec : ∀ j < J,w (j+1) ≤ w j)
    (hF0 : F 0=0) (hG0 : G 0=0) (hFG : ∀ j ≤ J,G j≤F j) :
    weightedDifference J w G ≤ weightedDifference J w F := by
  rw [weightedDifference_abel,weightedDifference_abel,hF0,hG0]
  simp only [mul_zero,sub_zero]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hFG J le_rfl) hw
  · apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hFG (j+1) (by omega))
      (sub_nonneg.mpr (hdec j j.isLt))

theorem weightedDifference_length_mono (w G : ℕ → ℝ)
    (hw : ∀ j,0≤w j) (hG : Monotone G) :
    Monotone (fun J => weightedDifference J w G) := by
  apply monotone_nat_of_le_succ
  intro J
  unfold weightedDifference
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  exact le_add_of_nonneg_right (mul_nonneg (hw J) (sub_nonneg.mpr (hG (by omega))))

/-- A decreasing soft profile retains every lower prefix guarantee. -/
theorem weightedDifference_lower_prefix (J l : ℕ) (hl : l<J) (w G : ℕ → ℝ)
    (hw : ∀ j,0≤w j) (hdec : Antitone w) (hG : Monotone G) (hG0 : G 0=0) :
    w l*G (l+1) ≤ weightedDifference J w G := by
  have hconst : weightedDifference (l+1) (fun _ => w l) G = w l*G (l+1) := by
    rw [weightedDifference_abel,hG0]
    simp
  calc
    _ = weightedDifference (l+1) (fun _ => w l) G := hconst.symm
    _ ≤ weightedDifference (l+1) w G := by
      unfold weightedDifference
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hdec (by omega : (j:ℕ)≤l))
        (sub_nonneg.mpr (hG (by omega)))
    _ ≤ _ := weightedDifference_length_mono w G hw hG (by omega)

end OperationalCompletion
