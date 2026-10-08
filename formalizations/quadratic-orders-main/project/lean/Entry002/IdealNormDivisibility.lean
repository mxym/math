import Entry002.IdealNormCoefficient

namespace Entry002

open NumberField Ideal
open scoped NumberField Classical

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The finite norm fiber has the same cardinality as the raw zeta coefficient. -/
theorem idealNormFiber_card (n : ℕ) :
    (idealNormFiber K n).card = idealNormCount K n := by
  unfold idealNormCount
  have hcard := Nat.card_congr
    (Equiv.subtypeEquivRight (fun I => mem_idealNormFiber K n I))
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hcard
  exact hcard

/-- Norm zero contains precisely the zero ideal. -/
@[simp] theorem idealNormCount_zero : idealNormCount K 0 = 1 := by
  rw [← idealNormFiber_card]
  have hset : idealNormFiber K 0 = {⊥} := by
    ext I
    simp [Ideal.absNorm_eq_zero_iff]
  rw [hset, Finset.card_singleton]

/-- Norm one contains precisely the unit ideal. -/
@[simp] theorem idealNormCount_one : idealNormCount K 1 = 1 := by
  rw [← idealNormFiber_card]
  have hset : idealNormFiber K 1 = {⊤} := by
    ext I
    simp [Ideal.absNorm_eq_one_iff]
  rw [hset, Finset.card_singleton]

@[simp] theorem idealNormCoefficient_zero : idealNormCoefficient K 0 = 1 := by
  simp [idealNormCoefficient]

@[simp] theorem idealNormCoefficient_one : idealNormCoefficient K 1 = 1 := by
  simp [idealNormCoefficient]

/-- Multiplication by a nonzero ideal identifies a quotient norm fiber with
the norm fiber consisting of its integral ideal multiples. -/
def idealNormMulEquiv (n : ℕ) (A : Ideal (𝓞 K)) (hA : A ≠ ⊥)
    (hdiv : Ideal.absNorm A ∣ n) :
    {J : Ideal (𝓞 K) // Ideal.absNorm J = n / Ideal.absNorm A} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n ∧ A ∣ I} where
  toFun J := ⟨A * J.1, by
    constructor
    · simpa only [map_mul, J.2] using Nat.mul_div_cancel' hdiv
    · exact ⟨J.1, rfl⟩⟩
  invFun I := ⟨Classical.choose I.2.2, by
    have hpos : 0 < Ideal.absNorm A := by
      exact Nat.pos_of_ne_zero (fun h => hA (Ideal.absNorm_eq_zero_iff.mp h))
    have hnorm : Ideal.absNorm A * Ideal.absNorm (Classical.choose I.2.2) = n := by
      rw [← map_mul, ← Classical.choose_spec I.2.2]
      exact I.2.1
    calc
      Ideal.absNorm (Classical.choose I.2.2) =
          (Ideal.absNorm A * Ideal.absNorm (Classical.choose I.2.2)) /
            Ideal.absNorm A := (Nat.mul_div_cancel_left _ hpos).symm
      _ = n / Ideal.absNorm A := congrArg (fun m => m / Ideal.absNorm A) hnorm⟩
  left_inv J := by
    apply Subtype.ext
    apply mul_left_cancel₀ hA
    exact (Classical.choose_spec (show A ∣ A * J.1 from ⟨J.1, rfl⟩)).symm
  right_inv I := by
    apply Subtype.ext
    exact (Classical.choose_spec I.2.2).symm

/-- The count of multiples retains a divisibility guard, including when the
raw quotient coefficient at zero would otherwise be nonzero. -/
theorem idealNormFiber_card_divisible {n : ℕ} (_hn : 0 < n)
    (A : Ideal (𝓞 K)) (hA : A ≠ ⊥) :
    ((idealNormFiber K n).filter (fun I => A ∣ I)).card =
      if Ideal.absNorm A ∣ n then idealNormCount K (n / Ideal.absNorm A) else 0 := by
  let s := (idealNormFiber K n).filter (fun I => A ∣ I)
  by_cases hdiv : Ideal.absNorm A ∣ n
  · rw [ite_eq_left hdiv]
    have hcard := Nat.card_congr (idealNormMulEquiv K n A hA hdiv)
    change s.card = _
    unfold idealNormCount
    rw [hcard]
    have hcardSet := Nat.card_congr (Equiv.subtypeEquivRight
      (fun I => show I ∈ s ↔ Ideal.absNorm I = n ∧ A ∣ I by simp [s]))
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hcardSet
    exact hcardSet
  · rw [ite_eq_right hdiv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro I hI
    obtain ⟨hnorm, hAI⟩ := by simpa using hI
    apply hdiv
    rw [← hnorm]
    exact map_dvd Ideal.absNorm hAI

/-- Weighted counts over the actual ideal fiber, in the form used by the
finite logarithmic convolution. -/
theorem idealNormFiber_sum_divisible {n : ℕ} (hn : 0 < n)
    (A : Ideal (𝓞 K)) (hA : A ≠ ⊥) (c : ℝ) :
    (∑ I ∈ idealNormFiber K n, if A ∣ I then c else 0) =
      (if Ideal.absNorm A ∣ n then idealNormCoefficient K (n / Ideal.absNorm A)
        else 0) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
    idealNormFiber_card_divisible K hn A hA]
  split_ifs <;> simp [idealNormCoefficient]

end
end Entry002
