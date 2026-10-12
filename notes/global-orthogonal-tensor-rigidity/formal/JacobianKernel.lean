import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
The algebraic part of Lemma 3, after extraction of the constant and first
spatial Taylor coefficients. This does not formalize spectral calculus,
the H⁻¹ coercivity argument, transport, or the entropy hypothesis R.

linearComm is the entrywise formula for
[e_r e_rᵀ,H_s] + [H_r,e_s e_sᵀ].
The last hypothesis is the diagonal part of DB at the coordinate tensor.
-/

namespace QuantitativeJacobian

variable {ι : Type*} [DecidableEq ι]

def linearComm (H : ι → ι → ι → ℝ) (r s i j : ι) : ℝ :=
  (if i = r then H s r j else 0) -
  (if j = r then H s i r else 0) +
  (if j = s then H r i s else 0) -
  (if i = s then H r s j else 0)

def fullySymmetric (H : ι → ι → ι → ℝ) : Prop :=
  (∀ i j k, H i j k = H j i k) ∧
  (∀ i j k, H i j k = H i k j)

def rotationTensor (K : ι → ι → ℝ) (i j k : ι) : ℝ :=
  if i = j then K k i else if i = k then K j i
  else if j = k then K i j else 0

theorem distinct_zero
    (H : ι → ι → ι → ℝ) (hs : fullySymmetric H)
    (hc : ∀ r s i j, linearComm H r s i j = 0)
    {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    H a b c = 0 := by
  have h := hc a b a c
  simp [linearComm, hab, Ne.symm hac, Ne.symm hbc] at h
  rw [hs.1 a b c]
  exact h

theorem repeated_sum_zero
    (H : ι → ι → ι → ℝ) (hs : fullySymmetric H)
    (hc : ∀ r s i j, linearComm H r s i j = 0)
    {a b : ι} (hab : a ≠ b) :
    H a a b + H a b b = 0 := by
  have h := hc a b a b
  simp [linearComm, hab, Ne.symm hab] at h
  have hp : H b a b = H a b b := hs.1 b a b
  linarith

theorem derivative_kernel_is_rotation
    (H : ι → ι → ι → ℝ) (hs : fullySymmetric H)
    (hc : ∀ r s i j, linearComm H r s i j = 0)
    (hn : ∀ i, H i i i + H i i i = 0) :
    ∃ K : ι → ι → ℝ,
      (∀ i j, K i j = -K j i) ∧
      (∀ i j k, H i j k = rotationTensor K i j k) := by
  have hz : ∀ i, H i i i = 0 := by
    intro i
    have h := hn i
    linarith
  let K : ι → ι → ℝ := fun i j => H j j i
  refine ⟨K, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst j
      simp [K, hz i]
    · have h := repeated_sum_zero H hs hc hij
      have hp : H i j j = H j j i := by
        rw [hs.1 i j j, hs.2 j i j]
      dsimp [K]
      linarith
  · intro i j k
    by_cases hij : i = j
    · subst j
      simp [rotationTensor, K]
    · by_cases hik : i = k
      · subst k
        simp [rotationTensor, K, hij, hs.2 i j i]
      · by_cases hjk : j = k
        · subst k
          have hp : H i j j = H j j i := by
            rw [hs.1 i j j, hs.2 j i j]
          simp [rotationTensor, K, hij, hp]
        · simp [rotationTensor, hij, hik, hjk,
            distinct_zero H hs hc hij hik hjk]

#print axioms distinct_zero
#print axioms repeated_sum_zero
#print axioms derivative_kernel_is_rotation

end QuantitativeJacobian
