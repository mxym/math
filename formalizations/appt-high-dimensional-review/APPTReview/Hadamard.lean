import APPTReview.Basic

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def halfRoot : ℂ := (Real.sqrt ((1 : ℝ)/2) : ℂ)
@[simp] theorem halfRoot_star : star halfRoot = halfRoot := by simp [halfRoot]
@[simp] theorem halfRoot_sq : halfRoot^2 = (1/2 : ℂ) := by
  norm_cast
  norm_num [halfRoot, ← Complex.ofReal_pow, Real.sq_sqrt]
@[simp] theorem halfRoot_conj : (starRingEnd ℂ) halfRoot = halfRoot := halfRoot_star

variable {a : Type*} [Fintype a] [LinearOrder a]

/-- Simultaneous real Hadamard rotations on every off-diagonal coordinate pair.
Unlike the previous qutrit corner this construction has arbitrary finite dimension. -/
noncomputable def hadamard : Matrix (a × a) (a × a) ℂ := fun p q =>
  if p.1 = p.2 then (if p = q then 1 else 0)
  else (if p = q then (if p.1 < p.2 then halfRoot else -halfRoot) else 0) +
       (if p.swap = q then halfRoot else 0)

theorem hadamard_mul_apply {κ : Type*} (B : Matrix (a × a) κ ℂ)
    (i j : a) (q : κ) :
    (hadamard (a := a) * B) (i,j) q =
      if i=j then B (i,j) q
      else (if i<j then halfRoot else -halfRoot) * B (i,j) q +
        halfRoot * B (j,i) q := by
  classical
  by_cases h : i=j
  · simp [Matrix.mul_apply, hadamard, h]
  · simp [Matrix.mul_apply, hadamard, h, add_mul, Finset.sum_add_distrib]

theorem hadamard_conjTranspose : (hadamard (a := a))ᴴ = hadamard := by
  classical
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hij : i=j
  · subst j
    by_cases hki : k=i
    · subst k
      by_cases hli : l=i <;> simp_all [hadamard, Matrix.conjTranspose_apply, eq_comm]
    · by_cases hkl : k=l <;> simp_all [hadamard, Matrix.conjTranspose_apply, eq_comm]
  · by_cases hkl : k=l
    · subst l
      by_cases hik : i=k <;> simp_all [hadamard, Matrix.conjTranspose_apply, eq_comm]
    · by_cases hik : i=k <;> by_cases hjl : j=l <;>
        by_cases hil : i=l <;> by_cases hjk : j=k <;>
        simp_all [hadamard, Matrix.conjTranspose_apply, eq_comm]
  all_goals split_ifs <;> simp only [map_neg, halfRoot_conj]

theorem hadamard_sq : (hadamard (a := a)) * hadamard = 1 := by
  classical
  ext ⟨i,j⟩ ⟨k,l⟩
  rw [hadamard_mul_apply]
  by_cases hij : i = j
  · subst j; simp [hadamard, Matrix.one_apply]
  · have hji : j ≠ i := Ne.symm hij
    have hboth : ¬ ((i,j) = (k,l) ∧ (j,i) = (k,l)) := by
      rintro ⟨h1,h2⟩
      exact hij (congrArg Prod.fst (h1.trans h2.symm))
    by_cases hlt : i < j
    · have hn : ¬ (j < i) := not_lt_of_gt hlt
      by_cases h1 : (i,j) = (k,l) <;> by_cases h2 : (j,i) = (k,l)
      · exact (hboth ⟨h1,h2⟩).elim
      all_goals
        simp [hadamard, hij, hji, hlt, hn, h1, h2, Matrix.one_apply]
        <;> ring_nf <;> norm_num
    · have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hji
      by_cases h1 : (i,j) = (k,l) <;> by_cases h2 : (j,i) = (k,l)
      · exact (hboth ⟨h1,h2⟩).elim
      all_goals
        simp [hadamard, hij, hji, hlt, hjlt, h1, h2, Matrix.one_apply]
        <;> ring_nf <;> norm_num

noncomputable def hadamardUnitary : Matrix.unitaryGroup (a × a) ℂ :=
  ⟨hadamard, by
    constructor <;> simpa only [Matrix.star_eq_conjTranspose,
      hadamard_conjTranspose] using (hadamard_sq (a := a))⟩
end APPTReview
