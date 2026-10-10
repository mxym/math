import APPTReview.Basic

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

noncomputable def halfRoot : ℂ := (Real.sqrt ((1 : ℝ)/2) : ℂ)
@[simp] theorem halfRoot_star : star halfRoot = halfRoot := by simp [halfRoot]
@[simp] theorem halfRoot_sq : halfRoot^2 = (1/2 : ℂ) := by
  change ((Real.sqrt ((1 : ℝ)/2) : ℂ))^2 = (1/2 : ℂ)
  norm_cast
  norm_num [Real.sq_sqrt]

variable {a : Type*} [Fintype a] [LinearOrder a]

noncomputable def diagWeight (p : a × a) : ℂ :=
  if p.1 = p.2 then 1 else if p.1 < p.2 then halfRoot else -halfRoot
noncomputable def swapWeight (p : a × a) : ℂ :=
  if p.1 = p.2 then 0 else halfRoot

@[simp] theorem diagWeight_star (p : a × a) : star (diagWeight p) = diagWeight p := by
  unfold diagWeight
  split_ifs <;> simp
@[simp] theorem swapWeight_star (p : a × a) : star (swapWeight p) = swapWeight p := by
  unfold swapWeight
  split_ifs <;> simp
@[simp] theorem swapWeight_swap (p : a × a) : swapWeight p.swap = swapWeight p := by
  simp [swapWeight, eq_comm]

theorem diagWeight_swap {p : a × a} (hp : p.1 ≠ p.2) :
    diagWeight p.swap = -diagWeight p := by
  rcases p with ⟨i,j⟩
  dsimp at hp
  rcases lt_or_gt_of_ne hp with hij | hji
  · simp [diagWeight, hp, Ne.symm hp, hij, not_lt_of_gt hij]
  · simp [diagWeight, hp, Ne.symm hp, hji, not_lt_of_gt hji]

theorem weight_squares (p : a × a) : diagWeight p * diagWeight p +
    swapWeight p * swapWeight p = 1 := by
  by_cases hp : p.1 = p.2
  · simp [diagWeight, swapWeight, hp]
  · simp only [diagWeight, swapWeight, hp, ite_false]
    have hs : halfRoot * halfRoot = (1/2 : ℂ) := by
      simpa only [pow_two] using halfRoot_sq
    split_ifs <;> norm_num [neg_mul_neg, hs]

/-- Real Hadamard rotation on every off-diagonal coordinate pair. -/
noncomputable def hadamard : Matrix (a × a) (a × a) ℂ := fun p q =>
  (if p=q then diagWeight p else 0) +
  (if p.swap=q then swapWeight p else 0)

theorem hadamard_mul_apply {κ : Type*} (B : Matrix (a × a) κ ℂ)
    (p : a × a) (q : κ) :
    (hadamard (a := a) * B) p q = diagWeight p * B p q + swapWeight p * B p.swap q := by
  classical
  simp [Matrix.mul_apply, hadamard, add_mul, ite_mul, Finset.sum_add_distrib]

theorem hadamard_conjTranspose : (hadamard (a := a))ᴴ = hadamard := by
  classical
  ext p q
  change star (hadamard q p) = hadamard p q
  by_cases h : p=q
  · subst q
    by_cases hs : p.swap=p <;> simp [hadamard, hs]
  · by_cases hs : p.swap=q
    · subst q
      simp [hadamard, h, Ne.symm h]
    · have hqs : q.swap ≠ p := by
        intro he
        apply hs
        simpa using (congrArg Prod.swap he).symm
      simp [hadamard, h, Ne.symm h, hs, hqs]

theorem hadamard_sq : (hadamard (a := a)) * hadamard = 1 := by
  classical
  ext p q
  rw [hadamard_mul_apply]
  by_cases hp : p.1=p.2
  · have hswap : p.swap=p := Prod.ext hp.symm hp
    simp [hadamard, diagWeight, swapWeight, hp, hswap, Matrix.one_apply]
  · have hswap : p.swap ≠ p := by
      intro hh
      exact hp (congrArg Prod.snd hh)
    by_cases h : p=q
    · subst q
      simpa [hadamard, hswap, Matrix.one_apply] using weight_squares p
    · by_cases hs : p.swap=q
      · subst q
        simp only [hadamard, h, ite_false, Prod.swap_swap, hswap, ite_true,
          swapWeight_swap, diagWeight_swap hp]
        simp [Matrix.one_apply, h]
        ring
      · simp [hadamard, h, hs, Matrix.one_apply]

noncomputable def hadamardUnitary : Matrix.unitaryGroup (a × a) ℂ :=
  ⟨hadamard, by
    constructor <;> simpa only [Matrix.star_eq_conjTranspose,
      hadamard_conjTranspose] using (hadamard_sq (a := a))⟩
end APPTReview
