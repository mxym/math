import APPTReview.SpectralBounds

open scoped BigOperators
namespace APPTReview
variable {a : Type*} [LinearOrder a]

def pairBad (z : a) (d : a × a → ℝ) (p : a × a) : Prop :=
  p.1 ≠ z ∧ p.2 ≠ z ∧ d (max p.1 p.2, min p.1 p.2) < d (min p.1 p.2, max p.1 p.2)

noncomputable def pairSortFun (z : a) (d : a × a → ℝ) (p : a × a) : a × a :=
  by classical exact if pairBad z d p then p.swap else p

theorem pairBad_swap (z : a) (d : a × a → ℝ) (p : a × a) :
    pairBad z d p.swap ↔ pairBad z d p := by
  simp [pairBad, min_comm, max_comm, and_left_comm]

theorem pairSortFun_involutive (z : a) (d : a × a → ℝ) :
    Function.Involutive (pairSortFun z d) := by
  intro p
  by_cases hp : pairBad z d p
  · have hq : pairBad z d p.swap := (pairBad_swap z d p).2 hp
    simp [pairSortFun, hp, hq]
  · simp [pairSortFun, hp]

noncomputable def cornerSort (z : a) (d : a × a → ℝ) : Equiv.Perm (a × a) :=
  ⟨pairSortFun z d, pairSortFun z d,
    pairSortFun_involutive z d, pairSortFun_involutive z d⟩

@[simp] theorem cornerSort_apply (z : a) (d : a × a → ℝ) (p : a × a) :
    cornerSort z d p = pairSortFun z d p := rfl

@[simp] theorem cornerSort_center_left (z j : a) (d : a × a → ℝ) :
    cornerSort z d (z,j) = (z,j) := by
  simp [cornerSort_apply, pairSortFun, pairBad]

@[simp] theorem cornerSort_center_right (z i : a) (d : a × a → ℝ) :
    cornerSort z d (i,z) = (i,z) := by
  simp [cornerSort_apply, pairSortFun, pairBad]

@[simp] theorem cornerSort_diagonal (z i : a) (d : a × a → ℝ) :
    cornerSort z d (i,i) = (i,i) := by
  simp [cornerSort_apply, pairSortFun, pairBad]

/-- Independently orient every leaf pair while fixing every diagonal and the
entire distinguished star. This removes the need to enumerate all triangle edges. -/
theorem cornerSort_order (z : a) (d : a × a → ℝ) (i j : a)
    (hi : i ≠ z) (hj : j ≠ z) (hij : i < j) :
    d (cornerSort z d (i,j)) ≤ d (cornerSort z d (j,i)) := by
  by_cases hd : d (i,j) ≤ d (j,i)
  · have hh : ¬ d (j,i) < d (i,j) := not_lt.mpr hd
    simpa [cornerSort_apply, pairSortFun, pairBad, hi, hj,
      min_eq_left hij.le, max_eq_right hij.le, min_eq_right hij.le,
      max_eq_left hij.le, hh] using hd
  · have hh : d (j,i) < d (i,j) := lt_of_not_ge hd
    simpa [cornerSort_apply, pairSortFun, pairBad, hi, hj,
      min_eq_left hij.le, max_eq_right hij.le, min_eq_right hij.le,
      max_eq_left hij.le, hh] using hh.le

abbrev StarSlot (h : ℕ) := Unit ⊕ (Fin h ⊕ (Fin h ⊕ Fin h))

def starSlotCoord {h : ℕ} : StarSlot h → Fin (h+1) × Fin (h+1)
  | .inl _ => (0,0)
  | .inr (.inl i) => (i.succ,i.succ)
  | .inr (.inr (.inl i)) => (0,i.succ)
  | .inr (.inr (.inr i)) => (i.succ,0)

theorem starSlotCoord_injective {h : ℕ} : Function.Injective (starSlotCoord (h:=h)) := by
  have hn (i : Fin h) : (0 : Fin (h+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  intro x y hxy
  rcases x with x | x | x | x <;> rcases y with y | y | y | y <;>
    simp_all [starSlotCoord]

def starSlotLabel {h D : ℕ} (hD : 3*h+1 ≤ D) : StarSlot h → Fin D
  | .inl _ => ⟨D-1, by omega⟩
  | .inr (.inl i) => ⟨D-(h+2+i.val), by omega⟩
  | .inr (.inr (.inl i)) => ⟨D-(2+i.val), by omega⟩
  | .inr (.inr (.inr i)) => ⟨i.val, by omega⟩

theorem starSlotLabel_injective {h D : ℕ} (hD : 3*h+1 ≤ D) :
    Function.Injective (starSlotLabel hD) := by
  intro x y hxy
  have hv := congrArg Fin.val hxy
  rcases x with x | x | x | x <;> rcases y with y | y | y | y
  all_goals simp only [starSlotLabel] at hv
  all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq]
  all_goals first | exact Subsingleton.elim _ _ | (apply Fin.ext; omega) | omega

end APPTReview
