import CircuitCompletion.OccupationRecurrence

open scoped BigOperators
open SymmetricSupport
namespace CircuitCompletion

/-- The normalized occupation basis in the actual original word coordinates. -/
noncomputable def occupationVector {D k : ℕ} (ν : Sym (Fin D) k) : Word D k → ℂ :=
  fun w => if occupation D k w=ν then ((Real.sqrt (fiberCard (occupation D k) ν : ℝ))⁻¹ : ℂ) else 0

theorem fiber_normalization_branch {D k : ℕ} (ν : Sym (Fin D) (k+1))
    (i : Fin D) (hi : i∈ν) :
    (Real.sqrt (fiberCard (occupation D (k+1)) ν : ℝ))⁻¹=
      Real.sqrt ((ν.val.count i : ℝ)/(k+1))*
        (Real.sqrt (fiberCard (occupation D k) (ν.erase i hi) : ℝ))⁻¹ := by
  have hA : (0 : ℝ)<fiberCard (occupation D k) (ν.erase i hi) := by
    exact_mod_cast fiberCard_pos _ (occupation_surjective D k) (ν.erase i hi)
  have hB : (0 : ℝ)<fiberCard (occupation D (k+1)) ν := by
    exact_mod_cast fiberCard_pos _ (occupation_surjective D (k+1)) ν
  have hN : (0 : ℝ)<k+1 := by positivity
  have hrec : (fiberCard (occupation D k) (ν.erase i hi) : ℝ)*(k+1)=
      (ν.val.count i : ℝ)*fiberCard (occupation D (k+1)) ν := by
    exact_mod_cast fiberCard_erase_recurrence ν i hi
  have hratio : (fiberCard (occupation D k) (ν.erase i hi) : ℝ)/
      fiberCard (occupation D (k+1)) ν=(ν.val.count i : ℝ)/(k+1) := by
    apply (div_eq_div_iff hB.ne' hN.ne').mpr
    exact hrec
  rw [← hratio,Real.sqrt_div hA.le]
  have hsA : Real.sqrt (fiberCard (occupation D k) (ν.erase i hi) : ℝ)≠0 :=
    (Real.sqrt_pos.mpr hA).ne'
  field_simp

/-- Exact normalized branching, including missing letters as zero branches.
The coefficient sqrt(ν_i/(k+1)) is derived from actual word-fiber sizes. -/
theorem occupationVector_branch {D k : ℕ} (ν : Sym (Fin D) (k+1))
    (i : Fin D) (w : Word D k) :
    occupationVector ν (Fin.cons i w)=
      if hi : i∈ν then (Real.sqrt ((ν.val.count i : ℝ)/(k+1)) : ℂ)*
        occupationVector (ν.erase i hi) w else 0 := by
  by_cases hi : i∈ν
  · rw [dif_pos hi]
    have heq : occupation D (k+1) (Fin.cons i w)=ν ↔ occupation D k w=ν.erase i hi := by
      rw [occupation_cons]
      constructor
      · intro h
        apply (Sym.cons_inj_right i _ _).mp
        exact h.trans (Sym.cons_erase hi).symm
      · intro h
        rw [h,Sym.cons_erase hi]
    by_cases hw : occupation D k w=ν.erase i hi
    · simp only [occupationVector,heq,hw,if_true]
      exact_mod_cast fiber_normalization_branch ν i hi
    · simp [occupationVector,heq,hw]
  · rw [dif_neg hi]
    have heq : occupation D (k+1) (Fin.cons i w)≠ν := by
      intro h
      have hm : i∈occupation D (k+1) (Fin.cons i w) := by rw [occupation_cons];simp
      exact hi (h ▸ hm)
    simp [occupationVector,heq]

end CircuitCompletion
