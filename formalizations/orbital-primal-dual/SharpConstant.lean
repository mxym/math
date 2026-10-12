import SharpAttainment

open scoped BigOperators
open Set

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I]

def kernelRatios (A : J → I → ℝ) (i : I) : Set ℝ :=
  {r | ∃ v : I → ℝ, Kernel A v ∧ v ≠ 0 ∧ r = |v i| / TV v}

/-- The inserted zero gives the correct value also when the kernel is trivial. -/
def sharpConstant (A : J → I → ℝ) (i : I) : ℝ := sSup (insert 0 (kernelRatios A i))

theorem sharpConstant_eq_optimum (A : J → I → ℝ) (i : I) (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q) (hm : Match A p q)
    (hb : PairBound A i (p i - q i)) : sharpConstant A i = p i - q i := by
  have hC : 0 ≤ p i - q i := by
    have hh := hb uniform uniform uniform_probability uniform_probability (fun _ => rfl)
    simpa only [sub_self] using hh
  have hs := (signedBound_iff_pairBound A i (p i - q i) hC).mpr hb
  have hupper : ∀ r ∈ insert 0 (kernelRatios A i), r ≤ p i - q i := by
    intro r hr
    rcases hr with rfl | hr
    · exact hC
    · obtain ⟨v, hv, hne, rfl⟩ := hr
      exact (div_le_iff₀ (tv_pos v hne)).mpr (hs v hv)
  have hbounded : BddAbove (insert 0 (kernelRatios A i)) := ⟨p i - q i, hupper⟩
  have hnonempty : (insert 0 (kernelRatios A i)).Nonempty := ⟨0, Or.inl rfl⟩
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · by_cases hz : p i - q i = 0
    · rw [hz]
      exact le_csSup hbounded (Or.inl rfl)
    · have hpos : 0 < p i - q i := lt_of_le_of_ne hC (Ne.symm hz)
      have htv := optimal_pair_tv_one A i p q hp hq hm hpos hb
      have hv : (fun g => p g - q g) ≠ 0 := by
        intro he
        have hh := congrFun he i
        exact hz hh
      apply le_csSup hbounded
      right
      refine ⟨(fun g => p g - q g), kernel_of_match A p q hp hq hm, hv, ?_⟩
      simp only [htv, div_one, abs_of_pos hpos]

theorem sharpConstant_trivial_kernel (A : J → I → ℝ) (i : I)
    (h : ∀ v, Kernel A v → v = 0) : sharpConstant A i = 0 := by
  have hr : kernelRatios A i = ∅ := by
    ext r
    constructor
    · rintro ⟨v, hv, hne, _⟩
      exact (hne (h v hv)).elim
    · simp
  simp [sharpConstant, hr]

end
end OrbitalMarginals
