import Entry005.TruncationActualDefect
import Entry005.TruncationSharpnessAssembly

noncomputable section
open Filter Topology

namespace Entry005

/-- The actual published sharpness target, using the literal research
definitions in unchanged `Targets.lean`. No geometric or maximum-simplex
identity is an assumption. -/
theorem truncationSharpness : truncationSharpnessGoal :=
  truncation_sharpness_from_actual_defect_formula
    (fun d hd t ht0 ht1 => truncation_entryDefect_exact (by omega) t ht0 ht1)

theorem truncation_entryDefect_pos {d : ℕ} (hd : 3 ≤ d)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < entryDefect (truncationSet d t) := by
  rw [truncation_entryDefect_exact (by omega) t ht0 ht1]
  exact truncation_rational_defect_pos hd ht0 ht1

theorem truncation_entryDefect_quotient_tendsto {d : ℕ} (hd : 3 ≤ d) :
    Tendsto (fun t : ℝ => entryDefect (truncationSet d t) / t ^ (d - 1))
      (𝓝[Set.Ioi 0] 0) (𝓝 ((d : ℝ) * (d - 1) / (d + 1) ^ 2)) :=
  truncation_conditional_scalar_quotient_tendsto hd
    (fun t => entryDefect (truncationSet d t))
    (fun t ht0 ht1 => truncation_entryDefect_exact (by omega) t ht0 ht1)

#print axioms truncationSharpness
#print axioms truncation_entryDefect_pos
#print axioms truncation_entryDefect_quotient_tendsto

end Entry005
