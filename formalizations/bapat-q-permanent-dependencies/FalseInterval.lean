import Controls

namespace BapatBounds

/-- Intentionally false: dropping the negative endpoint condition from the
interval theorem does not make an increasing function decrease. -/
theorem false_interval_without_negative_endpoint :
    (1 : ℝ) < 1 - 1 / (8 * 1) := by
  norm_num

end BapatBounds
