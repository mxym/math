import ContinuumGeometric.RoutingGeometry
namespace ContinuumGeometric.GeometryControls

-- Equality of a coarser grid key does not determine a finer key.
example : periodicGridKey 8 (1 / 16 : ℝ) = periodicGridKey 8 0 →
    periodicGridKey 16 (1 / 16 : ℝ) = periodicGridKey 16 0 := by
  norm_num [periodicGridKey]

end ContinuumGeometric.GeometryControls
