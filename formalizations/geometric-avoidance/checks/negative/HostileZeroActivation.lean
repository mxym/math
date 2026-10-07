import ContinuumGeometric.RoutingInterfaces
namespace ContinuumGeometric.GeometryControls

def zeroParameter : PowerParams 0 0 := (⟨0, by norm_num⟩, ⟨1, by norm_num⟩)
example : zeroParameter ∈ powerActivation 3 0 3 5 := by
  norm_num [zeroParameter, powerActivation]

end ContinuumGeometric.GeometryControls
