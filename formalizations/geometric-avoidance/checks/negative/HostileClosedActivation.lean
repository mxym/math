import ContinuumGeometric.RoutingStableGeometry
open ContinuumGeometric
def p : PowerParams 1 1 := (⟨1, by norm_num⟩, ⟨1, by norm_num⟩)
example : p ∈ powerActivation 3 0 3 5 := by norm_num [p, powerActivation]
