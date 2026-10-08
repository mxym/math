import ContinuumGeometric.RoutingPreorder
open ContinuumGeometric
def c : RoutingTemplate 2 1 := ⟨3, 4, 10⟩
def root : InternalNode 2 1 := ⟨0, Fin.elim0⟩
example : c.edgeStart ⟨root, 1⟩ = c.edgeEnd ⟨root, 0⟩ + 1 := by
  norm_num [c, root, RoutingTemplate.edgeStart, RoutingTemplate.edgeEnd,
    RoutingTemplate.edgeLength, RoutingTemplate.nodeStart, RoutingTemplate.subtreeStart,
    RoutingTemplate.lengthAt, RoutingTemplate.blockSpan]
