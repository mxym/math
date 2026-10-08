import ContinuumGeometric.RoutingModel
namespace ContinuumGeometric.GeometryControls

-- The first bit agrees, but the default decision still reads the second bit.
example : chooseRoutingChild 3 (by decide) (fun _ => false) =
    chooseRoutingChild 3 (by decide)
      (fun i => if i.val = 0 then false else true) := by
  decide

end ContinuumGeometric.GeometryControls
