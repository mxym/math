import CycleGraphMatrix
import Mathlib.LinearAlgebra.Matrix.Permanent

namespace Chollet

def intCycleL (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (SimpleGraph.cycleGraph n).lapMatrix ℤ

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem cycleFive_int_permanent :
    Matrix.permanent (intCycleL 5) = (80 : ℤ) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem cycleFive_int_hadamard_permanent :
    Matrix.permanent (fun i j => intCycleL 5 i j * intCycleL 5 i j) =
      (1366 : ℤ) := by
  decide

end Chollet

#print axioms Chollet.cycleFive_int_permanent
#print axioms Chollet.cycleFive_int_hadamard_permanent
