import BapatN200Trace3

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BapatRankTwo.N200
open Exact

noncomputable def permanentNorm : ℤ := fischerInt 200 checkpoint_200.1
noncomputable def wedgeNorm : ℤ := fischerInt 198 checkpoint_200.2

theorem norm_gap_positive : 19900 * permanentNorm < wedgeNorm := by
  decide +kernel

end BapatRankTwo.N200
