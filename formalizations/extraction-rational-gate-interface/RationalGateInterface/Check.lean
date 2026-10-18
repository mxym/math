import RationalGateInterface.Library
open RationalGateInterface
#check rationalGate_coordinates
#print axioms rationalGate_coordinates
#check rationalGate_inverse
#print axioms rationalGate_inverse
#check entryBits_error
#print axioms entryBits_error
#check dyadicEntry_correct
#print axioms dyadicEntry_correct
#check entryBits_length
#print axioms entryBits_length
#check entryBits_total_length
#print axioms entryBits_total_length

example : (dyadicEntry 0 4).get 0 = 9 := by decide
example : (dyadicEntry 0 4).get 1 = 12 := by decide
example : (dyadicEntry 1 4).get 1 = -12 := by decide
example : (dyadicEntry 3 4).get 3 = -12 := by decide

#eval do
  let expected : List (List Int) := [[9,12,0,0],[9,-12,0,0],[9,0,0,12],[9,0,0,-12]]
  for i in List.finRange 4 do
    unless (dyadicEntry i 4).toList == expected[i.val]! do
      throw (IO.userError "RATIONAL_GATE_PROVIDER_DATA_CHECK_FAILED")
  IO.println "RATIONAL_GATE_PROVIDER_DATA_CHECK_PASS"
