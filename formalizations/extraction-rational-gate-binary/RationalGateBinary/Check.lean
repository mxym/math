import RationalGateBinary.Provider
open RationalGateBinary CircuitRecursion
#check binaryWordValue_eq_bitValue
#print axioms binaryWordValue_eq_bitValue
#check binaryEntry_decode
#print axioms binaryEntry_decode
#check nativeEntry_decode
#print axioms nativeEntry_decode
#check nativeEntry_oracle
#print axioms nativeEntry_oracle
#check nativeEntry_correct
#print axioms nativeEntry_correct
#check nativeEntry_height
#print axioms nativeEntry_height
#check nativeEntry_height_ninth
#print axioms nativeEntry_height_ninth
#check nativeEntryProgram_normalization_actions
#print axioms nativeEntryProgram_normalization_actions

example : ((nativeEntry 0 4).decode.numerators.get 1) = 12 := by decide
example : ((nativeEntry 1 4).decode.numerators.get 1) = -12 := by decide
example : ((nativeEntry 3 4).decode.numerators.get 3) = -12 := by decide
example : (nativeEntry 2 0).decode.denominator = 1 := by decide

#eval do
  let expected : List (List Int) := [[9,12,0,0],[9,-12,0,0],[9,0,0,12],[9,0,0,-12]]
  for i in List.finRange 4 do
    let result := nativeEntryProgram i 4
    unless result.packet.decode.numerators.toList == expected[i.val]! &&
        result.packet.decode.denominator == 16 && result.actions ≤ 384 do
      throw (IO.userError "CONCRETE_NATIVE_WORD_PROVIDER_CHECK_FAILED")
    for j in List.finRange 4 do
      unless ((nativeEntry i 0).numerators.get j).negative == false do
        throw (IO.userError "NEGATIVE_ZERO_NORMALIZATION_FAILED")
  IO.println "CONCRETE_NATIVE_WORD_PROVIDER_CHECK_PASS"
