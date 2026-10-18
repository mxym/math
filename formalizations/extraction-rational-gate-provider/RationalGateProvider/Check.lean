import RationalGateProvider.SignedFifths

open RationalGateProvider

#check run_quotient
#check run_dyadic_error
#check run_steps
#check signedRun_error_real
#check total_output_bits

#print axioms run_quotient
#print axioms run_dyadic_error
#print axioms run_steps
#print axioms signedRun_error_real

example : bitValue (run .r3 0).bits = 0 := by decide
example : bitValue (run .r3 4).bits = 9 := by decide
example : bitValue (run .r4 4).bits = 12 := by decide
example : (signedRun true .r3 4).value = -9 := by decide
example : bitValue (denominatorBits 4) = 16 := by decide

#eval do
  for p in List.range 17 do
    for initial in [Remainder.r0, .r1, .r2, .r3, .r4] do
      let s := run initial p
      unless s.bits.length == p && bitValue s.bits == initial.value * 2 ^ p / 5 do
        throw (IO.userError "FINITE_FIFTH_PROVIDER_CHECK_FAILED")
  IO.println "FINITE_FIFTH_PROVIDER_CHECK_PASS"
