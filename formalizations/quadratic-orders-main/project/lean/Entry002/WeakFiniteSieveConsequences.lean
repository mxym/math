import Entry002.WeakSupplyDirichletGoodBins
import Entry002.WeakCoreWeakTargets

/-! Closed exact weak-sieve targets from the actual prime-specific Dirichlet
bridge and the proved A1–A4/common-law geometric engine. -/
set_option autoImplicit false

namespace Entry002

theorem weakFiniteSieveTarget_proved : WeakFiniteSieveTarget :=
  WeakA5.weakFiniteSieveTarget_of_prime_dirichlet_good_bin_bridge
    positiveUpperLogGoodBinSupply_of_positiveUpperDirichletSupply

theorem weakFiniteSieveNoWalkTarget_proved : WeakFiniteSieveNoWalkTarget :=
  WeakA5.weakFiniteSieveNoWalkTarget_of_finiteSieveTarget weakFiniteSieveTarget_proved

end Entry002
