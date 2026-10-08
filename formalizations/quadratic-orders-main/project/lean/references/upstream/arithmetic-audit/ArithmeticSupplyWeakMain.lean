import ArithmeticSupplyWeakFromDirichlet
import Entry002.WeakFiniteSieveConsequences
import Entry002.WeakAssembly

/-! The unchanged all-quadratic-order target from the actual all-conductor
ray-field supply and the closed weaker Dirichlet/common-law finite sieve. -/
set_option autoImplicit false

namespace Entry002

theorem arithmeticSupply_mainTarget_proved : MainTarget :=
  mainTarget_of_weak_supply_and_weak_finiteSieve
    arithmeticSupply_weakPrincipalSupply_from_Dirichlet weakFiniteSieveTarget_proved

end Entry002
