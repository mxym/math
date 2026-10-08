import Entry002.GenericFiniteSieveEngine
import Entry002.Assembly

/-! Closed consequences of the genuine all-lattice finite-sieve proof.
The remaining all-quadratic-order arithmetic supply is an explicit input
of the final conditional theorem, not a hidden proof of MainTarget. -/
set_option autoImplicit false
namespace Entry002

theorem finiteSieveNoWalkTarget_proved : FiniteSieveNoWalkTarget := by
  exact finiteSieveTarget_iff_noWalkTarget.mp finiteSieveTarget_proved

/-- The analytic finite-sieve premise of the earlier assembly is now proved.
The genuine arithmetic prime supply remains the one explicit open premise. -/
theorem mainTarget_of_principalPrimeSupply
    (hsupply : PrincipalSplitPrimeSupplyTarget) : MainTarget := by
  exact mainTarget_of_supply_and_finiteSieve hsupply finiteSieveTarget_proved

end Entry002
