import ArithmeticSupplyFromPrimeIdealPNT
import Entry002.FiniteSieveConsequences

/-! A conditional implication to the literal all-quadratic-orders moat
statement. Its sole analytic premise is the actual number-field prime-ideal
counting theorem, which is not proved or assumed as an axiom here. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace Entry002

/-- The displayed actual prime-ideal asymptotic is sufficient for the exact
unchanged all-quadratic-orders MainTarget, using the closed finite-sieve engine. -/
theorem arithmeticSupply_mainTarget_of_primeIdealPNT
    (hPrimeIdeal : ∀ (N : Type) [Field N] [NumberField N],
      Tendsto (fun x : ℝ =>
        ((nonzeroPrimeIdealsUpTo N ⌊x⌋₊).card : ℝ) / (x / Real.log x))
        atTop (nhds 1)) : MainTarget := by
  exact mainTarget_of_principalPrimeSupply
    (arithmeticSupply_principalSupply_of_primeIdealPNT hPrimeIdeal)

end Entry002
