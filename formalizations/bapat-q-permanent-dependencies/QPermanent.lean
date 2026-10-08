import QDefinitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

open scoped BigOperators
namespace Bapat
 theorem hasDerivAt_qPermanent_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (qPermanent A) (endpointDerivative A) 1 := by
  unfold qPermanent endpointDerivative
  apply HasDerivAt.fun_sum
  intro σ hσ
  simpa using ((hasDerivAt_id (1 : ℂ)).pow (inversionCount σ)).mul_const
    (permutationWeight A σ)

end Bapat
