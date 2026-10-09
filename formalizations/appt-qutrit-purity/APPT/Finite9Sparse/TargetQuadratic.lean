import APPT.Finite9Sparse.Moments
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def targetQuadratic : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0], Int.negSucc (nat_lit 103)), ([nat_lit 0, nat_lit 1], Int.negSucc (nat_lit 173)), ([nat_lit 0, nat_lit 2], Int.negSucc (nat_lit 139)), ([nat_lit 0, nat_lit 3], Int.negSucc (nat_lit 105)), ([nat_lit 0, nat_lit 4], Int.negSucc (nat_lit 71)), ([nat_lit 0, nat_lit 5], Int.negSucc (nat_lit 37)), ([nat_lit 0, nat_lit 6], Int.negSucc (nat_lit 3)), ([nat_lit 0, nat_lit 7], Int.ofNat (nat_lit 30)), ([nat_lit 0, nat_lit 8], Int.ofNat (nat_lit 64)), ([nat_lit 1, nat_lit 1], Int.negSucc (nat_lit 173)), ([nat_lit 1, nat_lit 2], Int.negSucc (nat_lit 279)), ([nat_lit 1, nat_lit 3], Int.negSucc (nat_lit 211)), ([nat_lit 1, nat_lit 4], Int.negSucc (nat_lit 143)), ([nat_lit 1, nat_lit 5], Int.negSucc (nat_lit 75)), ([nat_lit 1, nat_lit 6], Int.negSucc (nat_lit 7)), ([nat_lit 1, nat_lit 7], Int.ofNat (nat_lit 60)), ([nat_lit 1, nat_lit 8], Int.ofNat (nat_lit 128)), ([nat_lit 2, nat_lit 2], Int.negSucc (nat_lit 209)), ([nat_lit 2, nat_lit 3], Int.negSucc (nat_lit 317)), ([nat_lit 2, nat_lit 4], Int.negSucc (nat_lit 215)), ([nat_lit 2, nat_lit 5], Int.negSucc (nat_lit 113)), ([nat_lit 2, nat_lit 6], Int.negSucc (nat_lit 11)), ([nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 90)), ([nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 192)), ([nat_lit 3, nat_lit 3], Int.negSucc (nat_lit 211)), ([nat_lit 3, nat_lit 4], Int.negSucc (nat_lit 287)), ([nat_lit 3, nat_lit 5], Int.negSucc (nat_lit 151)), ([nat_lit 3, nat_lit 6], Int.negSucc (nat_lit 15)), ([nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 120)), ([nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 256)), ([nat_lit 4, nat_lit 4], Int.negSucc (nat_lit 179)), ([nat_lit 4, nat_lit 5], Int.negSucc (nat_lit 189)), ([nat_lit 4, nat_lit 6], Int.negSucc (nat_lit 19)), ([nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 150)), ([nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 320)), ([nat_lit 5, nat_lit 5], Int.negSucc (nat_lit 113)), ([nat_lit 5, nat_lit 6], Int.negSucc (nat_lit 23)), ([nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 180)), ([nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 384)), ([nat_lit 6, nat_lit 6], Int.negSucc (nat_lit 13)), ([nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 210)), ([nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 448)), ([nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 120)), ([nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 512)), ([nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 288))]
theorem targetQuadratic_data : targetQuadratic = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.scale 17 (SparsePolynomial.mul polyTotal polyTotal)) (SparsePolynomial.scale (-121) polySquares)) := by decide +kernel
theorem eval_targetQuadratic (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) targetQuadratic = 17*(total g)^2-121*squareTotal g := by
  rw [targetQuadratic_data]
  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, eval_polyTotal, eval_polySquares]
  push_cast
  ring

end APPT.Finite9
