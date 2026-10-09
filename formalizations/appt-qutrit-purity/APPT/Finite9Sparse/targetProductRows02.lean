import APPT.Finite9Sparse.TargetQuadratic
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def targetProductRow08 : CoefficientMerge.Poly := [(nat_lit 8, Int.negSucc (nat_lit 935)), (nat_lit 17, Int.negSucc (nat_lit 1565)), (nat_lit 26, Int.negSucc (nat_lit 1259)), (nat_lit 35, Int.negSucc (nat_lit 953)), (nat_lit 44, Int.negSucc (nat_lit 647)), (nat_lit 53, Int.negSucc (nat_lit 341)), (nat_lit 62, Int.negSucc (nat_lit 35)), (nat_lit 71, Int.ofNat (nat_lit 270)), (nat_lit 80, Int.ofNat (nat_lit 576)), (nat_lit 98, Int.negSucc (nat_lit 1565)), (nat_lit 107, Int.negSucc (nat_lit 2519)), (nat_lit 116, Int.negSucc (nat_lit 1907)), (nat_lit 125, Int.negSucc (nat_lit 1295)), (nat_lit 134, Int.negSucc (nat_lit 683)), (nat_lit 143, Int.negSucc (nat_lit 71)), (nat_lit 152, Int.ofNat (nat_lit 540)), (nat_lit 161, Int.ofNat (nat_lit 1152)), (nat_lit 188, Int.negSucc (nat_lit 1889)), (nat_lit 197, Int.negSucc (nat_lit 2861)), (nat_lit 206, Int.negSucc (nat_lit 1943)), (nat_lit 215, Int.negSucc (nat_lit 1025)), (nat_lit 224, Int.negSucc (nat_lit 107)), (nat_lit 233, Int.ofNat (nat_lit 810)), (nat_lit 242, Int.ofNat (nat_lit 1728)), (nat_lit 278, Int.negSucc (nat_lit 1907)), (nat_lit 287, Int.negSucc (nat_lit 2591)), (nat_lit 296, Int.negSucc (nat_lit 1367)), (nat_lit 305, Int.negSucc (nat_lit 143)), (nat_lit 314, Int.ofNat (nat_lit 1080)), (nat_lit 323, Int.ofNat (nat_lit 2304)), (nat_lit 368, Int.negSucc (nat_lit 1619)), (nat_lit 377, Int.negSucc (nat_lit 1709)), (nat_lit 386, Int.negSucc (nat_lit 179)), (nat_lit 395, Int.ofNat (nat_lit 1350)), (nat_lit 404, Int.ofNat (nat_lit 2880)), (nat_lit 458, Int.negSucc (nat_lit 1025)), (nat_lit 467, Int.negSucc (nat_lit 215)), (nat_lit 476, Int.ofNat (nat_lit 1620)), (nat_lit 485, Int.ofNat (nat_lit 3456)), (nat_lit 548, Int.negSucc (nat_lit 125)), (nat_lit 557, Int.ofNat (nat_lit 1890)), (nat_lit 566, Int.ofNat (nat_lit 4032)), (nat_lit 638, Int.ofNat (nat_lit 1080)), (nat_lit 647, Int.ofNat (nat_lit 4608)), (nat_lit 728, Int.ofNat (nat_lit 2592))]
theorem targetProductRow08_decode : SparsePolynomial.decodeCubic 9 targetProductRow08 = SparsePolynomial.monoTimes [8] (9 : Int) targetQuadratic := by decide +kernel
theorem eval_targetProductRow08 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) targetProductRow08 = (9 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) targetQuadratic := by
  rw [← SparsePolynomial.eval_decodeCubic, targetProductRow08_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
