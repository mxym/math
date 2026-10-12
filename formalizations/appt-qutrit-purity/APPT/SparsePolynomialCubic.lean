import APPT.SparsePolynomial
import APPT.CoefficientMergeFast

namespace APPT.CoefficientMerge

def trim : Poly → Poly
  | [] => []
  | (k,c)::p => if c=0 then trim p else (k,c)::trim p

theorem eval_trim (f : Nat → ℝ) (p : Poly) : eval f (trim p) = eval f p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨k,c⟩
    by_cases h : c=0 <;> simp [trim, h, eval, ih]

end APPT.CoefficientMerge

namespace APPT.SparsePolynomial

/-- A fixed-length three-letter monomial code. The decoding theorem requires no
injectivity premise; every concrete encoding is separately checked by the kernel. -/
def decodeCubic (base : Nat) : CoefficientMerge.Poly → Poly
  | [] => []
  | (k,c)::p => ([k/(base*base), k/base%base, k%base],c)::decodeCubic base p

noncomputable def cubeValue (x : Nat → ℝ) (base k : Nat) : ℝ :=
  x (k/(base*base)) * (x (k/base%base) * x (k%base))

theorem eval_decodeCubic (x : Nat → ℝ) (base : Nat) (p : CoefficientMerge.Poly) :
    eval x (decodeCubic base p) = CoefficientMerge.eval (cubeValue x base) p := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨k,c⟩
    simp [decodeCubic, eval, mon, cubeValue, CoefficientMerge.eval, ih]

end APPT.SparsePolynomial
