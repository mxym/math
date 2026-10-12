import CofactorNormalizedRows
import BapatPermanentFischer

/-! Exact coefficient norm formula for the permanent of actual normalized binary rows. -/
set_option autoImplicit false
open scoped BigOperators
open BapatFischer
namespace CofactorSpectral
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

def slopePolynomial (z : V → ℂ) : Polynomial ℂ :=
  ∏ i, (1+Polynomial.C (z i)*Polynomial.X)

theorem twoColorProduct_binary (a z : V → ℂ) :
    twoColorProduct a (fun i => a i*z i) = Polynomial.C (∏ i, a i)*slopePolynomial z := by
  unfold twoColorProduct slopePolynomial
  have he : ∀ i, Polynomial.C (a i)+Polynomial.C (a i*z i)*Polynomial.X =
      Polynomial.C (a i)*(1+Polynomial.C (z i)*Polynomial.X) := by
    intro i
    rw [map_mul]
    ring
  simp_rw [he]
  rw [Finset.prod_mul_distrib,map_prod]

theorem fischerNormSq_C_mul (n : ℕ) (a : ℂ) (p : Polynomial ℂ) :
    fischerNormSq n (Polynomial.C a*p) = Complex.normSq a*fischerNormSq n p := by
  unfold fischerNormSq
  simp_rw [Polynomial.coeff_C_mul,Complex.normSq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem binaryRows_permanent (a z : V → ℂ) :
    (complexGram (binaryRows a z)).permanent.re =
      Complex.normSq (∏ i, a i)*fischerNormSq (Fintype.card V) (slopePolynomial z) := by
  have he : complexGram (binaryRows a z) =
      (fun i j => a i*star (a j)+(a i*z i)*star (a j*z j)) := by
    ext i j
    simp only [complexGram,Fin.sum_univ_two,binaryRows,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [he,permanent_rankTwo_gram,Complex.ofReal_re,twoColorProduct_binary,
    fischerNormSq_C_mul]

theorem normalizedBinaryGram_permanent_formula (z : V → ℂ) :
    (normalizedBinaryGram z).permanent.re =
      (binaryGamma z)^2*fischerNormSq (Fintype.card V) (slopePolynomial z) := by
  unfold normalizedBinaryGram normalizedBinaryRows
  rw [binaryRows_permanent]
  have he : (∏ i, (binaryScale z i : ℂ)) = (binaryGamma z : ℂ) := by
    simp only [binaryGamma,Complex.ofReal_prod]
  rw [he,Complex.normSq_ofReal,pow_two]

end
end CofactorSpectral
