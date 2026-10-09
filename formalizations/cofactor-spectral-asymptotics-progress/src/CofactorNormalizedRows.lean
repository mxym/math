import CofactorBinaryMarkedLower
import CofactorTargets

/-! Actual unit binary rows, their positive permanent and their Gram correlation matrix. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder Matrix
open BapatFiniteRank
namespace CofactorSpectral
noncomputable section
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem complexGram_eq_self_mul_conjTranspose (v : V → C → ℂ) :
    complexGram v = Matrix.of v * (Matrix.of v)ᴴ := by
  ext i j
  simp only [complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.of_apply]

theorem complexGram_psd (v : V → C → ℂ) : (complexGram v).PosSemidef := by
  rw [complexGram_eq_self_mul_conjTranspose]
  exact Matrix.posSemidef_self_mul_conjTranspose (Matrix.of v)

def binaryScale (z : V → ℂ) (i : V) : ℝ := (Real.sqrt (1+Complex.normSq (z i)))⁻¹

def normalizedBinaryRows (z : V → ℂ) : V → Fin 2 → ℂ :=
  binaryRows (fun i => (binaryScale z i : ℂ)) z

def normalizedBinaryGram (z : V → ℂ) : Matrix V V ℂ := complexGram (normalizedBinaryRows z)
def binaryGamma (z : V → ℂ) : ℝ := ∏ i, binaryScale z i

theorem binaryScale_pos (z : V → ℂ) (i : V) : 0 < binaryScale z i :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by nlinarith [Complex.normSq_nonneg (z i)]))

theorem binaryScale_sq (z : V → ℂ) (i : V) :
    binaryScale z i ^ 2 * (1+Complex.normSq (z i)) = 1 := by
  have hp : 0 < 1+Complex.normSq (z i) := by nlinarith [Complex.normSq_nonneg (z i)]
  have hs := Real.sq_sqrt hp.le
  unfold binaryScale
  calc
    _ = (Real.sqrt (1+Complex.normSq (z i)))⁻¹^2 *
        (Real.sqrt (1+Complex.normSq (z i)))^2 :=
      congrArg (fun r : ℝ => (Real.sqrt (1+Complex.normSq (z i)))⁻¹^2*r) hs.symm
    _ = 1 := by field_simp [ne_of_gt (Real.sqrt_pos.mpr hp)]

theorem normalizedBinaryGram_psd (z : V → ℂ) : (normalizedBinaryGram z).PosSemidef :=
  complexGram_psd _

theorem normalizedBinaryGram_diagonal (z : V → ℂ) (i : V) : normalizedBinaryGram z i i = 1 := by
  have h : ((binaryScale z i : ℂ)^2) * (1+(Complex.normSq (z i) : ℂ)) = 1 := by
    exact_mod_cast binaryScale_sq z i
  simpa [normalizedBinaryGram,normalizedBinaryRows,binaryRows,complexGram,Fin.sum_univ_two,
    Complex.normSq_eq_conj_mul_self,pow_two,mul_add,mul_assoc,mul_comm,mul_left_comm] using h

theorem binaryGamma_pos (z : V → ℂ) : 0 < binaryGamma z :=
  Finset.prod_pos (fun i _ => binaryScale_pos z i)

theorem normalizedBinaryRows_pure_coefficient (z : V → ℂ) :
    (formsProduct (normalizedBinaryRows z)).coeff
      (Finsupp.single (0 : Fin 2) (Fintype.card V)) = (binaryGamma z : ℂ) := by
  rw [formsProduct_pure_coefficient]
  simp [normalizedBinaryRows,binaryRows,binaryGamma]

theorem normalizedBinaryGram_permanent_pos (z : V → ℂ) :
    0 < (normalizedBinaryGram z).permanent.re := by
  have h := fockNormSq_coefficient_lower (formsProduct (normalizedBinaryRows z))
    (Finsupp.single (0 : Fin 2) (Fintype.card V))
  rw [normalizedBinaryRows_pure_coefficient] at h
  have hp : 0 < ((Fintype.card V).factorial : ℝ) * (binaryGamma z)^2 := by
    exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (sq_pos_of_pos (binaryGamma_pos z))
  have he : multiFactorial (Finsupp.single (0 : Fin 2) (Fintype.card V)) =
      (Fintype.card V).factorial := by
    simp [multiFactorial,Fin.prod_univ_two,Finsupp.single_apply]
  rw [he,Complex.normSq_ofReal,← pow_two] at h
  have hpos := hp.trans_le h
  simpa only [normalizedBinaryGram,permanent_complexGram,Complex.ofReal_re] using hpos

end
end CofactorSpectral
