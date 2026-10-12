import CofactorComplexFock

/-! The actual first permanental compound is positive semidefinite for
every complex Hermitian positive semidefinite matrix, including singular ones. -/
set_option autoImplicit false
open scoped BigOperators MatrixOrder ComplexOrder
open MvPolynomial BapatFiniteRank
namespace CofactorSpectral
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
noncomputable section

def polynomialGram (p : V → MvPolynomial C ℂ) : Matrix V V ℂ :=
  fun i j => fockPair (p i) (p j)

def weightedPolynomial (p : V → MvPolynomial C ℂ) (w : V → ℂ) : MvPolynomial C ℂ :=
  ∑ i, MvPolynomial.C (star (w i)) * p i

theorem polynomialGram_quadratic (p : V → MvPolynomial C ℂ) (w : V → ℂ) :
    (∑ i, ∑ j, star (w i) * polynomialGram p i j * w j) =
      fockPair (weightedPolynomial p w) (weightedPolynomial p w) := by
  unfold weightedPolynomial
  rw [fockPair_sum_left]
  simp_rw [fockPair_C_mul_left, fockPair_sum_right, fockPair_C_mul_right, star_star,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold polynomialGram
  ring

theorem polynomialGram_psd (p : V → MvPolynomial C ℂ) : (polynomialGram p).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    exact fockPair_conjugate_symmetry (p j) (p i)
  · intro w
    change 0 ≤ ∑ i, star (w i) * ∑ j, polynomialGram p i j * w j
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [polynomialGram_quadratic]
    exact fockPair_self_nonneg _

def omittedProduct (v : V → C → ℂ) (i : V) : MvPolynomial C ℂ :=
  formsProduct (fun r : {r : V // r ≠ i} => v r.val)

theorem firstCofactor_matrix_complexGram (v : V → C → ℂ) :
    (fun i j => firstCofactor (complexGram v) i j) = polynomialGram (omittedProduct v) := by
  ext i j
  exact firstCofactor_complexGram v i j

theorem firstCofactor_matrix_psd (A : Matrix V V ℂ) (hA : A.PosSemidef) :
    Matrix.PosSemidef (fun i j => firstCofactor A i j) := by
  obtain ⟨v,rfl⟩ := psd_exists_complexGram A hA
  rw [firstCofactor_matrix_complexGram]
  exact polynomialGram_psd _

theorem compound_psd (A : Matrix V V ℂ) (hA : A.PosSemidef) : (compound A).PosSemidef :=
  hA.hadamard (firstCofactor_matrix_psd A hA)

def markedProduct (v : V → C → ℂ) (i : V) (c : C) : MvPolynomial C ℂ :=
  MvPolynomial.C (v i c) * omittedProduct v i

theorem compound_complexGram (v : V → C → ℂ) (i j : V) :
    compound (complexGram v) i j = ∑ c, fockPair (markedProduct v i c) (markedProduct v j c) := by
  simp only [compound, complexGram, firstCofactor_complexGram, markedProduct,
    fockPair_C_mul_left, fockPair_C_mul_right, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  unfold omittedProduct
  ring

def markedSum (v : V → C → ℂ) (w : V → ℂ) (c : C) : MvPolynomial C ℂ :=
  weightedPolynomial (fun i => markedProduct v i c) w

theorem compound_quadratic_complexGram (v : V → C → ℂ) (w : V → ℂ) :
    (∑ i, ∑ j, star (w i) * compound (complexGram v) i j * w j) =
      ∑ c, (fockNormSq (markedSum v w c) : ℂ) := by
  simp_rw [compound_complexGram, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← fockPair_self]
  rw [Finset.sum_comm]
  exact polynomialGram_quadratic (fun i => markedProduct v i c) w

end
end CofactorSpectral
