import BapatDefs
import ProofBundle

set_option autoImplicit false
open scoped BigOperators ComplexOrder

namespace BapatExplicit

theorem inversionCount_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Bapat.inversionCount σ = BapatRankTwo.inversions σ := by
  unfold Bapat.inversionCount BapatRankTwo.inversions
  simp only [Finset.card_filter, Fintype.sum_prod_type]

theorem qPermanent_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℂ) :
    Bapat.qPermanent A q = BapatRankTwo.qPermanent A q := by
  unfold Bapat.qPermanent BapatRankTwo.qPermanent Bapat.permutationWeight
  simp_rw [inversionCount_eq]
  apply Finset.sum_congr (by ext σ; simp)
  intro σ _
  rfl

theorem endpointDerivative_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (Bapat.endpointDerivative A).re =
      (BapatRankTwo.realQPolynomial A).derivative.eval 1 := by
  rw [BapatRankTwo.realQPolynomial_derivative_one]
  unfold Bapat.endpointDerivative BapatRankTwo.MarkedInversions.weightedInversionSum
    Bapat.permutationWeight BapatRankTwo.MarkedInversions.permutationWeight
  congr 1
  apply Finset.sum_congr (by ext σ; simp)
  intro σ _
  rw [inversionCount_eq]
  rfl

noncomputable def twoColumnGram {n : ℕ} (a b : Fin n → ℂ) :
    Matrix (Fin n) (Fin 2) ℂ := fun i j => if j = 0 then a i else b i

theorem twoColumnGram_mul {n : ℕ} (a b : Fin n → ℂ) :
    twoColumnGram a b * (twoColumnGram a b).conjTranspose = BapatRankTwo.gram a b := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    twoColumnGram, BapatRankTwo.gram]

theorem perturb_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    BapatBounds.diagonalPerturbation A ε = BapatRankTwo.perturb A ε := rfl

end BapatExplicit
