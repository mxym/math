import BapatMvFischer
import CofactorDefinitions
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Order

/-! Complex Bargmann--Fock pairing on actual multivariate polynomials.
All pairings are linear in the first argument. No rank restriction is used. -/
set_option autoImplicit false
open scoped BigOperators MatrixOrder ComplexOrder
open MvPolynomial BapatFiniteRank
namespace CofactorSpectral
variable {V W C : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
noncomputable section

def conjugatePolynomial (p : MvPolynomial C ℂ) : MvPolynomial C ℂ :=
  MvPolynomial.map (starRingEnd ℂ) p

def fockPair (p q : MvPolynomial C ℂ) : ℂ :=
  fischerPair p (conjugatePolynomial q)

def fockNormSq (p : MvPolynomial C ℂ) : ℝ :=
  p.coeff.sum fun α a => (multiFactorial α : ℝ) * Complex.normSq a

@[simp] theorem conjugatePolynomial_coeff (p : MvPolynomial C ℂ) (α : C →₀ ℕ) :
    (conjugatePolynomial p).coeff α = star (p.coeff α) := by
  simp [conjugatePolynomial, MvPolynomial.coeff_map]

theorem fockPair_eq_sum (p q : MvPolynomial C ℂ) :
    fockPair p q = ∑ α ∈ p.support,
      (multiFactorial α : ℂ) * p.coeff α * star (q.coeff α) := by
  simp [fockPair, fischerPair, MvPolynomial.sum_def]

theorem fockPair_eq_sum_of_support_subset (p q : MvPolynomial C ℂ)
    (s : Finset (C →₀ ℕ)) (hp : p.support ⊆ s) :
    fockPair p q = ∑ α ∈ s,
      (multiFactorial α : ℂ) * p.coeff α * star (q.coeff α) := by
  rw [fockPair_eq_sum]
  apply Finset.sum_subset hp
  intro α _ hα
  have hz : p.coeff α = 0 := by simpa using hα
  simp [hz]

theorem fockPair_conjugate_symmetry (p q : MvPolynomial C ℂ) :
    star (fockPair p q) = fockPair q p := by
  rw [fockPair_eq_sum_of_support_subset p q (p.support ∪ q.support) Finset.subset_union_left,
    fockPair_eq_sum_of_support_subset q p (p.support ∪ q.support) Finset.subset_union_right,
    star_sum]
  apply Finset.sum_congr rfl
  intro α _
  simp only [star_mul, star_star, star_natCast]
  ring

theorem fockPair_self (p : MvPolynomial C ℂ) :
    fockPair p p = (fockNormSq p : ℂ) := by
  rw [fockPair_eq_sum]
  unfold fockNormSq
  rw [MvPolynomial.sum_def, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

theorem fockNormSq_nonneg (p : MvPolynomial C ℂ) : 0 ≤ fockNormSq p := by
  unfold fockNormSq
  rw [MvPolynomial.sum_def]
  exact Finset.sum_nonneg fun α _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

theorem fockPair_self_nonneg (p : MvPolynomial C ℂ) : 0 ≤ fockPair p p := by
  rw [fockPair_self]
  exact_mod_cast fockNormSq_nonneg p

theorem fockPair_sum_left {J : Type*} (s : Finset J)
    (p : J → MvPolynomial C ℂ) (q : MvPolynomial C ℂ) :
    fockPair (∑ j ∈ s, p j) q = ∑ j ∈ s, fockPair (p j) q :=
  fischerPair_sum_left s p (conjugatePolynomial q)

theorem fockPair_sum_right {J : Type*} (s : Finset J)
    (p : MvPolynomial C ℂ) (q : J → MvPolynomial C ℂ) :
    fockPair p (∑ j ∈ s, q j) = ∑ j ∈ s, fockPair p (q j) := by
  unfold fockPair conjugatePolynomial
  rw [map_sum, fischerPair_sum_right]

theorem fockPair_C_mul_left (a : ℂ) (p q : MvPolynomial C ℂ) :
    fockPair (MvPolynomial.C a * p) q = a * fockPair p q :=
  fischerPair_C_mul_left a p (conjugatePolynomial q)

theorem fockPair_C_mul_right (a : ℂ) (p q : MvPolynomial C ℂ) :
    fockPair p (MvPolynomial.C a * q) = star a * fockPair p q := by
  unfold fockPair conjugatePolynomial
  rw [map_mul, MvPolynomial.map_C, fischerPair_C_mul_right]
  rfl

theorem conjugate_linearForm (v : C → ℂ) :
    conjugatePolynomial (linearForm v) = linearForm (fun c => star (v c)) := by
  simp [conjugatePolynomial, linearForm, map_sum, MvPolynomial.map_monomial]

theorem conjugate_formsProduct (v : V → C → ℂ) :
    conjugatePolynomial (formsProduct v) = formsProduct (fun i c => star (v i c)) := by
  unfold conjugatePolynomial formsProduct
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact conjugate_linearForm (v i)

def complexGram (v : V → C → ℂ) : Matrix V V ℂ :=
  fun i j => ∑ c, v i c * star (v j c)

theorem mixedPermanent_complexGram (v : V → C → ℂ) (w : W → C → ℂ) :
    BapatFiniteRank.mixedPermanent (fun i j => ∑ c, v i c * star (w j c)) =
      fockPair (formsProduct v) (formsProduct w) := by
  unfold fockPair
  rw [conjugate_formsProduct]
  exact BapatFiniteRank.mixedPermanent_fischer v (fun j c => star (w j c))

theorem permanent_complexGram (v : V → C → ℂ) :
    (complexGram v).permanent = (fockNormSq (formsProduct v) : ℂ) := by
  calc
    _ = BapatFiniteRank.mixedPermanent (complexGram v) :=
      (BapatFiniteRank.mixedPermanent_eq_permanent (complexGram v)).symm
    _ = fockPair (formsProduct v) (formsProduct v) := mixedPermanent_complexGram v v
    _ = _ := fockPair_self _

theorem firstCofactor_complexGram (v : V → C → ℂ) (i j : V) :
    firstCofactor (complexGram v) i j =
      fockPair (formsProduct (fun r : {r : V // r ≠ i} => v r.val))
        (formsProduct (fun c : {c : V // c ≠ j} => v c.val)) := by
  unfold firstCofactor
  change BapatFiniteRank.mixedPermanent (fun r : {r : V // r ≠ i} =>
    fun c : {c : V // c ≠ j} => ∑ k, v r.val k * star (v c.val k)) = _
  exact mixedPermanent_complexGram _ _

theorem psd_exists_complexGram (A : Matrix V V ℂ) (hA : A.PosSemidef) :
    ∃ v : V → V → ℂ, A = complexGram v := by
  let B := CFC.sqrt A
  have hB : B.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hBB : B * B = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  refine ⟨B, ?_⟩
  ext i j
  rw [← hBB]
  change (∑ k, B i k * B k j) = ∑ k, B i k * star (B j k)
  apply Finset.sum_congr rfl
  intro k _
  rw [← hB.apply k j]

theorem permanent_psd_real_nonneg (A : Matrix V V ℂ) (hA : A.PosSemidef) :
    ∃ r : ℝ, 0 ≤ r ∧ A.permanent = (r : ℂ) := by
  obtain ⟨v,rfl⟩ := psd_exists_complexGram A hA
  exact ⟨fockNormSq (formsProduct v), fockNormSq_nonneg _, permanent_complexGram v⟩

end
end CofactorSpectral
