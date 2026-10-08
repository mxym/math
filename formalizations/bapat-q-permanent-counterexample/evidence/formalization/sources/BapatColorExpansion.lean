import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic

/-! Two-color expansion of a product of linear polynomials. -/

namespace BapatFischer

set_option autoImplicit false

open Finset Polynomial
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The coefficient monomial selected by the indices using the X term. -/
def colorWeight (a b : ι → R) (s : Finset ι) : R :=
  (∏ i ∈ s, b i) * ∏ i ∈ sᶜ, a i

noncomputable def twoColorProduct (a b : ι → R) : R[X] :=
  ∏ i, (C (a i) + C (b i) * X)

theorem twoColorProduct_expand (a b : ι → R) :
    twoColorProduct a b =
      ∑ s : Finset ι, C (colorWeight a b s) * X ^ s.card := by
  unfold twoColorProduct
  simp_rw [add_comm (C (a _))]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, colorWeight]
  simp only [map_mul, map_prod]
  ac_rfl

theorem coeff_twoColorProduct (a b : ι → R) (k : ℕ) :
    (twoColorProduct a b).coeff k =
      ∑ s : Finset ι, if s.card = k then colorWeight a b s else 0 := by
  rw [twoColorProduct_expand, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro s hs
  simpa only [eq_comm] using Polynomial.coeff_C_mul_X_pow (colorWeight a b s) s.card k

theorem coeff_twoColorProduct_filter (a b : ι → R) (k : ℕ) :
    (twoColorProduct a b).coeff k =
      ∑ s : Finset ι with s.card = k, colorWeight a b s := by
  rw [coeff_twoColorProduct, Finset.sum_filter]

theorem colorWeight_map (a b : ι → R) (s : Finset ι) (σ : Equiv.Perm ι) :
    colorWeight a b (s.map σ.toEmbedding) =
      colorWeight (a ∘ σ) (b ∘ σ) s := by
  have hc : (s.map σ.toEmbedding)ᶜ = sᶜ.map σ.toEmbedding := by
    ext i
    simp
  simp only [colorWeight, hc, Finset.prod_map, Equiv.toEmbedding_apply,
    Function.comp_apply]

/-- This expansion starts from the genuine all-permutations permanent.
The four families are independent: this is already the bilinear form needed
for mixed Gram matrices, before specializing the right families to conjugates. -/
theorem permanent_twoColor_expand (a b c d : ι → R) :
    Matrix.permanent (fun i j => a i * c j + b i * d j) =
      ∑ σ : Equiv.Perm ι, ∑ s : Finset ι,
        colorWeight (a ∘ σ) (b ∘ σ) s * colorWeight c d s := by
  unfold Matrix.permanent
  apply Finset.sum_congr rfl
  intro σ hσ
  simp_rw [add_comm (a (σ _) * c _)]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [colorWeight, Function.comp_apply, Finset.prod_mul_distrib]
  ac_rfl

end BapatFischer
