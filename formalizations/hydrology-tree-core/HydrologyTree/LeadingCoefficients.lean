import HydrologyTree.Coefficients

/-! Leading-coefficient charts for the actual bounded polynomial spaces. -/
open Polynomial Module
noncomputable section
namespace HydrologyTree

lemma monic_monicPoly {n : ℕ} (p : Coeff n) : (monicPoly p : ℝ[X]).Monic := by
  rw [coe_monicPoly]
  exact Polynomial.monic_X_pow_add (Polynomial.mem_degreeLT.mp p.property)

@[simp] lemma monicPoly_coeff_top {n : ℕ} (p : Coeff n) :
    (monicPoly p : ℝ[X]).coeff n = 1 := by
  simp [coe_monicPoly, coeff_eq_zero_of_bound p le_rfl]

@[simp] lemma natDegree_monicPoly {n : ℕ} (p : Coeff n) :
    (monicPoly p : ℝ[X]).natDegree = n := by
  apply le_antisymm (bounded_natDegree _)
  exact Polynomial.le_natDegree_of_ne_zero (by
    rw [monicPoly_coeff_top]
    exact one_ne_zero)

lemma cut_X_pow_of_le (n k : ℕ) (hnk : n ≤ k) : cut n (X^k) = 0 := by
  apply (degreeLTEquiv ℝ n).injective
  funext i
  change ((cut n (X^k) : Coeff n) : ℝ[X]).coeff i = 0
  rw [cut_coeff]
  simp [Polynomial.coeff_X_pow, show (i : ℕ) ≠ k from by omega]

/-- Assemble a leading coefficient and all lower coefficients, without division. -/
def joinLeadingLM (n : ℕ) : (ℝ × Coeff n) →ₗ[ℝ] Coeff (n+1) where
  toFun x := x.1 • topMonomial n + liftCLM n x.2
  map_add' x y := by simp [add_smul]; abel
  map_smul' c x := by simp [smul_add, smul_smul]

@[simp] lemma coe_joinLeadingLM {n : ℕ} (x : ℝ × Coeff n) :
    (joinLeadingLM n x : ℝ[X]) = x.1 • (X^n : ℝ[X]) + (x.2 : ℝ[X]) := by
  simp [joinLeadingLM, topMonomial]

/-- Split a bounded polynomial into its leading coefficient and its truncation. -/
def splitLeadingLM (n : ℕ) : Coeff (n+1) →ₗ[ℝ] (ℝ × Coeff n) :=
  ((Polynomial.lcoeff ℝ n).comp (degreeLT ℝ (n+1)).subtype).prod
    ((cut n).comp (degreeLT ℝ (n+1)).subtype)

@[simp] lemma splitLeadingLM_apply {n : ℕ} (p : Coeff (n+1)) :
    splitLeadingLM n p = ((p : ℝ[X]).coeff n, cut n (p : ℝ[X])) := rfl

lemma split_joinLeading {n : ℕ} (x : ℝ × Coeff n) :
    splitLeadingLM n (joinLeadingLM n x) = x := by
  apply Prod.ext
  · simp [coe_joinLeadingLM, coeff_eq_zero_of_bound x.2 le_rfl]
  · simp [coe_joinLeadingLM, cut_X_pow_of_le n n le_rfl]

lemma join_splitLeading {n : ℕ} (p : Coeff (n+1)) :
    joinLeadingLM n (splitLeadingLM n p) = p := by
  apply Subtype.ext
  rw [coe_joinLeadingLM]
  ext k
  simp only [splitLeadingLM_apply, Polynomial.coeff_add, Polynomial.coeff_smul,
    smul_eq_mul, Polynomial.coeff_X_pow]
  rcases lt_trichotomy k n with h | h | h
  · rw [if_neg (ne_of_lt h), mul_zero, zero_add]
    exact cut_coeff n (p : ℝ[X]) ⟨k,h⟩
  · subst k
    rw [if_pos rfl, mul_one, coeff_eq_zero_of_bound _ le_rfl, add_zero]
  · rw [if_neg (ne_of_gt h), mul_zero,
      coeff_eq_zero_of_bound _ h.le, zero_add,
      coeff_eq_zero_of_bound p (by omega)]

/-- The exact linear isomorphism between high-first and ordinary polynomial coefficients. -/
def leadingEquiv (n : ℕ) : (ℝ × Coeff n) ≃ₗ[ℝ] Coeff (n+1) :=
  { joinLeadingLM n with
    invFun := splitLeadingLM n
    left_inv := split_joinLeading
    right_inv := join_splitLeading }

@[simp] lemma leadingEquiv_apply {n : ℕ} (x : ℝ × Coeff n) :
    leadingEquiv n x = joinLeadingLM n x := rfl

@[simp] lemma leadingEquiv_symm_apply {n : ℕ} (p : Coeff (n+1)) :
    (leadingEquiv n).symm p = splitLeadingLM n p := rfl

lemma monicPoly_eq_leadingEquiv {n : ℕ} (p : Coeff n) :
    monicPoly p = leadingEquiv n (1,p) := by
  simp [monicPoly, leadingEquiv, joinLeadingLM]

/-- Leading degree first, then increasing lower degrees. -/
def leadingBasis (n : ℕ) : Basis (Unit ⊕ Fin n) ℝ (Coeff (n+1)) :=
  ((Basis.singleton Unit ℝ).prod (degreeLT.basis ℝ n)).map (leadingEquiv n)

/-- Truncation is exact whenever the original polynomial already satisfies the bound. -/
lemma coe_cut_of_degree_lt {n : ℕ} (p : ℝ[X]) (hp : p.degree < n) :
    (cut n p : ℝ[X]) = p := by
  let q : Coeff n := ⟨p, Polynomial.mem_degreeLT.mpr hp⟩
  exact congrArg (fun z : Coeff n => (z : ℝ[X])) (cut_coe q)

/-- Actual monic polynomials are recovered from their non-leading coefficients. -/
lemma monic_reconstruct {n : ℕ} (p : ℝ[X]) (hp : p.Monic) (hd : p.natDegree = n) :
    (monicPoly (cut n p) : ℝ[X]) = p := by
  ext k
  rw [coe_monicPoly, Polynomial.coeff_add, Polynomial.coeff_X_pow]
  rcases lt_trichotomy k n with hk | hk | hk
  · rw [if_neg (ne_of_lt hk), zero_add]
    exact cut_coeff n p ⟨k,hk⟩
  · subst k
    rw [if_pos rfl, coeff_eq_zero_of_bound _ le_rfl, add_zero]
    rw [← hd, Polynomial.coeff_natDegree, hp]
  · rw [if_neg (ne_of_gt hk), zero_add,
      coeff_eq_zero_of_bound _ hk.le,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

end HydrologyTree
