import CholletPSD

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial BapatFiniteRank

namespace Chollet

variable {V C J : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C]
noncomputable section

@[simp] theorem pair_one_self :
    fischerPair (1 : MvPolynomial C ℝ) 1 = 1 := by
  change fischerPair (monomial 0 1) (monomial 0 1) = 1
  rw [pair_monomials]
  simp [multiFactorial]

@[simp] theorem directional_one (u : C → ℝ) :
    directional u (1 : MvPolynomial C ℝ) = 0 := by
  simp [directional]

@[simp] theorem directional_zero (u : C → ℝ) :
    directional u (0 : MvPolynomial C ℝ) = 0 := by
  simp [directional]

theorem pair_linearForm_self (u : C → ℝ) :
    fischerPair (linearForm u) (linearForm u) = scalarProduct u u := by
  simpa using linear_factor_norm_identity u 1

theorem pair_quadratic_self (u v : C → ℝ) :
    fischerPair (linearForm u * linearForm v) (linearForm u * linearForm v) =
      scalarProduct u u * scalarProduct v v + (scalarProduct u v)^2 := by
  simpa using quadratic_factor_norm_identity u v 1

def formsOn (v : V → C → ℝ) (s : Finset V) : MvPolynomial C ℝ :=
  ∏ i ∈ s, linearForm (v i)

theorem formsOn_eq_formsProduct (v : V → C → ℝ) (s : Finset V) :
    formsOn v s = formsProduct (fun i : s => v i.val) := by
  exact (Finset.prod_coe_sort s (fun i => linearForm (v i))).symm

theorem small_block_norm_bound (v : V → C → ℝ) (s : Finset V) (hs : s.card ≤ 2)
    (q : MvPolynomial C ℝ) :
    fischerPair (formsOn v s) (formsOn v s) * fischerPair q q ≤
      fischerPair (formsOn v s * q) (formsOn v s * q) := by
  have hc : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases hc with hc | hc | hc
  · have he : s = ∅ := Finset.card_eq_zero.mp hc
    subst s
    simp [formsOn]
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    simpa [formsOn, pair_linearForm_self] using linear_factor_norm_bound (v i) q
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hc
    simpa [formsOn, hij, pair_quadratic_self, mul_assoc] using
      quadratic_factor_norm_bound (v i) (v j) q

theorem product_small_blocks_norm_bound [DecidableEq J] (v : V → C → ℝ)
    (t : Finset J) (s : J → Finset V) (hs : ∀ j ∈ t, (s j).card ≤ 2) :
    (∏ j ∈ t, fischerPair (formsOn v (s j)) (formsOn v (s j))) ≤
      fischerPair (∏ j ∈ t, formsOn v (s j)) (∏ j ∈ t, formsOn v (s j)) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    calc
      _ ≤ fischerPair (formsOn v (s j)) (formsOn v (s j)) *
          fischerPair (∏ k ∈ t, formsOn v (s k)) (∏ k ∈ t, formsOn v (s k)) :=
        mul_le_mul_of_nonneg_left (ih (fun k hk => hs k (Finset.mem_insert_of_mem hk)))
          (pair_self_nonneg _)
      _ ≤ _ := small_block_norm_bound v (s j) (hs j (Finset.mem_insert_self _ _)) _

/-- Actual finite PSD principal blocks of size at most two. Blocks are disjoint
and cover the index set; empty blocks are allowed. -/
theorem permanent_psd_small_partition [DecidableEq J] (A : Matrix V V ℝ)
    (hA : A.PosSemidef) (t : Finset J) (s : J → Finset V)
    (hdisj : (t : Set J).PairwiseDisjoint s)
    (hcover : t.biUnion s = Finset.univ)
    (hsmall : ∀ j ∈ t, (s j).card ≤ 2) :
    (∏ j ∈ t, Matrix.permanent
      (A.submatrix (fun i : s j => i.val) Subtype.val)) ≤ A.permanent := by
  obtain ⟨v, hv⟩ := psd_exists_gram A hA
  have ha : A = fun i j => scalarProduct (v i) (v j) := by ext i j; exact hv i j
  have hb (j : J) : Matrix.permanent
      (A.submatrix (fun i : s j => i.val) Subtype.val) =
      fischerPair (formsOn v (s j)) (formsOn v (s j)) := by
    rw [ha, formsOn_eq_formsProduct]
    exact permanent_gram_eq _
  simp_rw [hb]
  rw [ha, permanent_gram_eq]
  have hp : (∏ j ∈ t, formsOn v (s j)) = formsProduct v := by
    unfold formsOn formsProduct
    rw [← Finset.prod_biUnion hdisj, hcover]
  rw [← hp]
  exact product_small_blocks_norm_bound v t s hsmall

theorem diagonal_product_norm_bound (v : V → C → ℝ) (s : Finset V) :
    (∏ i ∈ s, scalarProduct (v i) (v i)) ≤ fischerPair (formsOn v s) (formsOn v s) := by
  induction s using Finset.induction_on with
  | empty => simp [formsOn]
  | @insert i s hi ih =>
    simp only [formsOn, Finset.prod_insert hi] at *
    exact (mul_le_mul_of_nonneg_left ih (scalarProduct_self_nonneg _)).trans
      (linear_factor_norm_bound _ _)

/-- Marcus's diagonal-product lower bound, including singular PSD matrices. -/
theorem permanent_psd_ge_diag_product (A : Matrix V V ℝ) (hA : A.PosSemidef) :
    (∏ i, A i i) ≤ A.permanent := by
  obtain ⟨v, hv⟩ := psd_exists_gram A hA
  have h : A = fun i j => scalarProduct (v i) (v j) := by ext i j; exact hv i j
  rw [h, permanent_gram_eq]
  exact diagonal_product_norm_bound v Finset.univ

end
end Chollet
