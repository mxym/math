import HydrologyTree.ResidualFactors

/-! Exact real singular set of the full unreduced coefficient map, including
zero-rate boundary points. Leaf outward rates have exponent zero and are not
silently treated as obligatory nonzero coordinates. -/
noncomputable section
namespace HydrologyTree

lemma originalTreeRateMonomial_zero_iff {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    originalTreeRateMonomial t x = 0 ↔
      (∃ e : Fin n, x.1 e.succ = 0) ∨
      (∃ e : Fin n, 1 < subtreeVertexCount t e.succ ∧ x.2 e = 0) := by
  rw [originalTreeRateMonomial,Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨e,_,he⟩
    rcases mul_eq_zero.mp he with ha | hf
    · left
      refine ⟨e,?_⟩
      by_contra h
      exact pow_ne_zero _ h ha
    · right
      have hp : 0 < subtreeVertexCount t e.succ-1 := by
        by_contra h
        have hz : subtreeVertexCount t e.succ-1 = 0 := Nat.eq_zero_of_not_pos h
        rw [hz,pow_zero] at hf
        exact one_ne_zero hf
      refine ⟨e,by omega,?_⟩
      by_contra h
      exact pow_ne_zero _ h hf
  · rintro (⟨e,he⟩ | ⟨e,hsize,he⟩)
    · refine ⟨e,Finset.mem_univ e,?_⟩
      have hp : subtreeVertexCount t e.succ ≠ 0 := Nat.ne_of_gt (subtreeVertexCount_pos t e.succ)
      simp [he,hp]
    · refine ⟨e,Finset.mem_univ e,?_⟩
      have hp : subtreeVertexCount t e.succ-1 ≠ 0 := by omega
      simp [he,hp]

/-- Full real singular-locus classification for all rates, not just positive
models. The residual condition uses actual coprimality at each principal sibling
family and is valid even at zero inward/outward rates. -/
theorem treeJacobian_zero_iff_all_rates {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    treeCanonicalJacobian t x = 0 ↔
      (∃ e : Fin n, x.1 e.succ = 0) ∨
      (∃ e : Fin n, 1 < subtreeVertexCount t e.succ ∧ x.2 e = 0) ∨
      ¬CoprimeAtEveryBranch t x := by
  have he : treeProofOrientation t ≠ 0 := by
    rcases treeProofOrientation_sign t with h | h <;> rw [h] <;> norm_num
  have hR : originalTreeSiblingProduct t x = 0 ↔ ¬CoprimeAtEveryBranch t x := by
    have h := siblingProduct_ne_zero_iff_coprime t x
    constructor
    · intro hz hc
      exact h.mpr hc hz
    · intro hc
      by_contra hz
      exact hc (h.mp hz)
  rw [all_tree_canonical_jacobian,allTreeJacobianWeight_eq_original_products,mul_eq_zero,
    mul_eq_zero,originalTreeRateMonomial_zero_iff,hR]
  constructor
  · rintro (h | ((ha | hf) | hc))
    · exact False.elim (he h)
    · exact Or.inl ha
    · exact Or.inr (Or.inl hf)
    · exact Or.inr (Or.inr hc)
  · rintro (ha | hf | hc)
    · exact Or.inr (Or.inl (Or.inl ha))
    · exact Or.inr (Or.inl (Or.inr hf))
    · exact Or.inr (Or.inr hc)

end HydrologyTree
