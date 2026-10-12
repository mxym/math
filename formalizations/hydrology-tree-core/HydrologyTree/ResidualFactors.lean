import HydrologyTree.SubtreeProducts
import HydrologyTree.JacobianRegularity
import HydrologyTree.ZeroOutward

/-! Universal coordinate-boundary witnesses and absence of hidden individual
rate factors in the actual full sibling-resultant residual. This is an exact
functional nondivisibility theorem, not a finite specialization test. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- The residual has no rate monomial factors: at arbitrary rates it is nonzero
precisely when all actual sibling characteristic polynomials are coprime. -/
theorem siblingProduct_ne_zero_iff_coprime {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    originalTreeSiblingProduct t x ≠ 0 ↔ CoprimeAtEveryBranch t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hchildren : (∏ c : RootChild t,
        originalTreeSiblingProduct (childTree t c) (childRates t c x)) ≠ 0 ↔
        ∀ c : RootChild t, CoprimeAtEveryBranch (childTree t c) (childRates t c x) := by
      rw [Finset.prod_ne_zero_iff]
      simp only [Finset.mem_univ,true_implies]
      exact forall_congr' fun c => ih (childEdgeCount t c) (childEdgeCount_lt t c)
        (childTree t c) (childRates t c x)
    rw [originalTreeSiblingProduct_recursion,mul_ne_zero_iff,real_square_ne_zero_iff,
      treeSiblingResultant_ne_zero_iff,hchildren,CoprimeAtEveryBranch]

/-- A single explicit all-size witness: all outward rates vanish and the inward
rates are distinct with the selected coordinate exactly zero. -/
theorem siblingProduct_separating_witness {n : ℕ} (t : OrderedTree n) (j : Fin (n+1)) :
    originalTreeSiblingProduct t (separatingInward j,0) ≠ 0 :=
  (siblingProduct_ne_zero_iff_coprime t _).mpr
    (zero_outward_coprime_everywhere t _ (separatingInward_injective j))

theorem siblingProduct_inward_hyperplane_witness {n : ℕ} (t : OrderedTree n) (j : Fin (n+1)) :
    ∃ x : TreeRates n, x.1 j = 0 ∧ originalTreeSiblingProduct t x ≠ 0 :=
  ⟨(separatingInward j,0),separatingInward_self j,siblingProduct_separating_witness t j⟩

theorem siblingProduct_outward_hyperplane_witness {n : ℕ} (t : OrderedTree n) (e : Fin n) :
    ∃ x : TreeRates n, x.2 e = 0 ∧ originalTreeSiblingProduct t x ≠ 0 :=
  ⟨(separatingInward (0 : Fin (n+1)),0),rfl,siblingProduct_separating_witness t 0⟩

/-- Even among arbitrary real-valued quotient functions, no inward coordinate
can be factored out of the sibling residual globally. In particular a polynomial
coordinate factor is impossible; polynomial multiplicity bookkeeping is separate. -/
theorem siblingProduct_no_inward_factor {n : ℕ} (t : OrderedTree n) (j : Fin (n+1)) :
    ¬∃ q : TreeRates n → ℝ, ∀ x : TreeRates n,
      originalTreeSiblingProduct t x = x.1 j * q x := by
  rintro ⟨q,hq⟩
  obtain ⟨x,hx,hR⟩ := siblingProduct_inward_hyperplane_witness t j
  apply hR
  rw [hq x,hx,zero_mul]

/-- No outward coordinate is a hidden factor in the residual either. The
zero-outward construction proves this for every edge of every finite tree. -/
theorem siblingProduct_no_outward_factor {n : ℕ} (t : OrderedTree n) (e : Fin n) :
    ¬∃ q : TreeRates n → ℝ, ∀ x : TreeRates n,
      originalTreeSiblingProduct t x = x.2 e * q x := by
  rintro ⟨q,hq⟩
  obtain ⟨x,hx,hR⟩ := siblingProduct_outward_hyperplane_witness t e
  apply hR
  rw [hq x,hx,zero_mul]

/-- The all-tree residual is not the zero function. -/
theorem siblingProduct_not_identically_zero {n : ℕ} (t : OrderedTree n) :
    ¬∀ x : TreeRates n, originalTreeSiblingProduct t x = 0 := by
  intro h
  exact siblingProduct_separating_witness t 0 (h (separatingInward 0,0))

end HydrologyTree
