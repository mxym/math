import HydrologyTree.PathRates
import HydrologyTree.MatrixEntries
import HydrologyTree.PhysicalRecursion
import HydrologyTree.LeafRecursion

/-! The endpoint catenary is the original conservative OrderedTree matrix.
The root-tail recurrence is proved directly from every actual matrix entry. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

/-- The path 0--1--...--n, with leak and observation at vertex 0. -/
def pathTree (n : ℕ) : OrderedTree n where
  parent i := i.castSucc
  parent_le i := le_rfl

@[simp] lemma pathTree_parent (n : ℕ) (i : Fin n) : (pathTree n).parent i = i.castSucc := rfl

@[simp] lemma path_zero_ne_succ {n : ℕ} (i : Fin n) : (0 : Fin (n+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)

@[simp] lemma pathCast_zero (n : ℕ) : (0 : Fin (n+1)).castSucc = 0 := rfl

@[simp] lemma pathParent_succ {n : ℕ} (i : Fin n) :
    parentVertex (pathTree n) i.succ = i.castSucc := rfl

lemma pathCast_zero_iff {n : ℕ} (i : Fin (n+1)) : i.castSucc = 0 ↔ i = 0 := by
  constructor
  · intro h; exact Fin.ext (congrArg (fun j : Fin (n+2) => j.val) h)
  · intro h; subst i; rfl

lemma pathCast_succ {n : ℕ} (i : Fin n) : i.succ.castSucc = i.castSucc.succ := rfl

lemma path_root_exit (n : ℕ) (f : EdgeValues (n+1)) : parentCLM (pathTree (n+1)) f 0 = f 0 := by
  rw [parentCLM_apply]
  simp only [pathTree_parent, pathCast_zero_iff]; simp

lemma path_tail_exit (n : ℕ) (f : EdgeValues n) (g : ℝ) (i : Fin (n+1)) :
    parentCLM (pathTree (n+1)) (Fin.cons g f) i.succ = parentCLM (pathTree n) f i := by
  rw [parentCLM_apply, parentCLM_apply, Fin.sum_univ_succ]
  simp only [pathTree_parent, Fin.cons_zero, Fin.cons_succ, pathCast_succ,
    Fin.succ_inj, pathCast_zero, path_zero_ne_succ, ite_false, zero_add]
  rfl

lemma path_tail_offdiag (n : ℕ) (y : TreeRates n) (ell f : ℝ)
    (i j : Fin (n+1)) (hij : i ≠ j) :
    compartmentMatrix (pathTree (n+1)) (prependRateEquiv n (y,(ell,f))) i.succ j.succ =
      compartmentMatrix (pathTree n) y i j := by
  have hs : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
  rw [compartment_offdiag_parent_formula _ _ _ _ hs,
    compartment_offdiag_parent_formula _ _ _ _ hij]
  simp only [pathParent_succ, Fin.succ_ne_zero, ite_false, outwardByVertex_succ,
    prependRateEquiv_apply, Fin.cons_succ]
  revert hij
  refine Fin.cases ?_ (fun u => ?_) i
  · refine Fin.cases ?_ (fun v _ => ?_) j
    · intro h; exact False.elim (h rfl)
    · simp only [pathParent_succ, pathCast_succ, pathCast_zero, outwardByVertex_succ, Fin.succ_ne_zero, path_zero_ne_succ, ite_false, ite_true, Fin.cons_zero, Fin.cons_succ, Fin.succ_inj, zero_add, add_zero, eq_self]
      rfl
  · refine Fin.cases ?_ (fun v _ => ?_) j
    · intro h
      simp only [pathParent_succ, pathCast_succ, pathCast_zero, outwardByVertex_succ, Fin.succ_ne_zero, path_zero_ne_succ, ite_false, ite_true, Fin.cons_zero, Fin.cons_succ, Fin.succ_inj, zero_add, add_zero, eq_self]
      rfl
    · simp only [pathParent_succ, pathCast_succ, pathCast_zero, outwardByVertex_succ, Fin.succ_ne_zero, path_zero_ne_succ, ite_false, ite_true, Fin.cons_zero, Fin.cons_succ, Fin.succ_inj, zero_add, add_zero, eq_self]
      rfl

/-- The actual principal tail block is the smaller physical path, with its
exit-to-parent rate as its leak. No diagonal is reset or omitted. -/
theorem path_tail_matrix (n : ℕ) (y : TreeRates n) (ell f : ℝ) :
    (compartmentMatrix (pathTree (n+1)) (prependRateEquiv n (y,(ell,f)))).submatrix Fin.succ Fin.succ =
      compartmentMatrix (pathTree n) y := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.submatrix_apply, compartment_diagonal, rateChart,
      Pi.add_apply, prependRateEquiv_apply, Fin.cons_succ]
    rw [path_tail_exit]
  · exact path_tail_offdiag n y ell f i j h

lemma path_root_inward (n : ℕ) (y : TreeRates n) (ell f : ℝ) (i : Fin (n+1)) :
    compartmentMatrix (pathTree (n+1)) (prependRateEquiv n (y,(ell,f))) 0 i.succ =
      if i = 0 then y.1 0 else 0 := by
  rw [compartment_offdiag_parent_formula _ _ _ _ (path_zero_ne_succ i)]
  simp only [pathParent_succ, Fin.succ_ne_zero, ite_false, ite_true,
    prependRateEquiv_apply, Fin.cons_succ, pathCast_zero_iff, add_zero, eq_self]
  by_cases h : i = 0 <;> simp [h]

lemma path_root_outward (n : ℕ) (y : TreeRates n) (ell f : ℝ) (i : Fin (n+1)) :
    compartmentMatrix (pathTree (n+1)) (prependRateEquiv n (y,(ell,f))) i.succ 0 =
      if i = 0 then f else 0 := by
  rw [compartment_offdiag_parent_formula _ _ _ _ (Fin.succ_ne_zero i)]
  simp only [pathParent_succ, Fin.succ_ne_zero, ite_false, ite_true,
    outwardByVertex_succ, prependRateEquiv_apply, pathCast_zero_iff, zero_add, eq_self]
  by_cases h : i = 0 <;> simp [h]

def pathRootTailEquiv (n : ℕ) : Unit ⊕ Fin (n+1) ≃ Fin (n+2) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (.inl ()) Sum.inr
  left_inv z := by rcases z with u | i; cases u <;> rfl; rfl
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Exact root-tail edge attachment of the original physical path matrix. -/
theorem path_matrix_attachment (n : ℕ) (y : TreeRates n) (ell f : ℝ) :
    (compartmentMatrix (pathTree (n+1)) (prependRateEquiv n (y,(ell,f)))).submatrix
      (pathRootTailEquiv n) (pathRootTailEquiv n) =
      edgeJoin (singletonMatrix (-(ell+f))) (compartmentMatrix (pathTree n) y) () 0 (y.1 0) f := by
  ext u v
  rcases u with u | i <;> rcases v with v | j
  · cases u; cases v
    change compartmentMatrix _ _ 0 0 = -(ell+f)
    rw [compartment_diagonal]
    change -(ell + parentCLM (pathTree (n+1)) (Fin.cons f y.2) 0) = -(ell+f)
    rw [path_root_exit]
    rfl
  · cases u
    change compartmentMatrix _ _ 0 j.succ = Matrix.single () 0 (y.1 0) () j
    rw [path_root_inward]
    simp [Matrix.single_apply, eq_comm]
  · cases v
    change compartmentMatrix _ _ i.succ 0 = Matrix.single 0 () f i ()
    rw [path_root_outward]
    simp [Matrix.single_apply, eq_comm]
  · exact congrArg (fun A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => A i j)
      (path_tail_matrix n y ell f)

/-- Root cofactor recursion for the actual unreduced path model. -/
theorem path_cofactor_recursion (n : ℕ) (y : TreeRates n) (ell f : ℝ) :
    physicalRootCofactor (pathTree (n+1)) (prependRateEquiv n (y,(ell,f))) =
      physicalCharacteristic (pathTree n) y := by
  rw [physicalRootCofactor, path_tail_matrix]
  rfl

/-- The complete physical characteristic recurrence, valid at every real rate. -/
theorem path_characteristic_recursion (n : ℕ) (y : TreeRates n) (ell f : ℝ) :
    physicalCharacteristic (pathTree (n+1)) (prependRateEquiv n (y,(ell,f))) =
      (X+C (ell+f)) * physicalCharacteristic (pathTree n) y -
        C (y.1 0*f) * physicalRootCofactor (pathTree n) y := by
  rw [physicalCharacteristic, ← charpoly_submatrix_equiv _ (pathRootTailEquiv n),
    path_matrix_attachment, charpoly_edgeJoin, singletonMatrix_charpoly, singletonMatrix_cofactor,
    diagonalCofactor_zero]
  simp only [map_neg, sub_neg_eq_add, mul_one, physicalCharacteristic, physicalRootCofactor]

/-- Actual endpoint-path coefficient map in physical arrays. -/
def pathCoefficientMap (n : ℕ) (x : TreeRates n) : PathCoefficients n :=
  physicalCoefficientMap (pathTree n) x

theorem pathCoefficientMap_recursion (n : ℕ) (y : TreeRates n) (ell f : ℝ) :
    pathCoefficientMap (n+1) (prependRateEquiv n (y,(ell,f))) =
      pathStepCoefficients ((pathCoefficientMap n y).1,
        ((ell+f, y.1 0*f), (pathCoefficientMap n y).2)) := by
  apply Prod.ext
  · change cut (n+2) (physicalCharacteristic _ _) = _
    rw [path_characteristic_recursion]
    change _ = cut (n+2) ((X+C (ell+f)) * (monicPoly (physicalCoefficientMap (pathTree n) y).1 : ℝ[X]) -
      C (y.1 0*f) * (monicPoly (physicalCoefficientMap (pathTree n) y).2 : ℝ[X]))
    rw [physicalCoefficientMap_first_reconstruct, physicalCoefficientMap_second_reconstruct]
  · change cut (n+1) (physicalRootCofactor _ _) = _
    rw [path_cofactor_recursion]
    rfl

end HydrologyTree
