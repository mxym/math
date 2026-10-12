import HydrologyTree.SubtreeAssignment
import HydrologyTree.PositiveChildModels

/-! A uniform boundary construction: set all outward rates to zero. The actual
matrix becomes triangular, and injective inward rates give disjoint sibling
spectra throughout every finite tree. Positivity is deliberately not assumed. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

lemma outward_zero_function (n : ℕ) : outwardByVertex (0 : EdgeValues n) = 0 := by
  funext v
  exact Fin.cases rfl (fun _ => rfl) v

lemma zero_outward_upper_triangular {n : ℕ} (t : OrderedTree n) (a : VertexValues n) :
    (compartmentMatrix t (a,0)).IsUpperTriangular := by
  intro i j hji
  have hij : i ≠ j := ne_of_gt (show j < i from hji)
  rw [compartment_offdiag_parent_formula t (a,0) i j hij]
  have hparent : j ≠ 0 → parentVertex t j ≠ i := by
    intro hj hp
    have hlt := parentVertex_lt t j hj
    rw [hp] at hlt
    have hji' : j.val < i.val := hji
    omega
  by_cases hj : j = 0
  · simp [hj,outward_zero_function]
  · simp [hj,hparent hj,outward_zero_function]

/-- Exact factorization of the true characteristic polynomial on the entire
zero-outward-rate subspace, including arbitrary repeated and zero inward rates. -/
theorem zero_outward_characteristic {n : ℕ} (t : OrderedTree n) (a : VertexValues n) :
    physicalCharacteristic t (a,0) = ∏ v : Fin (n+1), (X+C (a v)) := by
  rw [physicalCharacteristic,Matrix.charpoly_of_isUpperTriangular _ (zero_outward_upper_triangular t a)]
  apply Finset.prod_congr rfl
  intro v _
  rw [compartment_diagonal]
  simp [rateChart]

lemma childRates_zero_outward {n : ℕ} (t : OrderedTree n) (c : RootChild t) (a : VertexValues n) :
    childRates t c (a,0) = ((fun i => a (childEnumeration t c i).val),0) := by
  apply Prod.ext
  · rfl
  · funext i
    simp [childRates,outward_zero_function]

lemma child_enumerations_distinct {n : ℕ} (t : OrderedTree n) (c d : RootChild t) (hcd : c ≠ d)
    (i : Fin (childEdgeCount t c+1)) (j : Fin (childEdgeCount t d+1)) :
    (childEnumeration t c i).val ≠ (childEnumeration t d j).val := by
  intro h
  apply hcd
  apply Subtype.ext
  have hb := congrArg (rootBranchVertex t) h
  rw [(childEnumeration t c i).property,(childEnumeration t d j).property] at hb
  exact hb

/-- Disjoint actual child-vertex sets and injective inward rates give coprime
child characteristic polynomials, even though every outward rate is zero. -/
theorem zero_outward_coprime_siblings {n : ℕ} (t : OrderedTree n) (a : VertexValues n)
    (ha : Function.Injective a) (c d : RootChild t) (hcd : c ≠ d) :
    IsCoprime (childCharacteristic t (a,0) c) (childCharacteristic t (a,0) d) := by
  change IsCoprime (physicalCharacteristic (childTree t c) (childRates t c (a,0)))
    (physicalCharacteristic (childTree t d) (childRates t d (a,0)))
  rw [childRates_zero_outward,childRates_zero_outward,zero_outward_characteristic,zero_outward_characteristic]
  apply IsCoprime.prod_left
  intro i _
  apply IsCoprime.prod_right
  intro j _
  apply coprime_linear_of_ne
  exact fun h => child_enumerations_distinct t c d hcd i j (ha h)

/-- The construction works recursively at every original vertex, not merely
at the observed root. It is a universal exact boundary witness, not a finite test. -/
theorem zero_outward_coprime_everywhere {n : ℕ} (t : OrderedTree n) (a : VertexValues n)
    (ha : Function.Injective a) : CoprimeAtEveryBranch t (a,0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [CoprimeAtEveryBranch]
    refine ⟨zero_outward_coprime_siblings t a ha,?_⟩
    intro c
    rw [childRates_zero_outward]
    exact ih (childEdgeCount t c) (childEdgeCount_lt t c) (childTree t c)
      (fun i => a (childEnumeration t c i).val) (ha.comp (childEnumeration_injective t c))

/-- An explicit injective real assignment vanishing at any specified vertex. -/
def separatingInward {n : ℕ} (j : Fin (n+1)) : VertexValues n :=
  fun v => (v.val : ℝ) - (j.val : ℝ)

lemma separatingInward_injective {n : ℕ} (j : Fin (n+1)) : Function.Injective (separatingInward j) := by
  intro u v h
  have hc : (u.val : ℝ) = (v.val : ℝ) := by
    dsimp [separatingInward] at h
    linarith
  apply Fin.ext
  exact_mod_cast hc

@[simp] lemma separatingInward_self {n : ℕ} (j : Fin (n+1)) : separatingInward j j = 0 := sub_self _

theorem zero_coordinate_coprime_witness {n : ℕ} (t : OrderedTree n) (j : Fin (n+1)) :
    (separatingInward j) j = 0 ∧ CoprimeAtEveryBranch t (separatingInward j,0) :=
  ⟨separatingInward_self j,zero_outward_coprime_everywhere t _ (separatingInward_injective j)⟩

end HydrologyTree
