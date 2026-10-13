import HydrologyTree.TreeMatrixSupport
import HydrologyTree.RingSiblingResidual

/-! Actual principal-matrix sibling resultants and edge-product weights over
arbitrary coefficient rings. These contain NO claimed Jacobian identity. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {R S : Type*} [CommRing R] [CommRing S]

def principalChildOver {n : ℕ} (t : OrderedTree n)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (c : RootChild t) :
    Matrix (Fin (childEdgeCount t c+1)) (Fin (childEdgeCount t c+1)) R :=
  A.submatrix (fun i => (childEnumeration t c i).val) (fun i => (childEnumeration t c i).val)

lemma principalChildOver_map (φ : R →+* S) {n : ℕ} (t : OrderedTree n)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (c : RootChild t) :
    (principalChildOver t A c).map φ=principalChildOver t (A.map φ) c := rfl

lemma principalChildOver_real {n : ℕ} (t : OrderedTree n) (A : TreeMatrix n) (c : RootChild t) :
    principalChildOver t A c=supportedChildMatrix t A c := rfl

def principalChildPolynomialList {n : ℕ} (t : OrderedTree n)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) : List R[X] :=
  List.ofFn fun i : Fin (Fintype.card (RootChild t)) =>
    (principalChildOver t A ((Fintype.equivFin (RootChild t)).symm i)).charpoly

lemma principalChildPolynomialList_monic {n : ℕ} (t : OrderedTree n)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    ∀ p ∈ principalChildPolynomialList t A,p.Monic := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact Matrix.charpoly_monic _

lemma principalChildPolynomialList_map (φ : R →+* S) {n : ℕ} (t : OrderedTree n)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    (principalChildPolynomialList t A).map (Polynomial.map φ)=principalChildPolynomialList t (A.map φ) := by
  simp only [principalChildPolynomialList,List.map_ofFn,Function.comp_def,← Matrix.charpoly_map,
    principalChildOver_map]

/-- Product of the actual squared sibling resultants over every principal subtree. -/
def matrixSiblingResidual {n : ℕ} (t : OrderedTree n)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) : R :=
  pairwiseResultantsOver (principalChildPolynomialList t A)^2*
    ∏ c : RootChild t,matrixSiblingResidual (childTree t c) (principalChildOver t A c)
termination_by n
decreasing_by exact childEdgeCount_lt t c

/-- Only actual edge products, each to the required descendant exponent. -/
def matrixEdgeWeight {n : ℕ} (t : OrderedTree n)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) : R :=
  ∏ c : RootChild t,(A 0 c.val*A c.val 0)^childEdgeCount t c*
    matrixEdgeWeight (childTree t c) (principalChildOver t A c)
termination_by n
decreasing_by exact childEdgeCount_lt t c

def matrixCoreWeight {n : ℕ} (t : OrderedTree n)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) : R := matrixEdgeWeight t A*matrixSiblingResidual t A

/-- Monicity makes specialization exact even at common-root and zero-rate boundaries. -/
theorem matrixSiblingResidual_map [Nontrivial S] (φ : R →+* S) {n : ℕ}
    (t : OrderedTree n) (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    φ (matrixSiblingResidual t A)=matrixSiblingResidual t (A.map φ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [matrixSiblingResidual]
    conv_rhs => rw [matrixSiblingResidual]
    rw [map_mul,map_pow,map_prod,← pairwiseResultantsOver_map φ _ (principalChildPolynomialList_monic t A),
      principalChildPolynomialList_map]
    congr 1
    apply Finset.prod_congr rfl
    intro c _
    rw [ih _ (childEdgeCount_lt t c),principalChildOver_map]

theorem matrixEdgeWeight_map (φ : R →+* S) {n : ℕ}
    (t : OrderedTree n) (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    φ (matrixEdgeWeight t A)=matrixEdgeWeight t (A.map φ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [matrixEdgeWeight]
    conv_rhs => rw [matrixEdgeWeight]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro c _
    rw [map_mul,map_pow,map_mul,ih _ (childEdgeCount_lt t c),principalChildOver_map]
    rfl

lemma matrixCoreWeight_map [Nontrivial S] (φ : R →+* S) {n : ℕ}
    (t : OrderedTree n) (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    φ (matrixCoreWeight t A)=matrixCoreWeight t (A.map φ) := by
  rw [matrixCoreWeight,map_mul,matrixEdgeWeight_map,matrixSiblingResidual_map]
  rfl

/-- The ring-valued actual principal residual specializes to the existing
physical root-leak residual, with no missing matrix/subtree bridge. -/
theorem matrixSiblingResidual_physical {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    matrixSiblingResidual t (compartmentMatrix t x)=originalTreeSiblingProduct t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hl : principalChildPolynomialList t (compartmentMatrix t x)=childCharacteristicListOver t x := by
      simp only [principalChildPolynomialList,childCharacteristicListOver,childRatesOver_real,
        modelCharacteristicOver_real,principalChildOver_real,supportedChild_physical,physicalCharacteristic]
    rw [matrixSiblingResidual,originalTreeSiblingProduct_recursion,hl,childCharacteristicListOver_real]
    congr 1
    apply Finset.prod_congr rfl
    intro c _
    rw [principalChildOver_real,supportedChild_physical]
    exact ih _ (childEdgeCount_lt t c) (childTree t c) (childRates t c x)

end HydrologyTree
