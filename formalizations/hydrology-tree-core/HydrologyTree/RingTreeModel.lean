import HydrologyTree.ChildIndex
import HydrologyTree.Resolvent

/-! The same physical tree over an arbitrary commutative coefficient ring.
This is used to construct, not assume, the multivariate Jacobian polynomial. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

abbrev RatesOver (R : Type*) (n : ℕ) := (Fin (n+1) → R) × (Fin n → R)

variable {R S : Type*} [CommRing R] [CommRing S]

def ratesOverMap (φ : R →+* S) {n : ℕ} (x : RatesOver R n) : RatesOver S n :=
  (fun i => φ (x.1 i), fun e => φ (x.2 e))

/-- Exactly the edge-conservative generator, now with ring-valued rates. -/
def modelMatrixOver {n : ℕ} (t : OrderedTree n) (x : RatesOver R n) :
    Matrix (Fin (n+1)) (Fin (n+1)) R :=
  (∑ e : Fin n,
    (x.1 e.succ • (Matrix.single (t.parent e) e.succ (1 : R) - Matrix.single e.succ e.succ 1) +
      x.2 e • (Matrix.single e.succ (t.parent e) (1 : R) - Matrix.single (t.parent e) (t.parent e) 1))) -
    x.1 0 • Matrix.single 0 0 (1 : R)

lemma modelMatrixOver_real {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    modelMatrixOver t x = compartmentMatrix t x := rfl

lemma scalarMatrix_specialize (φ : R →+* S) {n : ℕ} (c : R)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    φ.mapMatrix (c • A) = φ c • φ.mapMatrix A := by
  ext i j
  simp only [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_mul]

lemma singleMatrix_specialize (φ : R →+* S) {n : ℕ}
    (i j : Fin (n+1)) (c : R) :
    φ.mapMatrix (Matrix.single i j c) = Matrix.single i j (φ c) := by
  ext k l
  simp only [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.single_apply]
  by_cases h : i=k ∧ j=l <;> simp [h]

lemma modelMatrixOver_map (φ : R →+* S) {n : ℕ} (t : OrderedTree n) (x : RatesOver R n) :
    (modelMatrixOver t x).map φ = modelMatrixOver t (ratesOverMap φ x) := by
  change φ.mapMatrix (modelMatrixOver t x) = _
  simp only [modelMatrixOver,map_sub,map_sum,map_add,scalarMatrix_specialize,
    singleMatrix_specialize,map_one]
  rfl

/-- The actual characteristic polynomial over the coefficient ring. -/
def modelCharacteristicOver {n : ℕ} (t : OrderedTree n) (x : RatesOver R n) : R[X] :=
  (modelMatrixOver t x).charpoly

lemma modelCharacteristicOver_real {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    modelCharacteristicOver t x = physicalCharacteristic t x := rfl

lemma modelCharacteristicOver_map (φ : R →+* S) {n : ℕ}
    (t : OrderedTree n) (x : RatesOver R n) :
    (modelCharacteristicOver t x).map φ = modelCharacteristicOver t (ratesOverMap φ x) := by
  rw [modelCharacteristicOver,← Matrix.charpoly_map,modelMatrixOver_map]
  rfl

lemma modelCharacteristicOver_monic {n : ℕ} (t : OrderedTree n) (x : RatesOver R n) :
    (modelCharacteristicOver t x).Monic := Matrix.charpoly_monic _

lemma modelCharacteristicOver_degree [Nontrivial R] {n : ℕ}
    (t : OrderedTree n) (x : RatesOver R n) : (modelCharacteristicOver t x).natDegree = n+1 := by
  simp [modelCharacteristicOver]

/-- Subtree rate extraction is a coordinate selection, over any scalar ring. -/
def childRatesOver {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : RatesOver R n) :
    RatesOver R (childEdgeCount t c) :=
  (fun i => x.1 (childEnumeration t c i).val,
    fun i => x.2 (numberedEdgeEquiv t ⟨c,i.succ⟩))

lemma childRatesOver_real {n : ℕ} (t : OrderedTree n) (c : RootChild t) (x : TreeRates n) :
    childRatesOver t c x = childRates t c x := by
  apply Prod.ext
  · rfl
  · funext e
    exact outward_at_numbered_child t x.2 c e.succ

lemma childRatesOver_map (φ : R →+* S) {n : ℕ}
    (t : OrderedTree n) (c : RootChild t) (x : RatesOver R n) :
    ratesOverMap φ (childRatesOver t c x) = childRatesOver t c (ratesOverMap φ x) := rfl

end HydrologyTree
