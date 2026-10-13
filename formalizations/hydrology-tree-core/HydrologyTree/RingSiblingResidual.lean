import HydrologyTree.RingTreeModel
import HydrologyTree.RingPairwiseResultants
import HydrologyTree.SubtreeProducts

/-! Polynomial construction of the complete sibling residual. All coefficient
specializations are checked against actual principal child matrices. -/
open Polynomial
noncomputable section
namespace HydrologyTree

variable {R S : Type*} [CommRing R] [CommRing S]

/-- All actual child characteristic polynomials over the chosen coefficient ring. -/
def childCharacteristicListOver {n : ℕ} (t : OrderedTree n) (x : RatesOver R n) : List R[X] :=
  List.ofFn fun i : Fin (Fintype.card (RootChild t)) =>
    let c := (Fintype.equivFin (RootChild t)).symm i
    modelCharacteristicOver (childTree t c) (childRatesOver t c x)

lemma childCharacteristicListOver_monic {n : ℕ} (t : OrderedTree n) (x : RatesOver R n) :
    ∀ p ∈ childCharacteristicListOver t x, p.Monic := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact modelCharacteristicOver_monic _ _

lemma childCharacteristicListOver_map (φ : R →+* S) {n : ℕ}
    (t : OrderedTree n) (x : RatesOver R n) :
    (childCharacteristicListOver t x).map (Polynomial.map φ) =
      childCharacteristicListOver t (ratesOverMap φ x) := by
  simp only [childCharacteristicListOver,List.map_ofFn,Function.comp_def,
    modelCharacteristicOver_map,childRatesOver_map]

/-- Exact recursive residual over arbitrary ring-valued physical rate coordinates. -/
def siblingResidualOver {n : ℕ} (t : OrderedTree n) (x : RatesOver R n) : R :=
  pairwiseResultantsOver (childCharacteristicListOver t x)^2 *
    ∏ c : RootChild t, siblingResidualOver (childTree t c) (childRatesOver t c x)
termination_by n
decreasing_by exact childEdgeCount_lt t c

/-- Specialization of the actual recursive resultant residual commutes with
every coefficient homomorphism to a nontrivial ring. -/
theorem siblingResidualOver_map [Nontrivial S] (φ : R →+* S) {n : ℕ}
    (t : OrderedTree n) (x : RatesOver R n) :
    φ (siblingResidualOver t x) = siblingResidualOver t (ratesOverMap φ x) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [siblingResidualOver]
    conv_rhs => rw [siblingResidualOver]
    rw [map_mul,map_pow,map_prod,
      ← pairwiseResultantsOver_map φ _ (childCharacteristicListOver_monic t x),
      childCharacteristicListOver_map]
    congr 1
    apply Finset.prod_congr rfl
    intro c _
    rw [ih _ (childEdgeCount_lt t c),childRatesOver_map]

lemma pairwiseResultantsOver_real (ps : List ℝ[X]) :
    pairwiseResultantsOver ps = pairwiseResultants ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [pairwiseResultantsOver,pairwiseResultants,ih]

lemma childCharacteristicListOver_real {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    pairwiseResultantsOver (childCharacteristicListOver t x) = treeSiblingResultant t x := by
  rw [pairwiseResultantsOver_real]
  simp only [childCharacteristicListOver,childRatesOver_real,modelCharacteristicOver_real,
    treeSiblingResultant,childCharacteristic]

/-- This ring expression is the previously proved actual physical residual,
not a substitute model with an unproved identification. -/
theorem siblingResidualOver_real {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    siblingResidualOver t x = originalTreeSiblingProduct t x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [siblingResidualOver,originalTreeSiblingProduct_recursion,childCharacteristicListOver_real]
    congr 1
    apply Finset.prod_congr rfl
    intro c _
    rw [childRatesOver_real]
    exact ih _ (childEdgeCount_lt t c) (childTree t c) (childRates t c x)

end HydrologyTree
