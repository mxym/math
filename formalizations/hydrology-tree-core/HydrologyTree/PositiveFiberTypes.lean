import HydrologyTree.PositiveFiberAllocation

/-! Actual positive parameter fibers and canonical normalized child data.
Positivity concerns every original directed rate and the actual root leak. -/
open Polynomial
noncomputable section
namespace HydrologyTree

abbrev PositivePolynomialFiber {n : ℕ} (t : OrderedTree n) (P F : ℝ[X]) :=
  {x : TreeRates n // PositiveRateVector x ∧ physicalCharacteristic t x=P ∧ physicalRootCofactor t x=F}

abbrev PositiveStieltjesFiber {n : ℕ} (t : OrderedTree n) (r w : Fin (n+1) → ℝ) :=
  PositivePolynomialFiber t (stieltjesDenominator r) (stieltjesNumerator r w)

abbrev PositiveReciprocalFiber {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) (d : ℝ) :=
  PositivePolynomialFiber t ((X+C d)*stieltjesDenominator b-stieltjesNumerator b g)
    (stieltjesDenominator b)

def allocatedResidueMass {n : ℕ} (t : OrderedTree n) (g : Fin n → ℝ)
    (a : TreePoleAllocation t) (c : RootChild t) : ℝ :=
  ∑ i : Fin (childEdgeCount t c+1), g (allocationEquiv a ⟨c,i⟩)

def allocatedWeights {n : ℕ} (t : OrderedTree n) (g : Fin n → ℝ)
    (a : TreePoleAllocation t) (c : RootChild t) : Fin (childEdgeCount t c+1) → ℝ :=
  fun i => g (allocationEquiv a ⟨c,i⟩)/allocatedResidueMass t g a c

abbrev AllocatedChildFibers {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ)
    (a : TreePoleAllocation t) :=
  (c : RootChild t) → PositiveStieltjesFiber (childTree t c)
    (allocatedRates b a c) (allocatedWeights t g a c)

lemma allocatedRates_injective {n : ℕ} (t : OrderedTree n) (b : Fin n → ℝ)
    (hb : Function.Injective b) (a : TreePoleAllocation t) (c : RootChild t) :
    Function.Injective (allocatedRates b a c) := by
  intro i j hij
  have h := (allocationEquiv a).injective (hb hij)
  exact Fin.ext (congrArg (fun z : NumberedChildNodes t => z.2.val) h)

lemma allocatedResidueMass_pos {n : ℕ} (t : OrderedTree n) (g : Fin n → ℝ)
    (hg : ∀ i, 0 < g i) (a : TreePoleAllocation t) (c : RootChild t) :
    0 < allocatedResidueMass t g a c :=
  Finset.sum_pos (fun i _ => hg _) Finset.univ_nonempty

lemma allocatedWeights_pos {n : ℕ} (t : OrderedTree n) (g : Fin n → ℝ)
    (hg : ∀ i, 0 < g i) (a : TreePoleAllocation t) (c : RootChild t) :
    ∀ i, 0 < allocatedWeights t g a c i :=
  fun i => div_pos (hg _) (allocatedResidueMass_pos t g hg a c)

lemma allocatedWeights_sum {n : ℕ} (t : OrderedTree n) (g : Fin n → ℝ)
    (hg : ∀ i, 0 < g i) (a : TreePoleAllocation t) (c : RootChild t) :
    (∑ i, allocatedWeights t g a c i)=1 := by
  simp only [allocatedWeights]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (allocatedResidueMass_pos t g hg a c))

/-- Every prescribed labelled allocation has genuine positive child models;
this uses the already proved all-tree existence theorem without a new hypothesis. -/
theorem allocatedChildFibers_nonempty {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ)
    (hb : Function.Injective b) (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i)
    (a : TreePoleAllocation t) : Nonempty (AllocatedChildFibers t b g a) := by
  have hc (c : RootChild t) : Nonempty (PositiveStieltjesFiber (childTree t c)
      (allocatedRates b a c) (allocatedWeights t g a c)) := by
    obtain ⟨y,hy,hP,hF⟩ := positive_tree_stieltjes_realization_exists (childTree t c)
      (allocatedRates b a c) (allocatedWeights t g a c)
      (allocatedRates_injective t b hb a c) (fun i => hpos _)
      (allocatedWeights_pos t g hg a c) (allocatedWeights_sum t g hg a c)
    exact ⟨⟨y,hy,hP,hF⟩⟩
  exact ⟨fun c => Classical.choice (hc c)⟩

/-- Each admissible allocation and each tuple of actual positive child models
assemble to a genuine positive parent model with exact prescribed polynomials. -/
theorem allocatedChildren_assemble {n : ℕ} (t : OrderedTree n) (b g : Fin n → ℝ) (d : ℝ)
    (hpos : ∀ i, 0 < b i) (hg : ∀ i, 0 < g i) (hl : 0 < d-∑ i, g i/b i)
    (a : TreePoleAllocation t) (y : AllocatedChildFibers t b g a) :
    ∃ x : PositiveReciprocalFiber t b g d, ∀ c, childRates t c x.val=(y c).val := by
  obtain ⟨x,hx,hF,hP,hchild⟩ := assemble_positive_stieltjes_children t (allocationEquiv a)
    b g d hpos hg hl (fun c => (y c).val) (fun c => (y c).property.1)
    (fun c => (y c).property.2.1) (fun c => (y c).property.2.2)
  exact ⟨⟨x,hx,hP,hF⟩,hchild⟩

end HydrologyTree
