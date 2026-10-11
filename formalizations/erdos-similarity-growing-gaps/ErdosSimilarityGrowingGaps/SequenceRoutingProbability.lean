import ErdosSimilarityGrowingGaps.SequenceRouting
import ErdosSimilarityGrowingGaps.RoutingLaw

namespace ErdosSimilarityGrowingGaps

open Set
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def sequenceActiveLocalCandidates
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (k : ℤ) (p : PowerParams s₀ s₁) : Finset (Fin P) :=
  Finset.univ.filter fun i => sequencePowerActivation Z (indices i) k
    (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
    ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ) +
      c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩)) p

noncomputable def sequenceActiveLocalIndex
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (k : ℤ) (p : PowerParams s₀ s₁) :
    Fin (sequenceActiveLocalCandidates Z c v children indices k p).card → Fin P :=
  fun j => ((sequenceActiveLocalCandidates Z c v children indices k p).equivFin.symm j).val

theorem sequenceActiveLocalIndex_injective
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (k : ℤ) (p : PowerParams s₀ s₁) :
    Function.Injective (sequenceActiveLocalIndex Z c v children indices k p) := by
  intro i j hij
  exact ((sequenceActiveLocalCandidates Z c v children indices k p).equivFin.symm).injective
    (Subtype.ext hij)

theorem sequenceActiveLocalIndex_active
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (k : ℤ) (p : PowerParams s₀ s₁)
    (j : Fin (sequenceActiveLocalCandidates Z c v children indices k p).card) :
    sequencePowerActivation Z (indices (sequenceActiveLocalIndex Z c v children indices k p j)) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, children (sequenceActiveLocalIndex Z c v children indices k p j)⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge
        ⟨v, children (sequenceActiveLocalIndex Z c v children indices k p j)⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge
          ⟨v, children (sequenceActiveLocalIndex Z c v children indices k p j)⟩)) p := by
  exact (Finset.mem_filter.1
    (((sequenceActiveLocalCandidates Z c v children indices k p).equivFin.symm j).property)).2

def sequenceLocalAllMiss
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (s₀ s₁ x : ℝ) (k : ℤ)
    (edges : Fin P → SelectorEdge M d) (indices : Fin P → ℕ)
    (p : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) : Prop :=
  ∀ i, sequencePowerActivation Z (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge (edges i)) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge (edges i))) p →
    ¬(ω.selectors (selectorAddress c (edges i)
          (sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p)) = true ∧
      ω.terminals (localTerminalAddress c hM hd ω.selectors (edges i)
          (sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p)) = true)

theorem sequenceLocalAllMiss_iff_active
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (s₀ s₁ x : ℝ) (k : ℤ)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (p : PowerParams s₀ s₁)
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    sequenceLocalAllMiss Z c hM hd s₀ s₁ x k (fun i => ⟨v, children i⟩) indices p ω ↔
      localRoutingAllMiss
        (localOwnAddresses c v
          (fun j => children (sequenceActiveLocalIndex Z c v children indices k p j))
          (fun j => sequencePoint Z
            (indices (sequenceActiveLocalIndex Z c v children indices k p j))
            ((2 : ℝ) ^ k) x p))
        (localTerminalAddresses c hM hd v
          (fun j => children (sequenceActiveLocalIndex Z c v children indices k p j))
          (fun j => sequencePoint Z
            (indices (sequenceActiveLocalIndex Z c v children indices k p j))
            ((2 : ℝ) ^ k) x p)) ω := by
  constructor
  · intro h j
    exact h _ (sequenceActiveLocalIndex_active Z c v children indices k p j)
  · intro h i hi
    have himem : i ∈ sequenceActiveLocalCandidates Z c v children indices k p :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    obtain ⟨j, hj⟩ :=
      ((sequenceActiveLocalCandidates Z c v children indices k p).equivFin.symm).surjective
        ⟨i, himem⟩
    have heq : sequenceActiveLocalIndex Z c v children indices k p j = i :=
      congrArg Subtype.val hj
    simpa only [localRoutingSuccess, localOwnAddresses, localTerminalAddresses, heq] using h j

theorem sequence_fixed_parameter_joint_miss
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (hU : 4 ≤ c.origin) (s₀ s₁ x : ℝ) (k : ℤ) (p : ℝ)
    (bits : SelectorEdge M d → Bool) (v : InternalNode M d)
    (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    (r : PowerParams s₀ s₁)
    (hindex : Function.Injective (fun i => (children i, indices i)))
    (hgap : ∀ i j, i ≠ j → children i = children j →
      3 ≤ r.1.1 * |Z.z (indices j) - Z.z (indices i)|) :
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
        (fun i => ⟨v, children i⟩) indices r ω) =
      tableProbability (T := TerminalAddress c hd) p
        (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
        (1 - p / 2) ^
          (sequenceActiveLocalCandidates Z c v children indices k r).card := by
  let ix := sequenceActiveLocalIndex Z c v children indices k r
  have hsep := sequence_local_address_separation Z c hM hd hL hU x bits v
    (fun j => children (ix j)) (fun j => indices (ix j)) k r
    (fun i j heq => by
      apply sequenceActiveLocalIndex_injective Z c v children indices k r
      apply hindex
      exact heq)
    (fun j => sequenceActiveLocalIndex_active Z c v children indices k r j)
    (fun i j hij hchild => by
      apply hgap (ix i) (ix j)
      · intro heq
        exact hij (sequenceActiveLocalIndex_injective Z c v children indices k r heq)
      · exact hchild)
  have hevent : (fun ω =>
      centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
        (fun i => ⟨v, children i⟩) indices r ω) =
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      localRoutingAllMiss
        (localOwnAddresses c v
          (fun j => children (ix j))
          (fun j => sequencePoint Z (indices (ix j)) ((2 : ℝ) ^ k) x r))
        (localTerminalAddresses c hM hd v
          (fun j => children (ix j))
          (fun j => sequencePoint Z (indices (ix j)) ((2 : ℝ) ^ k) x r)) ω) := by
    funext ω
    exact propext (and_congr_right fun _ => sequenceLocalAllMiss_iff_active
      Z c hM hd s₀ s₁ x k v children indices r ω)
  rw [hevent]
  exact joint_center_atom_all_miss p (actualCenterExposure c x bits) _ _ hsep

end ErdosSimilarityGrowingGaps
