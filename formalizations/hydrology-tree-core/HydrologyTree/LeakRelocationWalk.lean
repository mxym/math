import HydrologyTree.LeakGauge

/-! Exact invertible leak relocation along actual graph walks. On a finite tree
all steps have proved cuts, so the actual diagonal response is preserved at ANY
fixed observation vertex while the leak is moved to ANY other vertex. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Compose the explicitly invertible edge transformations along the chosen walk. -/
def leakWalkEquiv : {u v : V} → G.Walk u v → PositiveGraphRateSpace G ≃ PositiveGraphRateSpace G
  | _,_, .nil => Equiv.refl _
  | _,_, .cons h p => (slidePositiveLeakEquiv ⟨(_, _),h⟩).trans (leakWalkEquiv p)

/-- Composition preserves the ACTUAL matrix up to positive diagonal similarity.
The observation point is not moved or relabelled. -/
theorem leakWalk_similarity (hG : G.IsTree) {u v : V} (p : G.Walk u v)
    (y : PositiveGraphRateSpace G) :
    ∃ h : V → ℝ, (∀ i, 0<h i) ∧
      graphCompartmentMatrix G v (leakWalkEquiv p y).val=
        diagonalGauge h (graphCompartmentMatrix G u y.val) := by
  induction p generalizing y with
  | nil =>
    refine ⟨fun _ => 1,fun _ => by norm_num,?_⟩
    simp [leakWalkEquiv,diagonalGauge]
  | @cons a b c hab p ih =>
    let d : G.Dart := ⟨(a,b),hab⟩
    obtain ⟨h,hh,hM⟩ := finite_tree_leak_slide hG d y.val y.property
    obtain ⟨k,hk,hN⟩ := ih (slidePositiveLeakEquiv d y)
    refine ⟨fun i => k i*h i,fun i => mul_pos (hk i) (hh i),?_⟩
    change graphCompartmentMatrix G c (leakWalkEquiv p (slidePositiveLeakEquiv d y)).val=_
    rw [hN]
    change diagonalGauge k (graphCompartmentMatrix G b (slideLeakRates d y.val))=_
    rw [hM,diagonalGauge_comp]

def relocatePositiveLeak (hG : G.IsTree) (u v : V) :
    PositiveGraphRateSpace G ≃ PositiveGraphRateSpace G :=
  leakWalkEquiv (Classical.choice (hG.connected u v))

/-- A constructive equivalence between the entire positive rate spaces at any
two leak sites, with a proved actual matrix similarity for every parameter vector. -/
theorem relocatePositiveLeak_similarity (hG : G.IsTree) (u v : V)
    (y : PositiveGraphRateSpace G) :
    ∃ h : V → ℝ, (∀ i, 0<h i) ∧
      graphCompartmentMatrix G v (relocatePositiveLeak hG u v y).val=
        diagonalGauge h (graphCompartmentMatrix G u y.val) :=
  leakWalk_similarity hG _ y

/-- All characteristic polynomials and ALL collocated observation responses
remain unchanged. Poles are included only under the algebraic total-inverse
convention; physical uses restrict to the actual nonpole domain. -/
theorem relocatePositiveLeak_response (hG : G.IsTree) (u v : V)
    (y : PositiveGraphRateSpace G) :
    (graphCompartmentMatrix G v (relocatePositiveLeak hG u v y).val).charpoly=
        (graphCompartmentMatrix G u y.val).charpoly ∧
      ∀ o : V, diagonalCofactor (graphCompartmentMatrix G v (relocatePositiveLeak hG u v y).val) o=
        diagonalCofactor (graphCompartmentMatrix G u y.val) o ∧
      ∀ s : ℝ, (Matrix.scalar V s-graphCompartmentMatrix G v (relocatePositiveLeak hG u v y).val)⁻¹ o o=
        (Matrix.scalar V s-graphCompartmentMatrix G u y.val)⁻¹ o o := by
  obtain ⟨h,hh,hM⟩ := relocatePositiveLeak_similarity hG u v y
  have hn : ∀ i, h i ≠ 0 := fun i => ne_of_gt (hh i)
  rw [hM]
  exact ⟨diagonalGauge_charpoly h hn _,fun o => ⟨diagonalGauge_cofactor h hn _ o,
    fun s => diagonalGauge_resolvent h hn _ o s⟩⟩

end HydrologyTree
