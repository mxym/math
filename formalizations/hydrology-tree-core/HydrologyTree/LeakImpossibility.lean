import HydrologyTree.LeakLocationIdentifiability
import HydrologyTree.GraphModelInjectivity

/-! Rigorous leakage-localization impossibility within the exact specified
observation class. Alternatives are distinct physical matrices, not relabellings
or duplicate encodings, and actual solutions exist for every continuous input. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For every positive tree model and any different candidate leak site there
is a DISTINCT positive physical matrix producing all the same collocated
input/state histories. The single alternative works for every observer and input. -/
theorem distinct_leak_models_all_collocated_outputs (hG : G.IsTree) (ell ell' : V)
    (hne : ell ≠ ell') (y : PositiveGraphRateSpace G) :
    ∃ y' : PositiveGraphRateSpace G,
      graphCompartmentMatrix G ell y.val ≠ graphCompartmentMatrix G ell' y'.val ∧
      (∀ (o : V) (s : ℝ), (Matrix.scalar V s-graphCompartmentMatrix G ell y.val)⁻¹ o o=
        (Matrix.scalar V s-graphCompartmentMatrix G ell' y'.val)⁻¹ o o) ∧
      ∀ (o : V) (u : ℝ → ℝ), Continuous u →
        ∃ z q : ℝ → V → ℝ,
          IsLocatedGraphSolution o ell y.val u z ∧ z 0=0 ∧
          IsLocatedGraphSolution o ell' y'.val u q ∧ q 0=0 ∧
          (∀ s : ℝ, z s o=q s o) ∧
          (∀ z', IsLocatedGraphSolution o ell y.val u z' → z' 0=0 → z'=z) ∧
          (∀ q', IsLocatedGraphSolution o ell' y'.val u q' → q' 0=0 → q'=q) := by
  let y' := relocatePositiveLeak hG ell ell' y
  refine ⟨y',?_,?_,?_⟩
  · intro he
    exact hne (equal_graph_matrices_identify_leak_site ell ell' y.val y'.val (ne_of_gt y.property.1) he)
  · intro o s
    exact ((relocatePositiveLeak_response hG ell ell' y).2 o).2 s |>.symm
  · exact leak_location_all_input_indistinguishability hG ell ell' y

/-- Underlying matrix of an actual unknown-leak trajectory-fiber member. -/
def unknownLeakContinuousMatrix {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ)
    (z : UnknownLeakContinuousFiber (G := G) o r w) : Matrix V V ℝ :=
  graphCompartmentMatrix G z.1 z.2.val.val

theorem unknownLeakContinuousMatrix_injective {n : ℕ} (o : V) (r w : Fin (n+1) → ℝ) :
    Function.Injective (unknownLeakContinuousMatrix (G := G) o r w) := by
  rintro ⟨ell,x⟩ ⟨ell',y⟩ h
  have he : ell=ell' := equal_graph_matrices_identify_leak_site ell ell' x.val.val y.val.val
    (ne_of_gt x.val.property.1) h
  subst ell'
  have hy : x=y := Subtype.ext (Subtype.ext (graphRates_from_matrix_injective ell h))
  subst y
  rfl

end HydrologyTree
