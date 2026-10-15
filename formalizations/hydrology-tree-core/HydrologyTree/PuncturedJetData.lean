import HydrologyTree.AllNodeStepExperiments
import HydrologyTree.RealLocatedPositivity

/-! One redundant third derivative can be omitted at ANY original vertex.
The remaining N second derivatives and N-1 third derivatives retain the full
all-node classification, for every strictly positive reference tree model. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The discarded node need not coincide with the inlet used in another
experiment or with either the reference or the candidate leakage site. -/
def SamePuncturedDiagonalJets (v0 : V) (A B : Matrix V V ℝ) : Prop :=
  (∀ v,A v v=B v v) ∧ ∀ v,v ≠ v0 → (A*A) v v=(B*B) v v

/-- For tree-supported actual graph matrices, the single omitted second
matrix moment is algebraically determined, without ANY rate sign assumptions. -/
theorem graph_punctured_jets_complete {n : ℕ} {v0 : V}
    (p : RootedTreePresentation n G v0) (a b : V) (x y : GraphRates G)
    (h : SamePuncturedDiagonalJets v0 (graphCompartmentMatrix G a x) (graphCompartmentMatrix G b y)) :
    diagonalTwoJet (graphCompartmentMatrix G a x)=diagonalTwoJet (graphCompartmentMatrix G b y) := by
  let A := graphCompartmentMatrix G a x
  let B := graphCompartmentMatrix G b y
  let M := A.submatrix p.vertices p.vertices
  let N := B.submatrix p.vertices p.vertices
  have hprod : ∀ i j,M i j*M j i=N i j*N j i := by
    apply tree_punctured_moments_determine_products p.tree M N
      (graphCompartment_tree_support p a x) (graphCompartment_tree_support p b y)
    · exact fun i => h.1 (p.vertices i)
    · intro e
      rw [matrix_square_submatrix_equiv,matrix_square_submatrix_equiv]
      apply h.2
      intro he
      have hh : p.vertices e.succ=p.vertices 0 := he.trans p.root_eq.symm
      exact Fin.succ_ne_zero e (p.vertices.injective hh)
  have hsquare (i : Fin (n+1)) : (M*M) i i=(N*N) i i := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun j _ => hprod i j)
  refine Prod.ext (funext h.1) ?_
  funext v
  obtain ⟨i,rfl⟩ := p.vertices.surjective v
  exact (matrix_square_submatrix_equiv A p.vertices i i).symm.trans
    ((hsquare i).trans (matrix_square_submatrix_equiv B p.vertices i i))

abbrev PuncturedJetFiber (v0 o : V) (x : GraphRates G) :=
  Σ ell : V,{y : GraphRates G // SamePuncturedDiagonalJets v0
    (graphCompartmentMatrix G ell y) (graphCompartmentMatrix G o x)}

def puncturedJetFiberEquivFull {n : ℕ} {v0 : V}
    (p : RootedTreePresentation n G v0) (o : V) (x : GraphRates G) :
    PuncturedJetFiber v0 o x ≃ AllNodeJetFiber o x where
  toFun z := ⟨z.1,⟨z.2.val,graph_punctured_jets_complete p z.1 o z.2.val x z.2.property⟩⟩
  invFun z := ⟨z.1,⟨z.2.val,
    (fun v => congrArg (fun q : (V → ℝ) × (V → ℝ) => q.1 v) z.2.property),
    (fun v _ => congrArg (fun q : (V → ℝ) × (V → ℝ) => q.2 v) z.2.property)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly N distinct real models remain from only 2N-1 scalar low-order
coefficients, with the omitted high-order coefficient chosen arbitrarily. -/
theorem punctured_jet_fiber_exact_card {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (v0 : V) (x : PositiveGraphRateSpace G) :
    Nonempty (PuncturedJetFiber v0 o x.val ≃ V) ∧
      Finite (PuncturedJetFiber v0 o x.val) ∧
      Nat.card (PuncturedJetFiber v0 o x.val)=Fintype.card V := by
  let q := leakRootPresentation hG p v0
  let E := (puncturedJetFiberEquivFull q o x.val).trans (allNodeJetFiberEquivSites hG p x)
  exact ⟨⟨E⟩,Finite.of_injective E E.injective,(Nat.card_congr E).trans Nat.card_eq_fintype_card⟩

/-- The omitted coefficient is also redundant for actual scalar derivatives,
not only for hypothetical direct observations of entries of A and A^2. -/
theorem actual_punctured_step_jets_suffice {n : ℕ} (hG : G.IsTree) {o : V}
    (p : RootedTreePresentation n G o) (v0 ell : V) (x : PositiveGraphRateSpace G)
    (y : GraphRates G)
    (h : ∀ v : V,∃ z q : ℝ → V → ℝ,
      IsLocatedGraphSolution v o x.val (fun _ => 1) z ∧ z 0=0 ∧
      IsLocatedGraphSolution v ell y (fun _ => 1) q ∧ q 0=0 ∧
      iteratedDeriv 2 (fun s => z s v) 0=iteratedDeriv 2 (fun s => q s v) 0 ∧
      (v ≠ v0 → iteratedDeriv 3 (fun s => z s v) 0=iteratedDeriv 3 (fun s => q s v) 0)) :
    SameAllNodeStepJets o ell x.val y := by
  apply (all_node_step_jets_iff_moments hG p ell x y).mpr
  apply graph_punctured_jets_complete (leakRootPresentation hG p v0) ell o y x.val
  constructor
  · intro v
    obtain ⟨z,q,hz,hz0,hq,hq0,h2,_⟩ := h v
    have hp := congrArg Prod.fst (constant_input_collocated_jet v hz hz0)
    have hr := congrArg Prod.fst (constant_input_collocated_jet v hq hq0)
    exact hr.symm.trans (h2.symm.trans hp)
  · intro v hv
    obtain ⟨z,q,hz,hz0,hq,hq0,_,h3⟩ := h v
    have hp := congrArg Prod.snd (constant_input_collocated_jet v hz hz0)
    have hr := congrArg Prod.snd (constant_input_collocated_jet v hq hq0)
    exact hr.symm.trans ((h3 hv).symm.trans hp)

end HydrologyTree
