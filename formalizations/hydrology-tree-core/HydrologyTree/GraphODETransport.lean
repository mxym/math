import HydrologyTree.GraphMatrixTransport
import HydrologyTree.PhysicalForcedODE

/-! Bijection of actual classical graph ODE trajectories and parent-model
trajectories. Neither the state equation nor the root input is replaced by
an assumed coefficient or transfer-function identity. -/
open Matrix
noncomputable section
namespace HydrologyTree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev IsGraphForcedSolution (o : V) (y : GraphRates G) (u : ℝ → ℝ) (z : ℝ → V → ℝ) : Prop :=
  IsForcedMatrixSolution (graphCompartmentMatrix G o y) (Pi.single o 1) u z

def graphStateEquiv {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    (V → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) := vectorReindex p.vertices

def graphTrajectoryEquiv {n : ℕ} {o : V} (p : RootedTreePresentation n G o) :
    (ℝ → V → ℝ) ≃ (ℝ → Fin (n+1) → ℝ) where
  toFun z s := graphStateEquiv p (z s)
  invFun q s := (graphStateEquiv p).symm (q s)
  left_inv z := by funext s; exact (graphStateEquiv p).symm_apply_apply (z s)
  right_inv q := by funext s; exact (graphStateEquiv p).apply_symm_apply (q s)

@[simp] lemma graphTrajectoryEquiv_apply {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (z : ℝ → V → ℝ) (s : ℝ) (i : Fin (n+1)) :
    graphTrajectoryEquiv p z s i=z s (p.vertices i) := rfl

@[simp] lemma graphTrajectoryEquiv_symm_apply {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (q : ℝ → Fin (n+1) → ℝ) (s : ℝ) (v : V) :
    (graphTrajectoryEquiv p).symm q s v=q s (p.vertices.symm v) := rfl

lemma graph_mulVec_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (v : V → ℝ) (i : Fin (n+1)) :
    (graphCompartmentMatrix G o (graphRateEquiv p x)*ᵥv) (p.vertices i)=
      (compartmentMatrix p.tree x*ᵥgraphStateEquiv p v) i := by
  simp only [Matrix.mulVec,dotProduct]
  rw [← p.vertices.sum_comp (fun j => graphCompartmentMatrix G o (graphRateEquiv p x) (p.vertices i) j*v j)]
  apply Finset.sum_congr rfl
  intro j _
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M i j)
    (graphCompartmentMatrix_transport p x)
  exact congrArg (fun a : ℝ => a*v (p.vertices j)) h

lemma graph_field_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (a : ℝ) (v : V → ℝ) (i : Fin (n+1)) :
    (graphCompartmentMatrix G o (graphRateEquiv p x)*ᵥv+a • (Pi.single o 1 : V → ℝ)) (p.vertices i)=
      (compartmentMatrix p.tree x*ᵥgraphStateEquiv p v+a • (Pi.single 0 1 : Fin (n+1) → ℝ)) i := by
  simp only [Pi.add_apply,Pi.smul_apply,graph_mulVec_transport]
  congr 1
  simp [Pi.single_apply,← p.root_eq]

/-- Exact equivalence for every forcing, including noncontinuous forcing
whenever the actual classical trajectory exists. -/
theorem graph_forced_solution_transport {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (u : ℝ → ℝ) (z : ℝ → V → ℝ) :
    IsGraphForcedSolution o (graphRateEquiv p x) u z ↔
      IsPhysicalForcedSolution p.tree x u (graphTrajectoryEquiv p z) := by
  constructor
  · intro hz s
    apply hasDerivAt_pi.mpr
    intro i
    have h := (hasDerivAt_pi.mp (hz s)) (p.vertices i)
    apply h.congr_deriv
    exact graph_field_transport p x (u s) (z s) i
  · intro hz s
    apply hasDerivAt_pi.mpr
    intro v
    obtain ⟨i,rfl⟩ := p.vertices.surjective v
    have h := (hasDerivAt_pi.mp (hz s)) i
    apply h.congr_deriv
    exact (graph_field_transport p x (u s) (z s) i).symm

lemma graph_trajectory_endpoint_iff {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (z : ℝ → V → ℝ) (a : ℝ) (v : V → ℝ) :
    graphTrajectoryEquiv p z a=graphStateEquiv p v ↔ z a=v :=
  (graphStateEquiv p).injective.eq_iff

lemma graph_trajectory_zero_iff {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (z : ℝ → V → ℝ) (a : ℝ) : graphTrajectoryEquiv p z a=0 ↔ z a=0 := by
  have h := graph_trajectory_endpoint_iff p z a 0
  simpa only [map_zero] using h

@[simp] lemma graphTrajectoryEquiv_root {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (z : ℝ → V → ℝ) (s : ℝ) : graphTrajectoryEquiv p z s 0=z s o := by
  rw [graphTrajectoryEquiv_apply,p.root_eq]

/-- Well-posedness of the independently defined actual graph system. -/
theorem graph_forced_ODE_existsUnique {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (y : GraphRates G) (hy : PositiveGraphRates y) (u : ℝ → ℝ) (hu : Continuous u)
    (a : ℝ) (z0 : V → ℝ) :
    ∃! z : ℝ → V → ℝ, IsGraphForcedSolution o y u z ∧ z a=z0 := by
  obtain ⟨x,rfl⟩ := (graphRateEquiv p).surjective y
  have hx := (graphRateEquiv_positive_iff p x).mp hy
  obtain ⟨q,hq,huniq⟩ := physical_forced_ODE_existsUnique p.tree x hx u hu a (graphStateEquiv p z0)
  let z := (graphTrajectoryEquiv p).symm q
  have hODE : IsGraphForcedSolution o (graphRateEquiv p x) u z := by
    apply (graph_forced_solution_transport p x u z).mpr
    simpa only [z,Equiv.apply_symm_apply] using hq.1
  have h0 : z a=z0 := by
    apply (graph_trajectory_endpoint_iff p z a z0).mp
    simpa only [z,Equiv.apply_symm_apply] using hq.2
  refine ⟨z,⟨hODE,h0⟩,?_⟩
  intro v hv
  apply (graphTrajectoryEquiv p).injective
  change graphTrajectoryEquiv p v=graphTrajectoryEquiv p ((graphTrajectoryEquiv p).symm q)
  rw [Equiv.apply_symm_apply]
  apply huniq
  exact ⟨(graph_forced_solution_transport p x u v).mp hv.1,
    (graph_trajectory_endpoint_iff p v a z0).mpr hv.2⟩


@[simp] lemma graphTrajectoryEquiv_symm_root {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (q : ℝ → Fin (n+1) → ℝ) (s : ℝ) : (graphTrajectoryEquiv p).symm q s o=q s 0 := by
  have h : p.vertices.symm o=0 := by
    simpa only [p.root_eq] using p.vertices.symm_apply_apply 0
  rw [graphTrajectoryEquiv_symm_apply,h]

lemma graph_two_endpoint_predicate_iff {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (u : ℝ → ℝ) (T : ℝ) (z0 z1 : V → ℝ) (z : ℝ → V → ℝ) :
    (IsGraphForcedSolution o (graphRateEquiv p x) u z ∧ z 0=z0 ∧ z T=z1) ↔
      (IsPhysicalForcedSolution p.tree x u (graphTrajectoryEquiv p z) ∧
        graphTrajectoryEquiv p z 0=graphStateEquiv p z0 ∧
        graphTrajectoryEquiv p z T=graphStateEquiv p z1) := by
  rw [graph_forced_solution_transport,graph_trajectory_endpoint_iff,graph_trajectory_endpoint_iff]

/-- Endpoint-feasible actual solution sets are transported bijectively, including
uniqueness rather than only existence of one chosen trajectory. -/
theorem graph_two_endpoint_existsUnique_iff {n : ℕ} {o : V} (p : RootedTreePresentation n G o)
    (x : TreeRates n) (u : ℝ → ℝ) (T : ℝ) (z0 z1 : V → ℝ) :
    (∃! z : ℝ → V → ℝ, IsGraphForcedSolution o (graphRateEquiv p x) u z ∧ z 0=z0 ∧ z T=z1) ↔
      (∃! q : ℝ → Fin (n+1) → ℝ, IsPhysicalForcedSolution p.tree x u q ∧
        q 0=graphStateEquiv p z0 ∧ q T=graphStateEquiv p z1) := by
  constructor
  · rintro ⟨z,hz,hu⟩
    refine ⟨graphTrajectoryEquiv p z,(graph_two_endpoint_predicate_iff p x u T z0 z1 z).mp hz,?_⟩
    intro q hq
    have hq' : IsGraphForcedSolution o (graphRateEquiv p x) u ((graphTrajectoryEquiv p).symm q) ∧
        (graphTrajectoryEquiv p).symm q 0=z0 ∧ (graphTrajectoryEquiv p).symm q T=z1 := by
      apply (graph_two_endpoint_predicate_iff p x u T z0 z1 _).mpr
      simpa only [Equiv.apply_symm_apply] using hq
    have h := congrArg (graphTrajectoryEquiv p) (hu _ hq')
    simpa only [Equiv.apply_symm_apply] using h
  · rintro ⟨q,hq,hu⟩
    refine ⟨(graphTrajectoryEquiv p).symm q,?_,?_⟩
    · apply (graph_two_endpoint_predicate_iff p x u T z0 z1 _).mpr
      simpa only [Equiv.apply_symm_apply] using hq
    · intro z hz
      apply (graphTrajectoryEquiv p).injective
      rw [Equiv.apply_symm_apply]
      exact hu _ ((graph_two_endpoint_predicate_iff p x u T z0 z1 z).mp hz)

end HydrologyTree
