import HydrologyTree.GraphPresentation
import HydrologyTree.PositiveRateAssembly
import Mathlib.Combinatorics.SimpleGraph.Dart

/-! Exact linear rate-coordinate equivalence with every actual oriented graph
edge. No sign or nonzero-rate hypothesis restricts this transport. -/
noncomputable section
namespace HydrologyTree

abbrev GraphRates {V : Type*} (G : SimpleGraph V) := ℝ × (G.Dart → ℝ)

variable {V : Type*} {n : ℕ} {G : SimpleGraph V} {o : V}

def treeDartOfPresentation (p : RootedTreePresentation n G o) : Fin n ⊕ Fin n → G.Dart
  | .inl i => ⟨(p.vertices i.succ,p.vertices (p.tree.parent i)),
      (p.adj_iff _ _).mp ⟨i,Or.inr ⟨rfl,rfl⟩⟩⟩
  | .inr i => ⟨(p.vertices (p.tree.parent i),p.vertices i.succ),
      (p.adj_iff _ _).mp ⟨i,Or.inl ⟨rfl,rfl⟩⟩⟩

lemma treeDartOfPresentation_injective (p : RootedTreePresentation n G o) :
    Function.Injective (treeDartOfPresentation p) := by
  intro a b h
  have hf := congrArg (fun d : G.Dart => d.fst) h
  have hs := congrArg (fun d : G.Dart => d.snd) h
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      dsimp only [treeDartOfPresentation] at hf hs
      exact congrArg Sum.inl (Fin.succ_injective _ (p.vertices.injective hf))
    | inr j =>
      dsimp only [treeDartOfPresentation] at hf hs
      exact False.elim (no_reversed_tree_edges p.tree i j
        ⟨(p.vertices.injective hs).symm,(p.vertices.injective hf).symm⟩)
  | inr i =>
    cases b with
    | inl j =>
      dsimp only [treeDartOfPresentation] at hf hs
      exact False.elim (no_reversed_tree_edges p.tree i j
        ⟨(p.vertices.injective hf).symm,(p.vertices.injective hs).symm⟩)
    | inr j =>
      dsimp only [treeDartOfPresentation] at hf hs
      exact congrArg Sum.inr (Fin.succ_injective _ (p.vertices.injective hs))

lemma treeDartOfPresentation_surjective (p : RootedTreePresentation n G o) :
    Function.Surjective (treeDartOfPresentation p) := by
  intro d
  have ha : (orderedTreeGraph p.tree).Adj (p.vertices.symm d.fst) (p.vertices.symm d.snd) :=
    (p.adj_iff _ _).mpr (by simpa only [Equiv.apply_symm_apply] using d.adj)
  obtain ⟨i,⟨h1,h2⟩ | ⟨h1,h2⟩⟩ := ha
  · refine ⟨.inr i,?_⟩
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · simpa only [treeDartOfPresentation,Equiv.apply_symm_apply] using (congrArg p.vertices h1).symm
    · simpa only [treeDartOfPresentation,Equiv.apply_symm_apply] using (congrArg p.vertices h2).symm
  · refine ⟨.inl i,?_⟩
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · simpa only [treeDartOfPresentation,Equiv.apply_symm_apply] using (congrArg p.vertices h2).symm
    · simpa only [treeDartOfPresentation,Equiv.apply_symm_apply] using (congrArg p.vertices h1).symm

def treeDartEquiv (p : RootedTreePresentation n G o) : (Fin n ⊕ Fin n) ≃ G.Dart :=
  Equiv.ofBijective (treeDartOfPresentation p)
    ⟨treeDartOfPresentation_injective p,treeDartOfPresentation_surjective p⟩

def graphRateEquiv (p : RootedTreePresentation n G o) : TreeRates n ≃ₗ[ℝ] GraphRates G where
  toFun x := (x.1 0,fun d => Sum.elim (fun i => x.1 i.succ) x.2 ((treeDartEquiv p).symm d))
  invFun y := (Fin.cons y.1 (fun i => y.2 (treeDartEquiv p (.inl i))),
    fun i => y.2 (treeDartEquiv p (.inr i)))
  left_inv x := by
    apply Prod.ext
    · funext v
      refine Fin.cases ?_ (fun i => ?_) v <;> simp
    · funext i
      simp
  right_inv y := by
    apply Prod.ext
    · rfl
    · funext d
      obtain ⟨i,rfl⟩ := (treeDartEquiv p).surjective d
      cases i <;> simp
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext d
      cases h : (treeDartEquiv p).symm d <;> simp [h]
  map_smul' c x := by
    apply Prod.ext
    · rfl
    · funext d
      cases h : (treeDartEquiv p).symm d <;> simp [h]

@[simp] lemma graphRateEquiv_leak (p : RootedTreePresentation n G o) (x : TreeRates n) :
    (graphRateEquiv p x).1=x.1 0 := rfl

@[simp] lemma graphRateEquiv_inward (p : RootedTreePresentation n G o) (x : TreeRates n) (i : Fin n) :
    (graphRateEquiv p x).2 (treeDartEquiv p (.inl i))=x.1 i.succ := by simp [graphRateEquiv]

@[simp] lemma graphRateEquiv_outward (p : RootedTreePresentation n G o) (x : TreeRates n) (i : Fin n) :
    (graphRateEquiv p x).2 (treeDartEquiv p (.inr i))=x.2 i := by simp [graphRateEquiv]

def PositiveGraphRates (y : GraphRates G) : Prop := 0 < y.1 ∧ ∀ d, 0 < y.2 d

theorem graphRateEquiv_positive_iff (p : RootedTreePresentation n G o) (x : TreeRates n) :
    PositiveGraphRates (graphRateEquiv p x) ↔ PositiveRateVector x := by
  constructor
  · rintro ⟨h0,hd⟩
    constructor
    · intro v
      refine Fin.cases h0 (fun i => ?_) v
      simpa only [graphRateEquiv_inward] using hd (treeDartEquiv p (.inl i))
    · intro i
      simpa only [graphRateEquiv_outward] using hd (treeDartEquiv p (.inr i))
  · rintro ⟨ha,hf⟩
    refine ⟨ha 0,?_⟩
    intro d
    obtain ⟨i,rfl⟩ := (treeDartEquiv p).surjective d
    cases i with
    | inl i => simpa only [graphRateEquiv_inward] using ha i.succ
    | inr i => simpa only [graphRateEquiv_outward] using hf i

end HydrologyTree
