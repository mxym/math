import HydrologyTree.GraphMassBalance
import HydrologyTree.LeakRelocationRates

/-! Different positive leak locations really give different physical matrices.
This excludes an artificial increase in the model count by redundant labels. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma graphTransfer_offdiag_dart (y : GraphRates G) (e d : G.Dart) :
    graphTransfer y e d.snd d.fst=if e=d then y.2 d else 0 := by
  have hd : ¬(e.fst=d.snd ∧ e.fst=d.fst) := by
    rintro ⟨h1,h2⟩
    exact d.snd_ne_fst (h1.symm.trans h2)
  have he : (e.snd=d.snd ∧ e.fst=d.fst) ↔ e=d := by
    constructor
    · rintro ⟨h1,h2⟩
      exact SimpleGraph.Dart.ext _ _ (Prod.ext h2 h1)
    · rintro rfl
      exact ⟨rfl,rfl⟩
  simp only [graphTransfer,Matrix.smul_apply,Matrix.sub_apply,Matrix.single_apply,hd,he,
    if_false,sub_zero,smul_eq_mul]
  by_cases h : e=d <;> simp [h]

/-- Every directed graph rate is an actual off-diagonal entry, independently of
the leak site and without assuming positivity or tree structure. -/
theorem graphCompartment_dart_entry (o : V) (y : GraphRates G) (d : G.Dart) :
    graphCompartmentMatrix G o y d.snd d.fst=y.2 d := by
  have hd : ¬(o=d.snd ∧ o=d.fst) := by
    rintro ⟨h1,h2⟩
    exact d.snd_ne_fst (h1.symm.trans h2)
  simp only [graphCompartmentMatrix,Matrix.sub_apply,Matrix.sum_apply,
    graphTransfer_offdiag_dart,Matrix.smul_apply,Matrix.single_apply,hd,if_false,smul_eq_mul,mul_zero,sub_zero]
  simp

/-- With a fixed leak site, the full physical matrix uniquely determines every
real rate and the leak coefficient. No response-identifiability claim is used. -/
theorem graphRates_from_matrix_injective (o : V) :
    Function.Injective (graphCompartmentMatrix G o) := by
  intro x y h
  apply Prod.ext
  · have hs := congrArg (fun A : Matrix V V ℝ => ∑ v, A v o) h
    simpa only [graphCompartment_column_sum,ite_true,neg_inj] using hs
  · funext d
    have hs := congrArg (fun A : Matrix V V ℝ => A d.snd d.fst) h
    simpa only [graphCompartment_dart_entry] using hs

/-- A nonzero physical leak is located uniquely by the actual matrix's column
sums. Therefore two different positive leakage sites cannot be the same matrix. -/
theorem equal_graph_matrices_identify_leak_site (o ell : V) (x y : GraphRates G)
    (hx : x.1 ≠ 0) (h : graphCompartmentMatrix G o x=graphCompartmentMatrix G ell y) : o=ell := by
  by_contra ho
  have hs := congrArg (fun A : Matrix V V ℝ => ∑ v, A v o) h
  simp only [graphCompartment_column_sum,ite_true,if_neg ho,neg_eq_zero] at hs
  exact hx hs

/-- Full physical parameterization, including the positive leak location, has
no redundant representatives. The unknown-site count is a count of distinct
matrices, not multiple names for the same physical model. -/
def positiveGraphModelMatrix (z : Σ ell : V, PositiveGraphRateSpace G) : Matrix V V ℝ :=
  graphCompartmentMatrix G z.1 z.2.val

theorem positiveGraphModelMatrix_injective : Function.Injective (positiveGraphModelMatrix (G := G)) := by
  rintro ⟨o,x⟩ ⟨ell,y⟩ h
  have he : o=ell := equal_graph_matrices_identify_leak_site o ell x.val y.val
    (ne_of_gt x.property.1) h
  subst ell
  have hy : x=y := Subtype.ext (graphRates_from_matrix_injective o h)
  subst y
  rfl

end HydrologyTree
