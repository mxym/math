import APPTReview.SchmidtJointScalar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open scoped BigOperators
namespace APPTReview

/-- A descending scale list with a strict factor-two gap. -/
def LacunaryScales (ds : List ℝ) : Prop :=
  (∀ d ∈ ds, 0 < d) ∧ ds.Pairwise (fun d e => 2*e < d)

/-- Reflect the high endpoint across the largest scale and reverse its color.
This is a total function on the reals; only nonnegative endpoints enter the theorem. -/
noncomputable def lacunaryColor : List ℝ → ℝ → Bool
  | [] => fun _ => false
  | d::ds => fun x => if d/2 < x then !(lacunaryColor ds (d-x)) else lacunaryColor ds x

/-- Every off-diagonal exact scale interaction crosses one canonical bipartition.
The coloring is constructed, rather than supplied as a graph hypothesis. -/
theorem lacunaryColor_separates (ds : List ℝ)
    (hgap : ds.Pairwise (fun d e => 2*e < d))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hne : x ≠ y) (hmem : x+y ∈ ds) :
    lacunaryColor ds x ≠ lacunaryColor ds y := by
  induction ds with
  | nil => simp at hmem
  | cons d ds ih =>
    rcases List.pairwise_cons.mp hgap with ⟨hd,hds⟩
    rcases List.mem_cons.mp hmem with he | ht
    · have he' : x+y=d := he
      by_cases hh : d/2 < x
      · have hl : ¬ d/2 < y := by linarith
        have hsub : d-x=y := by linarith
        simp only [lacunaryColor,ite_eq_left hh,ite_eq_right hl,hsub]
        cases lacunaryColor ds y <;> decide
      · have hh' : d/2 < y := by
          by_contra hb
          have heq : x=y := by linarith
          exact hne heq
        have hsub : d-y=x := by linarith
        simp only [lacunaryColor,ite_eq_right hh,ite_eq_left hh',hsub]
        cases lacunaryColor ds x <;> decide
    · have hsmall := hd (x+y) ht
      have hnx : ¬ d/2 < x := by linarith
      have hny : ¬ d/2 < y := by linarith
      simpa only [lacunaryColor,ite_eq_right hnx,ite_eq_right hny] using ih hds ht

/-- All scales are genuinely distinct; zero/negative scales are not hidden in the encoding. -/
theorem LacunaryScales.nodup {ds : List ℝ} (h : LacunaryScales ds) : ds.Nodup := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rcases h with ⟨hp,hg⟩
    rcases List.pairwise_cons.mp hg with ⟨hd,hds⟩
    apply List.nodup_cons.mpr
    constructor
    · intro hm
      have hlt := hd d hm
      have hpos := hp d (by simp)
      linarith
    · exact ih ⟨fun e he => hp e (by simp [he]),hds⟩

/-- The partition is Borel measurable, so the same coloring can be applied to
arbitrary probability measures, not just finite atomic approximations. -/
theorem measurable_lacunaryColor (ds : List ℝ) : Measurable (lacunaryColor ds) := by
  induction ds with
  | nil => exact measurable_const
  | cons d ds ih =>
    change Measurable (fun x : ℝ => if d/2 < x then !(lacunaryColor ds (d-x)) else lacunaryColor ds x)
    apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
    · exact (measurable_of_finite Bool.not).comp (ih.comp (measurable_const.sub measurable_id))
    · exact ih

end APPTReview
