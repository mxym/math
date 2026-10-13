import APPTReview.LacunaryColor
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open scoped BigOperators NNReal
open MeasureTheory Set
namespace APPTReview

/-- Exact interaction line for the same probability measure at every level. -/
def scaleLine (d : ℝ) : Set (ℝ≥0 × ℝ≥0) := {p | (p.1:ℝ)+(p.2:ℝ)=d}
def scaleOff (d : ℝ) : Set (ℝ≥0 × ℝ≥0) := {p | (p.1:ℝ)+(p.2:ℝ)=d ∧ p.1≠p.2}
noncomputable def scaleCenter (d : ℝ) : ℝ≥0 := Real.toNNReal (d/2)

theorem scaleCenter_coe (d : ℝ) (hd : 0 ≤ d) : (scaleCenter d:ℝ)=d/2 :=
  Real.coe_toNNReal _ (by positivity)

theorem measurableSet_scaleLine (d : ℝ) : MeasurableSet (scaleLine d) := by
  exact (isClosed_eq (by fun_prop) continuous_const).measurableSet

theorem measurableSet_scaleOff (d : ℝ) : MeasurableSet (scaleOff d) := by
  exact (measurableSet_scaleLine d).inter
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl

theorem scaleLine_split (d : ℝ) (hd : 0 ≤ d) :
    scaleLine d=scaleOff d ∪ ({scaleCenter d} ×ˢ {scaleCenter d}) := by
  ext p
  change ((p.1:ℝ)+(p.2:ℝ)=d) ↔
    (((p.1:ℝ)+(p.2:ℝ)=d ∧ p.1≠p.2) ∨ (p.1=scaleCenter d ∧ p.2=scaleCenter d))
  have hc := scaleCenter_coe d hd
  constructor
  · intro he
    by_cases hn : p.1=p.2
    · right
      have he1 : p.1=scaleCenter d := by
        apply NNReal.coe_injective
        have hh := congrArg (fun x : ℝ≥0 => (x:ℝ)) hn
        linarith
      exact ⟨he1,hn.symm.trans he1⟩
    · exact Or.inl ⟨he,hn⟩
  · rintro (he | ⟨h1,h2⟩)
    · exact he.1
    · rw [h1,h2,hc]; ring

theorem scaleLine_measure_split (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (d : ℝ) (hd : 0 ≤ d) :
    (μ.prod μ).real (scaleLine d)=
      (μ.prod μ).real (scaleOff d)+(μ.real {scaleCenter d})^2 := by
  rw [scaleLine_split d hd]
  have hdis : Disjoint (scaleOff d) ({scaleCenter d} ×ˢ {scaleCenter d}) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hp.2 (hq.1.trans hq.2.symm)
  rw [measureReal_union hdis ((measurableSet_singleton _).prod (measurableSet_singleton _)),
    measureReal_prod_prod,pow_two]

/-- Canonical bipartition bounds all off-diagonal lines simultaneously.
No finite-support or atom enumeration hypothesis is imposed on the measure. -/
theorem lacunary_off_mass (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (ds : List ℝ) (hgap : ds.Pairwise (fun d e => 2*e<d)) :
    (∑ d ∈ ds.toFinset, (μ.prod μ).real (scaleOff d)) ≤ 1/2 := by
  classical
  let c : ℝ≥0 → Bool := fun x => lacunaryColor ds (x:ℝ)
  let B : Set ℝ≥0 := {x | c x=true}
  have hc : Measurable c := (measurable_lacunaryColor ds).comp (by fun_prop)
  have hB : MeasurableSet B := hc (measurableSet_singleton true)
  have hd : (ds.toFinset : Set ℝ).PairwiseDisjoint scaleOff := by
    intro d _ e _ hne
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hne (hp.1.symm.trans hq.1)
  have hu := measureReal_biUnion_finset (μ:=μ.prod μ) hd
    (fun d _ => measurableSet_scaleOff d)
  have hsub : (⋃ d ∈ ds.toFinset, scaleOff d) ⊆ (B ×ˢ Bᶜ) ∪ (Bᶜ ×ˢ B) := by
    intro p hp
    rcases mem_iUnion.mp hp with ⟨d,hp⟩
    rcases mem_iUnion.mp hp with ⟨hd,hp⟩
    have hcol := lacunaryColor_separates ds hgap p.1.property p.2.property
      (fun he => hp.2 (NNReal.coe_injective he))
      (hp.1 ▸ (List.mem_toFinset.mp hd))
    change c p.1 ≠ c p.2 at hcol
    cases h1 : c p.1 <;> cases h2 : c p.2 <;> simp_all [B]
  have hbound := (measureReal_mono (μ:=μ.prod μ) hsub).trans
    (measureReal_union_le (μ:=μ.prod μ) (B ×ˢ Bᶜ) (Bᶜ ×ˢ B))
  rw [hu,measureReal_prod_prod,measureReal_prod_prod] at hbound
  have hsum := measureReal_add_measureReal_compl (μ:=μ) hB
  rw [probReal_univ] at hsum
  nlinarith [sq_nonneg (μ.real B-μ.real Bᶜ)]

/-- The exceptional loop masses have total at most one, even with infinitely
many atoms or a nonatomic component in the underlying probability measure. -/
theorem scale_center_mass (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (S : Finset ℝ) (hp : ∀ d∈S,0≤d) :
    (∑ d∈S, μ.real {scaleCenter d}) ≤ 1 := by
  classical
  have hd : (S : Set ℝ).PairwiseDisjoint (fun d => ({scaleCenter d}:Set ℝ≥0)) := by
    intro d hdm e hem hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    have he : scaleCenter d=scaleCenter e := hx.symm.trans hy
    have hh := congrArg (fun z : ℝ≥0 => (z:ℝ)) he
    rw [scaleCenter_coe d (hp d hdm),scaleCenter_coe e (hp e hem)] at hh
    exact hne (by linarith)
  have he := measureReal_biUnion_finset (μ:=μ) hd (fun _ _ => measurableSet_singleton _)
  rw [← he]
  exact (measureReal_mono (μ:=μ) (subset_univ _)).trans_eq probReal_univ

end APPTReview
