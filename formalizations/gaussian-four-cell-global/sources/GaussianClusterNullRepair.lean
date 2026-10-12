import GaussianIndicatorPartitionLimit

/-! A finite measurable indicator partition holding almost everywhere can
be repaired to literally disjoint measurable cells without changing any
Gaussian mass or BV perimeter. No choice of a geometric minimizer is made. -/
open MeasureTheory ProbabilityTheory Module Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ}

lemma indicator_sum_one_unique (S : Fin k → Set (Space d)) (x : Space d)
    (hsum : (∑ i,(S i).indicator (fun _ => (1 : ℝ)) x)=1) :
    ∃ r,x ∈ S r ∧ ∀ j,j ≠ r → x ∉ S j := by
  classical
  have hex : ∃ r,x ∈ S r := by
    by_contra hn
    have hnot : ∀ r,x ∉ S r := not_exists.mp hn
    simp only [Set.indicator_of_notMem (hnot _),Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨r,hr⟩ := hex
  refine ⟨r,hr,fun j hj hmem => ?_⟩
  have hnon (i : Fin k) : 0 ≤ (S i).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hi : x ∈ S i <;> simp [hi]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({r,j} : Finset (Fin k)) ⊆ Finset.univ from Finset.subset_univ _)
    (fun i _ _ => hnon i)
  have hpair : (∑ i ∈ ({r,j} : Finset (Fin k)),(S i).indicator (fun _ => (1 : ℝ)) x)=2 := by
    norm_num [Ne.symm hj,hr,hmem]
  rw [hpair,hsum] at hle
  norm_num at hle

noncomputable def firstLabelCell (S : Fin k → Set (Space d)) (i : Fin k) : Set (Space d) :=
  S i \ ⋃ j ∈ Finset.univ.filter (fun j => j < i),S j

lemma firstLabelCell_measurable (S : Fin k → Set (Space d))
    (hS : ∀ i,MeasurableSet (S i)) (i : Fin k) : MeasurableSet (firstLabelCell S i) :=
  (hS i).diff ((Finset.univ.filter (fun j => j < i)).measurableSet_biUnion (fun j _ => hS j))

lemma firstLabelCell_disjoint (S : Fin k → Set (Space d)) (i j : Fin k) (hij : i ≠ j) :
    Disjoint (firstLabelCell S i) (firstLabelCell S j) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  change x ∈ S i ∧ x ∉ ⋃ l ∈ Finset.univ.filter (fun l => l < i),S l at hi
  change x ∈ S j ∧ x ∉ ⋃ l ∈ Finset.univ.filter (fun l => l < j),S l at hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · apply hj.2
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩,hi.1⟩⟩
  · apply hi.2
    exact Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hgt⟩,hj.1⟩⟩

lemma firstLabelCell_iff_at_partition_point (S : Fin k → Set (Space d)) (x : Space d)
    (hsum : (∑ i,(S i).indicator (fun _ => (1 : ℝ)) x)=1) (i : Fin k) :
    x ∈ firstLabelCell S i ↔ x ∈ S i := by
  constructor
  · exact fun h => h.1
  · intro hi
    obtain ⟨r,hr,hnot⟩ := indicator_sum_one_unique S x hsum
    have hir : i=r := by
      by_contra hn
      exact hnot i hn hi
    subst i
    refine ⟨hi,?_⟩
    intro hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hm,hsj⟩ := Set.mem_iUnion.mp hj
    exact hnot j (ne_of_lt (Finset.mem_filter.mp hm).2) hsj

lemma firstLabelCell_ae_eq (S : Fin k → Set (Space d))
    (hsum : ∀ᵐ x ∂gaussian d,∑ i,(S i).indicator (fun _ => (1 : ℝ)) x=1) (i : Fin k) :
    ∀ᵐ x ∂gaussian d,x ∈ firstLabelCell S i ↔ x ∈ S i :=
  hsum.mono fun x hx => firstLabelCell_iff_at_partition_point S x hx i

noncomputable def repairedBalancedGaussianCluster (S : Fin k → Set (Space d))
    (hS : ∀ i,MeasurableSet (S i))
    (hsum : ∀ᵐ x ∂gaussian d,∑ i,(S i).indicator (fun _ => (1 : ℝ)) x=1)
    (hmass : ∀ i,(gaussian d).real (S i)=uniformMass k i) : BalancedGaussianCluster d k :=
  { cell := firstLabelCell S
    measurable := firstLabelCell_measurable S hS
    disjoint := firstLabelCell_disjoint S
    cover := hsum.mono fun x hx => by
      obtain ⟨r,hr,_⟩ := indicator_sum_one_unique S x hx
      exact ⟨r,(firstLabelCell_iff_at_partition_point S x hx r).mpr hr⟩
    mass := fun i => by
      rw [← hmass i]
      exact congrArg ENNReal.toReal
        (measure_congr ((firstLabelCell_ae_eq S hsum i).mono fun _ hx => propext hx)) }

end GaussianMeasureBridge
