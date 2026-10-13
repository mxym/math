import HydrologyTree.SignedFamilyResultant

/-! Exact finite-family enumeration of the physical numerator sum.
Index conversion preserves all terms, including repeated polynomial values. -/
open Polynomial
noncomputable section
namespace HydrologyTree

variable {ι : Type*} [DecidableEq ι]

def finiteResultantNumerator (s : Finset ι) (p r : ι → ℝ[X]) : ℝ[X] :=
  ∑ i ∈ s, r i * ∏ j ∈ s.erase i, p j

lemma finiteResultantNumerator_insert (s : Finset ι) (p r : ι → ℝ[X])
    (a : ι) (ha : a ∉ s) :
    finiteResultantNumerator (insert a s) p r =
      r a * (∏ i ∈ s, p i) + p a * finiteResultantNumerator s p r := by
  rw [finiteResultantNumerator,Finset.sum_insert ha,Finset.erase_insert ha]
  congr 1
  rw [finiteResultantNumerator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hia : i ≠ a := by intro h; exact ha (h ▸ hi)
  have hae : a ∉ s.erase i := fun h => ha (Finset.mem_of_mem_erase h)
  rw [Finset.erase_insert_of_ne (Ne.symm hia),Finset.prod_insert hae]
  ring

lemma resultantFamilyNumerator_map (l : List ι) (hl : l.Nodup) (p r : ι → ℝ[X]) :
    resultantFamilyNumerator (l.map fun i => (p i,r i)) = finiteResultantNumerator l.toFinset p r := by
  induction l with
  | nil => simp [resultantFamilyNumerator,finiteResultantNumerator]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    rw [List.map_cons,resultantFamilyNumerator,List.toFinset_cons,
      finiteResultantNumerator_insert l.toFinset p r a (by simpa using ha),ih hl]
    rw [List.map_map]
    rw [List.prod_toFinset p hl]
    rfl

/-- Rate-independent enumeration of a finite index type. -/
def resultantEnumeration (ι : Type*) [Fintype ι] : List ι :=
  List.ofFn (fun i : Fin (Fintype.card ι) => (Fintype.equivFin ι).symm i)

lemma resultantEnumeration_nodup [Fintype ι] : (resultantEnumeration ι).Nodup :=
  List.nodup_ofFn_ofInjective (Fintype.equivFin ι).symm.injective

lemma resultantEnumeration_toFinset [Fintype ι] : (resultantEnumeration ι).toFinset = Finset.univ := by
  ext i
  simp only [List.mem_toFinset,Finset.mem_univ,iff_true,resultantEnumeration,List.mem_ofFn]
  exact ⟨(Fintype.equivFin ι) i,(Fintype.equivFin ι).symm_apply_apply i⟩

lemma resultantEnumeration_prod [Fintype ι] {α : Type*} [CommMonoid α] (f : ι → α) :
    ((resultantEnumeration ι).map f).prod = ∏ i, f i := by
  rw [← List.prod_toFinset f resultantEnumeration_nodup,resultantEnumeration_toFinset]

lemma resultantFamilyNumerator_enumeration [Fintype ι] (p r : ι → ℝ[X]) :
    resultantFamilyNumerator ((resultantEnumeration ι).map fun i => (p i,r i)) =
      ∑ i, r i * ∏ j ∈ Finset.univ.erase i, p j := by
  rw [resultantFamilyNumerator_map _ resultantEnumeration_nodup,
    resultantEnumeration_toFinset]
  rfl

/-- Exact signed finite-family formula in the ordinary product/sum notation. -/
theorem finite_family_signed_resultant [Fintype ι] (p r : ι → ℝ[X]) (hp : ∀ i, (p i).Monic) :
    (∏ i, p i).resultant (∑ i, r i * ∏ j ∈ Finset.univ.erase i, p j) =
      resultantPairSign ((resultantEnumeration ι).map fun i => (p i).natDegree) *
        (∏ i, (p i).resultant (r i)) *
        pairwiseResultants ((resultantEnumeration ι).map p)^2 := by
  have hm : ∀ q ∈ (resultantEnumeration ι).map (fun i => (p i,r i)), q.1.Monic := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
    exact hp i
  have h := resultant_family_factorization _ hm
  have hden : (((resultantEnumeration ι).map fun i => (p i,r i)).map Prod.fst).prod = ∏ i, p i := by
    rw [List.map_map]
    exact resultantEnumeration_prod p
  rw [hden,resultantFamilyNumerator_enumeration] at h
  simpa only [List.map_map,Function.comp_def,resultantEnumeration_prod] using h

end HydrologyTree
