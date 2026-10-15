import APPTReview.EntropyTaylor
import APPTReview.PrefixMass

open scoped BigOperators
namespace APPTReview

/-- Exactly the nonexceptional coordinates, excluding the first h and last h+1. -/
def entropyBulkIndices (D h : ℕ) : Finset (Fin D) :=
  Finset.univ.filter (fun i => h ≤ i.val ∧ i.val<D-(h+1))

theorem entropy_bulk_partition {D h : ℕ} (hsize : 2*h+1≤D) (F : Fin D → ℝ) :
    (∑ i,F i)=(∑ i : Fin h,F (Fin.castLE (by omega) i))+
      (∑ i∈entropyBulkIndices D h,F i)+
      (∑ i : Fin (h+1),F (Fin.rev (Fin.castLE (by omega) i))) := by
  let T := D-(h+1)
  have hhT : h≤T := by dsimp [T];omega
  have htD : T+(h+1)=D := by dsimp [T];omega
  have he := prefix_tail_mass htD F
  have hbulk : (∑ i∈entropyBulkIndices D h,F i)=
      (∑ i : Fin T,F (Fin.castLE (by omega) i))-
      (∑ i : Fin h,F (Fin.castLE (by omega) i)) := by
    rw [← fin_prefix_indicator_sum (show T≤D by omega),
      ← fin_prefix_indicator_sum (show h≤D by omega),← Finset.sum_sub_distrib]
    unfold entropyBulkIndices
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    change (if h ≤ i.val ∧ i.val<T then F i else 0)=
      (if i.val<T then F i else 0)-(if i.val<h then F i else 0)
    split_ifs <;> simp_all <;> omega
  linarith

/-- Partition the exact logarithmic correction using the same actual head
indices as the shifted physical witness, not independently chosen labels. -/
theorem entropy_remainder_partition {k D : ℕ} (hD : 3*(k+1)+1≤D)
    (f : Fin D → ℝ) (b : ℝ) :
    (∑ i,entropyRemainder (f i/b-1))=
      (∑ i : Fin (k+1),entropyRemainder (sortedHeadA hD f b i))+
      (∑ i∈entropyBulkIndices D (k+1),entropyRemainder (f i/b-1))+
      (∑ i : Fin (k+2),entropyRemainder (-sortedHeadBeta hD f b i)) := by
  have he := entropy_bulk_partition (h:=k+1) (by omega : 2*(k+1)+1≤D)
    (fun i => entropyRemainder (f i/b-1))
  have hh : (∑ i : Fin (k+1),entropyRemainder (f (Fin.castLE (show k+1≤D by omega) i)/b-1))=
      ∑ i : Fin (k+1),entropyRemainder (sortedHeadA hD f b i) := by
    rfl
  have ht : (∑ i : Fin (k+2),entropyRemainder (f (Fin.rev (Fin.castLE (show k+2≤D by omega) i))/b-1))=
      ∑ i : Fin (k+2),entropyRemainder (-sortedHeadBeta hD f b i) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hi : (Fin.rev (Fin.castLE (show k+2≤D by omega) i))=
        (⟨D-(1+i.val),by omega⟩:Fin D) := by
      apply Fin.ext;simp [Fin.val_rev,Nat.add_comm]
    rw [hi]
    unfold sortedHeadBeta
    ring
  rw [hh,ht] at he
  exact he

end APPTReview
