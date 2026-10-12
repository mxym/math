import APPTReview.PrefixCut

open scoped BigOperators
namespace APPTReview

/-- A prefix indicator sum equals the actual shorter Fin sum. -/
theorem fin_prefix_indicator_sum {D R : ℕ} (hR : R ≤ D) (f : Fin D → ℝ) :
    (∑ i : Fin D, if i.val < R then f i else 0)=∑ i : Fin R,f (Fin.castLE hR i) := by
  obtain ⟨M,rfl⟩ : ∃ M,D=R+M := ⟨D-R,by omega⟩
  rw [Fin.sum_univ_add]
  have hleft (i : Fin R) :
      (if (i.castAdd M).val < R then f (i.castAdd M) else 0)=f (Fin.castLE hR i) := by
    simp only [Fin.val_castAdd, i.isLt,if_true]
    congr 1
  have hright (i : Fin M) :
      (if (Fin.natAdd R i).val < R then f (Fin.natAdd R i) else 0)=0 := by
    simp only [Fin.val_natAdd]
    have h : ¬ R+i.val < R := by omega
    simp [h]
  simp_rw [hleft,hright]
  simp

theorem weighted_prefix_mass {D : ℕ} (r : Fin D) (f : Fin D → ℝ) :
    (∑ i, ((r.val+1:ℕ):ℝ)*uniformPrefix r i*f i)=
      ∑ i : Fin (r.val+1), f (Fin.castLE (by omega) i) := by
  have he (i : Fin D) : ((r.val+1:ℕ):ℝ)*uniformPrefix r i*f i=
      if i.val < r.val+1 then f i else 0 := by
    have hr : ((r.val+1:ℕ):ℝ)≠0 := by positivity
    have hi : (i ≤ r) ↔ i.val < r.val+1 := by change i.val ≤ r.val ↔ _;omega
    unfold uniformPrefix
    simp only [hi]
    split_ifs <;> field_simp <;> ring
  simp_rw [he]
  exact fin_prefix_indicator_sum (by omega) f

/-- Full mass is a prefix plus a reversed tail, with no ordering assumptions. -/
theorem prefix_tail_mass {D T S : ℕ} (hD : T+S=D) (f : Fin D → ℝ) :
    (∑ i, f i)=(∑ i : Fin T, f (Fin.castLE (by omega) i))+
      (∑ i : Fin S, f (Fin.rev (Fin.castLE (by omega) i))) := by
  subst D
  rw [Fin.sum_univ_add]
  have hhead : (∑ i : Fin T, f (i.castAdd S))=∑ i : Fin T,f (Fin.castLE (by omega) i) := by
    congr 1
  rw [hhead]
  congr 1
  have he (i : Fin S) : Fin.rev (Fin.castLE (show S ≤ T+S by omega) i)=Fin.natAdd T i.rev := by
    apply Fin.ext
    dsimp only [Fin.rev,Fin.castLE,Fin.natAdd]
    omega
  simp_rw [he]
  exact (Equiv.sum_comp (Fin.revPerm (n:=S)) (fun i => f (Fin.natAdd T i))).symm

/-- Split the reversed tail into its final R and preceding m entries. -/
theorem reversed_tail_split {D R m : ℕ} (hD : R+m ≤ D) (f : Fin D → ℝ) :
    (∑ i : Fin (R+m), f (Fin.rev (Fin.castLE hD i)))=
      (∑ i : Fin R, f (Fin.rev (Fin.castLE (by omega) i)))+
      (∑ i : Fin m, f ⟨D-1-R-i.val,by have hi:=i.isLt;omega⟩) := by
  rw [Fin.sum_univ_add]
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Fin.ext
    dsimp only [Fin.rev,Fin.castLE,Fin.natAdd]
    omega

/-- Prefix cut rewritten in exactly the top-minus-bottom spectral sums. -/
theorem prefixCut_mass_identity {D : ℕ} (r q : Fin D)
    (f : Fin D → ℝ) :
    (∑ i,prefixCut r q i*f i)=
      (∑ i : Fin (r.val+1),f (Fin.castLE (by omega) i))+
      (∑ i : Fin (q.val+1),f (Fin.castLE (by omega) i))-(∑ i,f i) := by
  unfold prefixCut
  simp_rw [sub_mul,add_mul,one_mul]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,
    weighted_prefix_mass,weighted_prefix_mass]

end APPTReview
