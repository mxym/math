import APPTReview.PrefixMass
import APPTReview.FixedLocalRatio

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The exact maximally entangled witness gives the top-minus-bottom mass
inequality, before any eigenvalue is replaced by a pivot. -/
theorem density_appt_prefix_mass {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A) :
    let R := Fintype.card (UpperPair m)
    let D := Fintype.card (Fin m × Fin n)
    let f := hρ.1.isHermitian.eigenvalues₀
    (∑ i : Fin R,f (Fin.castLE (gapPrefixBound hmn) i)) ≤
      (∑ i : Fin R,f (Fin.rev (Fin.castLE (gapPrefixBound hmn) i)))+
      (∑ i : Fin m,f ⟨D-1-R-i.val,by have hp:=pairPlacementBound hmn;have hi:=i.isLt;omega⟩) := by
  dsimp only
  let f := hρ.1.isHermitian.eigenvalues₀
  let d := placedSpectrum hmn (rowRank m) f
  let G := gapMatrix d
  have hw := appt_all_ordered_pair_witnesses hmn hρ.1.isHermitian happt (rowRank m)
  have hq := hw.dotProduct_mulVec_nonneg (fun _ => (1:ℝ))
  have hg := gapMatrix_hermitian d hw
  have hsym (i j : Fin m) : G i j=G j i := by
    have he := congrArg (fun M => M j i) hg.eq
    simpa [Matrix.conjTranspose_apply] using he
  have hmass := symmetric_degree_mass G hsym (gapMatrix_diag d)
  have he : witnessMatrix d=Matrix.diagonal (fun i => 2*d (i,i))-G := by
    unfold G gapMatrix
    abel
  change 0 ≤ star (fun _ : Fin m => (1:ℝ)) ⬝ᵥ ((witnessMatrix d) *ᵥ (fun _ => 1)) at hq
  rw [he] at hq
  have hcap : (∑ p : UpperPair m,G p.val.1 p.val.2) ≤ ∑ i,d (i,i) := by
    simp only [dotProduct,Matrix.mulVec,star_trivial,one_mul,mul_one] at hq
    simp only [Matrix.sub_apply,Finset.sum_sub_distrib,Matrix.diagonal_apply] at hq
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true] at hq
    rw [hmass] at hq
    simp only [← Finset.mul_sum] at hq
    linarith
  have hsum : (∑ p : UpperPair m,G p.val.1 p.val.2)=
      ∑ i : Fin (Fintype.card (UpperPair m)), sortedGap (gapPrefixBound hmn) f i := by
    dsimp only [G,d]
    simp_rw [placed_gap_eq_sortedGap]
    exact (rowRank m).sum_comp _
  have hdiag (i : Fin m) : d (i,i)=
      f ⟨Fintype.card (Fin m × Fin n)-1-Fintype.card (UpperPair m)-i.val,
        by have hp:=pairPlacementBound hmn;have hi:=i.isLt;omega⟩ := by
    change placedSpectrum hmn (rowRank m) f (squareSlotCoord (.inl i))=_
    rw [placedSpectrum_slot]
    rfl
  rw [hsum] at hcap
  simp_rw [hdiag] at hcap
  simp only [sortedGap,Finset.sum_sub_distrib] at hcap
  linarith

/-- The exact physical APPT cut in the same prefix coordinates as the
ordered-simplex optimization. Neither the cut nor its permutation is assumed. -/
theorem density_appt_ordered_prefix_cut {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (happt : APPT.Quantum.AbsolutelyPPT A)
    (r q : Fin (Fintype.card (Fin m × Fin n)))
    (hr : r.val+1=Fintype.card (UpperPair m))
    (hq : q.val+1+Fintype.card (UpperPair m)+m=Fintype.card (Fin m × Fin n)) :
    (∑ i,prefixCut r q i*hρ.1.isHermitian.eigenvalues₀ i) ≤ 0 := by
  let D := Fintype.card (Fin m × Fin n)
  let R := Fintype.card (UpperPair m)
  let f := hρ.1.isHermitian.eigenvalues₀
  have hplace : 2*R+m ≤ D := pairPlacementBound hmn
  have hcap := density_appt_prefix_mass (by omega : 2 ≤ m) hmn hρ happt
  dsimp only at hcap
  have htail := reversed_tail_split (show R+m ≤ D by omega) f
  have hsplit := prefix_tail_mass (show (q.val+1)+(R+m)=D by omega) f
  have hhead : (∑ i : Fin (r.val+1),f (Fin.castLE (by omega) i))=
      ∑ i : Fin R,f (Fin.castLE (gapPrefixBound hmn) i) := by
    have he := (finCongr (show r.val+1=R from hr)).sum_comp
      (fun i : Fin R => f (Fin.castLE (gapPrefixBound hmn) i))
    convert he using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  rw [prefixCut_mass_identity]
  change (∑ i : Fin (r.val+1),f (Fin.castLE _ i))+
    (∑ i : Fin (q.val+1),f (Fin.castLE _ i))-(∑ i,f i) ≤ 0
  rw [hhead,hsplit,htail]
  linarith

end APPTReview
