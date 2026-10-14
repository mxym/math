import APPTReview.RetainedGraphBudget

open scoped BigOperators
open Matrix
namespace APPTReview

/-- An increasing injection of finite ordered indices cannot move an index to
its left. Used only to compare the first graph row with the largest gaps. -/
theorem strictMono_fin_val_lower {h R : ℕ} (f : Fin h → Fin R)
    (hf : StrictMono f) (i : Fin h) : i.val≤(f i).val := by
  have H : ∀ k : ℕ, ∀ hk : k<h, k≤(f ⟨k,hk⟩).val := by
    intro k
    induction k with
    | zero => intro hk;omega
    | succ k ih =>
      intro hk
      have hk' : k<h := by omega
      have hh := ih hk'
      have hs := hf (show (⟨k,hk'⟩:Fin h)<⟨k+1,hk⟩ by change k<k+1;omega)
      change (f ⟨k,hk'⟩).val<(f ⟨k+1,hk⟩).val at hs
      omega
  exact H i.val i.isLt

theorem rowRank_first_row_lower {h : ℕ} (i : Fin h) :
    i.val≤(rowRank (h+1) ⟨(0,i.succ),by simp⟩).val := by
  apply strictMono_fin_val_lower (fun j : Fin h => rowRank (h+1) ⟨(0,j.succ),by simp⟩)
  intro j k hjk
  have hle := rowRank_monotone (⟨(0,j.succ),by simp⟩:UpperPair (h+1))
    ⟨(0,k.succ),by simp⟩ (by dsimp [upperPairCode];simp only [zero_mul,zero_add];omega)
  apply lt_of_le_of_ne hle
  intro he
  have hp := (rowRank (h+1)).injective he
  have hv := congrArg (fun p : UpperPair (h+1) => p.val.2.val) hp
  change j.val+1=k.val+1 at hv
  have hnat : j.val<k.val := hjk
  omega

/-- The first residual row is bounded by the actual largest h paired gaps;
no claim that arbitrary independent spectral labels are compatible is needed. -/
theorem residual_first_row_le_head {h n : ℕ} (hh : 1≤h) (hmn : h+1≤n)
    (f : Fin (Fintype.card (Fin (h+1) × Fin n)) → ℝ) (hf : Antitone f)
    (w : ℝ) (hw : 0≤w)
    (hn : ∀ i j,0≤(gapMatrix (placedSpectrum hmn (rowRank (h+1)) f)-w • completeAdjacency :
      Matrix (Fin (h+1)) (Fin (h+1)) ℝ) i j) :
    rowEnergy (gapMatrix (placedSpectrum hmn (rowRank (h+1)) f)-w • completeAdjacency) 0≤
      ∑ i : Fin h,(sortedGap (show h≤Fintype.card (Fin (h+1) × Fin n) by
        have hp:=pairPlacementBound hmn;have hc:=upperPair_card (h+1);nlinarith) f i)^2 := by
  let D := Fintype.card (Fin (h+1) × Fin n)
  let R := Fintype.card (UpperPair (h+1))
  have hR : h≤R := by have hc:=upperPair_card (h+1);dsimp [R];nlinarith
  rw [rowEnergy_zero]
  apply Finset.sum_le_sum
  intro i _
  let p : UpperPair (h+1) := ⟨(0,i.succ),by simp⟩
  let j : Fin R := Fin.castLE hR i
  have hr : j≤rowRank (h+1) p := rowRank_first_row_lower i
  have hgap := sortedGap_antitone (gapPrefixBound hmn) f hf hr
  have he : (gapMatrix (placedSpectrum hmn (rowRank (h+1)) f)-w • completeAdjacency :
      Matrix (Fin (h+1)) (Fin (h+1)) ℝ) 0 i.succ=
      sortedGap (gapPrefixBound hmn) f (rowRank (h+1) p)-w := by
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,completeAdjacency,
      Ne.symm (Fin.succ_ne_zero i),ite_false,mul_one]
    exact congrArg (fun x : ℝ => x-w) (placed_gap_eq_sortedGap hmn (rowRank (h+1)) f p)
  apply pow_le_pow_left₀ (hn 0 i.succ)
  rw [he]
  have hle : sortedGap (gapPrefixBound hmn) f (rowRank (h+1) p)-w≤
      sortedGap (gapPrefixBound hmn) f j := by linarith
  exact hle

end APPTReview
