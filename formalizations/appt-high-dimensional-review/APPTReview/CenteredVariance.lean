import APPTReview.SpectralGap
open scoped BigOperators
namespace APPTReview

theorem pair_center_variance (a b t s : ℝ) (ha : t≤a) (hb : b≤s) :
    (a-(t+s)/2)^2+(b-(t+s)/2)^2 ≤
      (a-b)^2-(t-s)*(a-b)+(t-s)^2/2 := by
  have hp := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  nlinarith

theorem interval_center_variance (x t s : ℝ) (hx : s≤x) (ht : x≤t) :
    (x-(t+s)/2)^2 ≤ (t-s)^2/4 := by
  have hp := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr ht)
  nlinarith

theorem trace_one_variance_center {D : ℕ} (hD : 0<D) (f : Fin D → ℝ)
    (hs : (∑ i, f i)=1) (z : ℝ) :
    (∑ i, (f i)^2)-1/(D:ℝ) ≤ ∑ i, (f i-z)^2 := by
  have hn : (D:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have he : (∑ i, (f i-z)^2) - ((∑ i, (f i)^2)-1/(D:ℝ)) =
      (D:ℝ)*(z-1/(D:ℝ))^2 := by
    simp [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, hs]
    field_simp
    ring
  have hp : 0≤(D:ℝ)*(z-1/(D:ℝ))^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  linarith

def topBand (R M : ℕ) (i : Fin R) : Fin (R+(M+R)) := i.castAdd (M+R)
def middleBand (R M : ℕ) (i : Fin M) : Fin (R+(M+R)) := Fin.natAdd R (i.castAdd R)
def bottomBand (R M : ℕ) (i : Fin R) : Fin (R+(M+R)) := Fin.natAdd R (Fin.natAdd M i)

theorem topBand_rev (R M : ℕ) (i : Fin R) :
    (topBand R M i).rev = bottomBand R M i.rev := by
  apply Fin.ext
  dsimp [topBand, bottomBand, Fin.rev, Fin.natAdd, Fin.castAdd]
  have hi := i.isLt
  omega

theorem three_band_sum (R M : ℕ) (f : Fin (R+(M+R)) → ℝ) :
    (∑ i, f i) = (∑ i : Fin R, f (topBand R M i)) +
      (∑ i : Fin M, f (middleBand R M i)) +
      (∑ i : Fin R, f ((topBand R M i).rev)) := by
  have hb : (∑ i : Fin R, f ((topBand R M i).rev)) =
      ∑ i : Fin R, f (bottomBand R M i) := by
    simp_rw [topBand_rev]
    exact Equiv.sum_comp (Fin.revPerm (n:=R)) (fun i => f (bottomBand R M i))
  rw [hb, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [topBand, middleBand, bottomBand]
  ring

def bandTop {R M : ℕ} (hR : 0<R) : Fin (R+(M+R)) := ⟨R-1, by omega⟩
def bandBottom {R M : ℕ} (hR : 0<R) : Fin (R+(M+R)) := (bandTop (M:=M) hR).rev

theorem sorted_centered_variance_bands {R M : ℕ} (hR : 0<R)
    (f : Fin (R+(M+R)) → ℝ) (hf : Antitone f) (hs : (∑ i, f i)=1) :
    let w := f (bandTop hR)-f (bandBottom hR)
    (∑ i, (f i)^2)-1/((R+(M+R):ℕ):ℝ) ≤
      (∑ i : Fin R, (f (topBand R M i)-f ((topBand R M i).rev))^2) -
      w*(∑ i : Fin R, (f (topBand R M i)-f ((topBand R M i).rev))) +
      (((R+(M+R):ℕ):ℝ)/4)*w^2 := by
  dsimp only
  let t := f (bandTop (M:=M) hR)
  let s := f (bandBottom (M:=M) hR)
  let z := (t+s)/2
  have hp (i : Fin R) :
      (f (topBand R M i)-z)^2+(f ((topBand R M i).rev)-z)^2 ≤
      (f (topBand R M i)-f ((topBand R M i).rev))^2 -
      (t-s)*(f (topBand R M i)-f ((topBand R M i).rev))+(t-s)^2/2 := by
    apply pair_center_variance
    · apply hf
      change i.val ≤ R-1
      omega
    · apply hf
      change R+(M+R)-(R-1+1) ≤ R+(M+R)-(i.val+1)
      have hi := i.isLt
      omega
  have hm (i : Fin M) : (f (middleBand R M i)-z)^2 ≤ (t-s)^2/4 := by
    apply interval_center_variance
    · apply hf
      change R+i.val ≤ R+(M+R)-(R-1+1)
      have hi := i.isLt
      omega
    · apply hf
      change R-1 ≤ R+i.val
      omega
  have hpSum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hp i)
  have hmSum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hm i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hpSum hmSum
  have hvar := trace_one_variance_center (show 0<R+(M+R) by omega) f hs z
  rw [three_band_sum R M (fun i => (f i-z)^2)] at hvar
  change (∑ i, (f i)^2)-1/((R+(M+R):ℕ):ℝ) ≤
    (∑ i : Fin R, (f (topBand R M i)-f ((topBand R M i).rev))^2) -
    (t-s)*(∑ i : Fin R, (f (topBand R M i)-f ((topBand R M i).rev))) +
    (((R+(M+R):ℕ):ℝ)/4)*(t-s)^2
  simp only [Nat.cast_add, Finset.sum_sub_distrib] at *
  nlinarith

def finalTop {D R : ℕ} (hR : 0<R) (hRD : R≤D) : Fin D := ⟨R-1, by omega⟩

theorem sorted_centered_variance {D R : ℕ} (hR : 0<R) (h2R : 2*R≤D)
    (f : Fin D → ℝ) (hf : Antitone f) (hs : (∑ i, f i)=1) :
    let hr : R≤D := by omega
    let w := f (finalTop hR hr)-f (finalTop hR hr).rev
    (∑ i, (f i)^2)-1/(D:ℝ) ≤
      (∑ i : Fin R, (sortedGap hr f i)^2)-w*(∑ i : Fin R, sortedGap hr f i)+
        (D:ℝ)/4*w^2 := by
  obtain ⟨M,rfl⟩ : ∃ M, D=R+(M+R) := ⟨D-2*R,by omega⟩
  dsimp only
  have h := sorted_centered_variance_bands (M:=M) hR f hf hs
  dsimp only at h
  exact h

end APPTReview
