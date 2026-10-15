import APPTReview.EntropyQuantile
import APPTReview.PhysicalCut

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- Pairing the two extreme blocks controls the full trace deviation. The
unpaired coordinates are bounded by the last paired gap, not by a variance
estimate with an aspect-ratio-dependent loss. -/
theorem paired_pivot_trace_deviation {D R : ℕ} (hR : 0<R) (h2R : 2*R≤D)
    (f : Fin D → ℝ) (hf : Antitone f) (hs : (∑ i,f i)=1) (p : Fin D)
    (hpl : R-1≤p.val) (hpr : p.val≤D-R) :
    let g := sortedGap (show R≤D by omega) f
    |1-(D:ℝ)*f p|≤(∑ i,g i)+(D:ℝ)*g ⟨R-1,by omega⟩ := by
  let g := sortedGap (show R≤D by omega) f
  let l : Fin D := ⟨R-1,by omega⟩
  let r : Fin D := l.rev
  let b := f p
  let w := f l-f r
  let T := D-R
  have hrval : r.val=D-R := by dsimp [r,l];omega
  have hlp : l≤p := hpl
  have hpr' : p≤r := by change p.val≤r.val;rw [hrval];exact hpr
  have hbhi : b≤f l := hf hlp
  have hblo : f r≤b := hf hpr'
  have hw : 0≤w := by dsimp [w];linarith
  have hsumup := prefix_tail_mass (show R+T=D by dsimp [T];omega) f
  have hsumlo := prefix_tail_mass (show T+R=D by dsimp [T];omega) f
  have hu1 (i : Fin R) : f (Fin.castLE (show R≤D by omega) i)≤b+g i := by
    have htail : f (Fin.rev (Fin.castLE (show R≤D by omega) i))≤b := by
      apply hf
      change p.val≤D-(i.val+1)
      have hi:=i.isLt;omega
    dsimp [g,sortedGap];linarith
  have hu2 (i : Fin T) : f (Fin.rev (Fin.castLE (show T≤D by dsimp [T];omega) i))≤b+w := by
    have hx : l≤Fin.rev (Fin.castLE (show T≤D by dsimp [T];omega) i) := by
      change R-1≤D-(i.val+1)
      have hi:=i.isLt;dsimp [T] at hi;omega
    have hh:=hf hx
    dsimp [w];linarith
  have hl1 (i : Fin T) : b-w≤f (Fin.castLE (show T≤D by dsimp [T];omega) i) := by
    have hx : Fin.castLE (show T≤D by dsimp [T];omega) i≤r := by
      change i.val≤r.val;rw [hrval]
      have hi:=i.isLt;dsimp [T] at hi;omega
    have hh:=hf hx
    dsimp [w];linarith
  have hl2 (i : Fin R) : b-g i≤f (Fin.rev (Fin.castLE (show R≤D by omega) i)) := by
    have htop : b≤f (Fin.castLE (show R≤D by omega) i) := by
      apply hf
      change i.val≤p.val
      have hi:=i.isLt;omega
    dsimp [g,sortedGap];linarith
  have H1:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hu1 i)
  have H2:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hu2 i)
  have H3:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hl1 i)
  have H4:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hl2 i)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H1 H2 H3 H4
  rw [hs] at hsumup hsumlo
  have hRT : (R:ℝ)+(T:ℝ)=(D:ℝ) := by exact_mod_cast (show R+T=D by dsimp [T];omega)
  have hTw : (T:ℝ)*w≤(D:ℝ)*w := mul_le_mul_of_nonneg_right
    (by exact_mod_cast (show T≤D by dsimp [T];omega)) hw
  have hDb : (R:ℝ)*b+(T:ℝ)*b=(D:ℝ)*b := by rw [← add_mul,hRT]
  change |1-(D:ℝ)*b|≤(∑ i,g i)+(D:ℝ)*w
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

end APPTReview
