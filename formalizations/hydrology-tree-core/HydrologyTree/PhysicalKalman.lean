import HydrologyTree.ModalKalman
import HydrologyTree.PhysicalModalConstruction
import HydrologyTree.StieltjesWeightedMatching
import HydrologyTree.RealFiberClassification

/-! Full-mode Kalman controllability/observability in the original physical
coordinates. This alone is not called continuous-time steering; the actual
trajectory observation and reachability statements require their own bridges. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

/-- Nonsingularity of BOTH actual root Kalman matrices is a proved consequence
of the prescribed full response, for unrestricted real competing parameters. -/
theorem real_full_response_kalman_nonsingular {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (hx : HasStieltjesRootResponse t x r w) :
    (rootKrylovMatrix (compartmentMatrix t x)).det ≠ 0 ∧
      (rootObservationMatrix (compartmentMatrix t x)).det ≠ 0 := by
  obtain ⟨hP,hF⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp hx
  have hp := real_stieltjes_realization_is_positive t x r w hr hpos hw hm hP hF
  obtain ⟨M,_,hMP,hMF⟩ := physical_root_modal_representation t x (hp.1 0) (fun e => hp.1 e.succ) hp.2
  obtain ⟨e,he,hweights⟩ := stieltjes_pair_matching M.rates r (fun i => (M.amplitudes i)^2) w hr
    (hMP.symm.trans hP) (hMF.symm.trans hF)
  apply rootModal_kalman_nonsingular M
  · intro i j hij
    apply e.injective
    apply hr
    rwa [← he i,← he j]
  · intro i hi
    have h := hw (e i)
    rw [← hweights i,hi] at h
    norm_num at h

end HydrologyTree
