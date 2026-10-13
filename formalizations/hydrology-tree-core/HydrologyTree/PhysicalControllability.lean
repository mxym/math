import HydrologyTree.ModalSteering
import HydrologyTree.PhysicalKalman

/-! Actual continuous-time finite-horizon steering for every real full-response
realization, with all spectral and physical prerequisites proved. Real-valued
controls describe the usual signed-input linear controllability, not reachability
under a nonnegative-rainfall constraint. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

/-- Every positive time horizon and every pair of state vectors admit a genuine
continuous forcing reaching the target under the actual original matrix ODE. -/
theorem real_full_response_controllable {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (r w : Fin (n+1) → ℝ) (hr : Function.Injective r) (hpos : ∀ i, 0 < r i)
    (hw : ∀ i, 0 < w i) (hm : (∑ i, w i)=1) (hx : HasStieltjesRootResponse t x r w)
    (T : ℝ) (hT : 0 < T) (z0 z1 : Fin (n+1) → ℝ) :
    ∃ u : ℝ → ℝ, Continuous u ∧
      ∃! z : ℝ → Fin (n+1) → ℝ,
        IsForcedMatrixSolution (compartmentMatrix t x) (Pi.single 0 1) u z ∧ z 0=z0 ∧ z T=z1 := by
  obtain ⟨hP,hF⟩ := (stieltjes_root_response_iff_polynomials t r w hr hpos hw hm x).mp hx
  have hp := real_stieltjes_realization_is_positive t x r w hr hpos hw hm hP hF
  obtain ⟨M,_,hMP,hMF⟩ := physical_root_modal_representation t x (hp.1 0) (fun e => hp.1 e.succ) hp.2
  obtain ⟨e,he,hweights⟩ := stieltjes_pair_matching M.rates r (fun i => (M.amplitudes i)^2) w hr
    (hMP.symm.trans hP) (hMF.symm.trans hF)
  have hMr : Function.Injective M.rates := by
    intro i j hij
    apply e.injective
    apply hr
    rwa [← he i,← he j]
  have hMk : ∀ i, M.amplitudes i ≠ 0 := by
    intro i hi
    have h := hw (e i)
    rw [← hweights i,hi] at h
    norm_num at h
  exact modal_finite_horizon_steering M hMr hMk T hT z0 z1

end HydrologyTree
