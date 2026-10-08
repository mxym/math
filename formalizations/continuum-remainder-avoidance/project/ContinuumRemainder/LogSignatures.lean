import ContinuumRemainder.LogGeometry
import ContinuumGeometric.LocalSignatures

namespace ContinuumRemainder
open ContinuumGeometric Set

noncomputable def logLowerActivationCut (z : ℝ) (k : ℤ) (u : ℝ) : AffineCut :=
  (z,0,-(k:ℝ)-u)
noncomputable def logUpperActivationCut (z : ℝ) (k : ℤ) (v : ℝ) : AffineCut :=
  (-z,0,(k:ℝ)+v)

theorem log_activation_cut_signs (s₀ s₁ u v z : ℝ) (k : ℤ)
    (p : PowerParams s₀ s₁) :
    p ∈ logActivation z k u v ↔
      cutSign (evalCut (logLowerActivationCut z k u) (logPowerParams p)) = .positive ∧
      cutSign (evalCut (logUpperActivationCut z k v) (logPowerParams p)) = .positive := by
  rw [cutSign_eq_positive,cutSign_eq_positive]
  simp only [logActivation,mem_ofPred_eq,evalCut,logLowerActivationCut,
    logUpperActivationCut,logPowerParams]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]

theorem log_grid_boundary_sign (s₀ s₁ x z : ℝ) (N : ℕ) (k b : ℤ)
    (_hN : 0<N) (p : PowerParams s₀ s₁) (hβ : 0<(b:ℝ)/N-x) :
    cutSign (powerPoint (logInput z) ((2:ℝ)^k) (x,p)-(b:ℝ)/N) =
    cutSign (evalCut (gridCrossingCut (logInput z) ((b:ℝ)/N-x) k) (logPowerParams p)) := by
  have ht : 0<p.2.1 := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) p.2.2.1
  have hh:=power_grid_cut_sign (logInput z) ((b:ℝ)/N-x) p.1.1 p.2.1 k (logInput_pos z) hβ ht
  convert hh using 1 <;> simp only [powerPoint,logPowerParams]
  congr 1
  ring

theorem log_grid_key_eq_of_log_signs (s₀ s₁ x u v : ℝ) (z : ℝ) (N : ℕ) (k : ℤ)
    (hN : 0 < N) (p p' : PowerParams s₀ s₁)
    (hp : p ∈ logActivation z k u v) (hp' : p' ∈ logActivation z k u v)
    (hsig : ∀ b ∈ liftedBoundaryBatch N x ((2 : ℝ) ^ (1 - u)),
      cutSign (evalCut (gridCrossingCut (logInput z) ((b : ℝ) / N - x) k)
        (logPowerParams p)) =
      cutSign (evalCut (gridCrossingCut (logInput z) ((b : ℝ) / N - x) k)
        (logPowerParams p'))) :
    periodicGridKey N (powerPoint (logInput z) ((2 : ℝ) ^ k) (x, p)) =
      periodicGridKey N (powerPoint (logInput z) ((2 : ℝ) ^ k) (x, p')) := by
  apply periodicGridKey_eq_of_local_signs N hN x ((2 : ℝ) ^ (1 - u))
    _ _ (log_point_range s₀ s₁ x u v z k p hp)
    (log_point_range s₀ s₁ x u v z k p' hp')
  intro b hb
  have hβ := ((mem_liftedBoundaryBatch_iff N hN x _ b).1 hb).1
  change cutSign (powerPoint (logInput z) ((2 : ℝ) ^ k) (x,p) - (b:ℝ)/N) =
    cutSign (powerPoint (logInput z) ((2 : ℝ) ^ k) (x,p') - (b:ℝ)/N)
  rw [log_grid_boundary_sign s₀ s₁ x z N k b hN p hβ,
    log_grid_boundary_sign s₀ s₁ x z N k b hN p' hβ]
  exact hsig b hb

noncomputable def logParameterCuts {P : ℕ} (x : ℝ) (logs : Fin P → ℝ) (grids : Fin P → ℕ)
    (k : ℤ) (windows : Fin P → ℝ × ℝ) : Finset AffineCut := by
  classical
  exact Finset.univ.biUnion fun i =>
    {logLowerActivationCut (logs i) k (windows i).1,
      logUpperActivationCut (logs i) k (windows i).2} ∪
    (liftedBoundaryBatch (grids i) x ((2 : ℝ) ^ (1 - (windows i).1))).image
      (fun b : ℤ => gridCrossingCut (logInput (logs i)) ((b : ℝ) / grids i - x) k)

theorem logParameterCuts_card_le {P : ℕ} (x : ℝ) (logs : Fin P → ℝ) (grids : Fin P → ℕ)
    (k : ℤ) (windows : Fin P → ℝ × ℝ) :
    (logParameterCuts x logs grids k windows).card ≤
      ∑ i : Fin P, (2 + (liftedBoundaryBatch (grids i) x
        ((2 : ℝ) ^ (1 - (windows i).1))).card) := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i _
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_le_two Finset.card_image_le)

/-- Inactive endpoints have value none; an active test carries its ACTUAL finest-grid key. -/
noncomputable def logGridVector {s₀ s₁ : ℝ} {P : ℕ} (x : ℝ)
    (logs : Fin P → ℝ) (grids : Fin P → ℕ) (k : ℤ) (windows : Fin P → ℝ × ℝ)
    (p : PowerParams s₀ s₁) : Fin P → Option ℤ := by
  classical
  exact fun i => if p ∈ logActivation (logs i) k (windows i).1 (windows i).2
    then some (periodicGridKey (grids i)
      (powerPoint (logInput (logs i)) ((2 : ℝ) ^ k) (x, p))) else none

/-- A finite, boundary-complete signature determines every active actual local address.
The representatives depend only on the FIXED center and prescribed finite tests,
not on any random selector or terminal table assignment.
-/
theorem log_local_grid_representatives {P : ℕ} (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁)
    (logs : Fin P → ℝ) (grids : Fin P → ℕ) (hgrids : ∀ i, 0 < grids i) (k : ℤ)
    (windows : Fin P → ℝ × ℝ) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * ((logParameterCuts x logs grids k windows).card + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        logGridVector x logs grids k windows r =
          logGridVector x logs grids k windows p := by
  classical
  obtain ⟨reps, hcard, hsig⟩ := power_parameter_finset_sign_representatives s₀ s₁ hs
    (logParameterCuts x logs grids k windows)
  refine ⟨reps, hcard, ?_⟩
  intro p
  obtain ⟨r, hr, hsign⟩ := hsig p
  refine ⟨r, hr, ?_⟩
  funext i
  have hlow : logLowerActivationCut (logs i) k (windows i).1 ∈
      logParameterCuts x logs grids k windows := by
    simp only [logParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_union_left _ (by simp)⟩
  have hhigh : logUpperActivationCut (logs i) k (windows i).2 ∈
      logParameterCuts x logs grids k windows := by
    simp only [logParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_union_left _ (by simp)⟩
  have ha : r ∈ logActivation (logs i) k (windows i).1 (windows i).2 ↔
      p ∈ logActivation (logs i) k (windows i).1 (windows i).2 := by
    rw [log_activation_cut_signs, log_activation_cut_signs, hsign _ hlow, hsign _ hhigh]
  by_cases hp : p ∈ logActivation (logs i) k (windows i).1 (windows i).2
  · have hkey := log_grid_key_eq_of_log_signs s₀ s₁ x (windows i).1 (windows i).2
      (logs i) (grids i) k (hgrids i) r p (ha.2 hp) hp (by
        intro b hb
        apply hsign
        simp only [logParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_union_right _ (Finset.mem_image.2 ⟨b, hb, rfl⟩)⟩)
    simp only [logGridVector, ite_eq_left (ha.2 hp), ite_eq_left hp, hkey]
  · have hr' : r ∉ logActivation (logs i) k (windows i).1 (windows i).2 :=
      fun h => hp (ha.1 h)
    simp [logGridVector, hp, hr']

theorem logParameterCuts_card_le_window_budget {P : ℕ} (x : ℝ)
    (logs : Fin P → ℝ) (grids : Fin P → ℕ) (hgrids : ∀ i, 0 < grids i) (k : ℤ)
    (windows : Fin P → ℝ × ℝ) :
    ((logParameterCuts x logs grids k windows).card : ℝ) ≤
      ∑ i : Fin P, (3 + (grids i : ℝ) * (2 : ℝ) ^ (1 - (windows i).1)) := by
  have hc := logParameterCuts_card_le x logs grids k windows
  have hcr : ((logParameterCuts x logs grids k windows).card : ℝ) ≤
      ∑ i : Fin P, (2 + ((liftedBoundaryBatch (grids i) x
        ((2 : ℝ) ^ (1 - (windows i).1))).card : ℝ)) := by
    exact_mod_cast hc
  apply hcr.trans
  apply Finset.sum_le_sum
  intro i _
  have hb := liftedBoundaryBatch_card_le (grids i) (hgrids i) x
    ((2 : ℝ) ^ (1 - (windows i).1)) (Real.rpow_pos_of_pos (by norm_num) _)
  linarith

/-- Table readouts of the PROVED actual address vector are uniform in every assignment. -/
theorem log_local_grid_representatives_uniform {Ω Y : Type*} {P : ℕ}
    (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁) (logs : Fin P → ℝ) (grids : Fin P → ℕ)
    (hgrids : ∀ i, 0 < grids i) (k : ℤ) (windows : Fin P → ℝ × ℝ)
    (readout : Ω → (Fin P → Option ℤ) → Y) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * ((logParameterCuts x logs grids k windows).card + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps, ∀ ω : Ω,
        readout ω (logGridVector x logs grids k windows r) =
          readout ω (logGridVector x logs grids k windows p) := by
  obtain ⟨reps, hcard, hrep⟩ := log_local_grid_representatives s₀ s₁ x hs
    logs grids hgrids k windows
  refine ⟨reps, hcard, ?_⟩
  intro p
  obtain ⟨r, hr, heq⟩ := hrep p
  exact ⟨r, hr, fun ω => congrArg (readout ω) heq⟩

theorem logParameterCuts_card_le_span {P : ℕ} (x : ℝ) (logs : Fin P → ℝ) (u v b : Fin P → ℕ)
    (k : ℤ) (ell : ℕ) (hspan : ∀ i, b i + 1 ≤ u i + 2 * ell) :
    (logParameterCuts x logs (fun i => 2 ^ (b i + 3)) k
      (fun i => ((u i : ℝ), (v i : ℝ)))).card ≤ P * (3 + 2 ^ (2 * ell + 3)) := by
  have hc := logParameterCuts_card_le x logs (fun i => 2 ^ (b i + 3)) k
    (fun i => ((u i : ℝ), (v i : ℝ)))
  have hs : (∑ i : Fin P, (2 + (liftedBoundaryBatch (2 ^ (b i + 3)) x
      ((2 : ℝ) ^ (1 - (u i : ℝ)))).card)) ≤
      ∑ _i : Fin P, (2 + (1 + 2 ^ (2 * ell + 3))) := by
    apply Finset.sum_le_sum
    intro i _
    exact Nat.add_le_add_left (dyadic_boundary_batch_card_le x (u i) (b i) ell (hspan i)) 2
  exact hc.trans (by simpa [← Nat.add_assoc, Nat.mul_comm] using hs)

/-- The exact local continuum entropy bound, with actual grids and zero-sign strata.
No center grid or probabilistic routing hypothesis is used. P is the prescribed
finite candidate-pair count; its output-window bound remains a separate obligation.
-/
theorem log_representatives_entropy_bound {P : ℕ} (s₀ s₁ x : ℝ)
    (hs : s₀ ≤ s₁) (logs : Fin P → ℝ) (u v b : Fin P → ℕ) (k : ℤ) (ell : ℕ)
    (hspan : ∀ i, b i + 1 ≤ u i + 2 * ell) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        logGridVector x logs (fun i => 2 ^ (b i + 3)) k
          (fun i => ((u i : ℝ), (v i : ℝ))) r =
        logGridVector x logs (fun i => 2 ^ (b i + 3)) k
          (fun i => ((u i : ℝ), (v i : ℝ))) p := by
  obtain ⟨reps, hcard, hrep⟩ := log_local_grid_representatives s₀ s₁ x hs logs
    (fun i => 2 ^ (b i + 3)) (fun i => pow_pos (by decide) _) k
    (fun i => ((u i : ℝ), (v i : ℝ)))
  refine ⟨reps, hcard.trans ?_, hrep⟩
  have hc := logParameterCuts_card_le_span x logs u v b k ell hspan
  gcongr

end ContinuumRemainder
