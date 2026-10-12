import ErdosSimilarityGrowingGaps.SequenceRoutingProbability
import ErdosSimilarityGrowingGaps.RoutingLocalProbability
import ErdosSimilarityGrowingGaps.RoutingLocalProbability
import ErdosSimilarityGrowingGaps.RoutingFactorization
import ErdosSimilarityGrowingGaps.GridCutBridge
import Mathlib.Tactic

namespace ErdosSimilarityGrowingGaps

/-! Boundary-complete local signatures for the actual logarithmic sequence.
The coefficients use `Z.z n` directly, so these signatures can be consumed by
`sequenceLocalAllMiss` without replacing the sampled logarithms by integers. -/

noncomputable def sequenceLowerActivationCut (Z : LogScale) (n : ℕ) (k : ℤ) (u : ℝ) : AffineCut :=
  (Z.z n, 0, -(k : ℝ) - u)

noncomputable def sequenceUpperActivationCut (Z : LogScale) (n : ℕ) (k : ℤ) (v : ℝ) : AffineCut :=
  (-Z.z n, 0, (k : ℝ) + v)

theorem sequence_activation_cut_signs (Z : LogScale) (s₀ s₁ u v : ℝ) (n : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁) :
    sequencePowerActivation Z n k u v p ↔
      cutSign (evalCut (sequenceLowerActivationCut Z n k u) (logPowerParams p)) = .positive ∧
      cutSign (evalCut (sequenceUpperActivationCut Z n k v) (logPowerParams p)) = .positive := by
  rw [cutSign_eq_positive, cutSign_eq_positive]
  simp only [sequencePowerActivation, evalCut,
    sequenceLowerActivationCut, sequenceUpperActivationCut, logPowerParams]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

theorem sequence_grid_boundary_sign (Z : LogScale) (s₀ s₁ x : ℝ) (n N : ℕ) (k b : ℤ)
    (hN : 0 < N) (p : PowerParams s₀ s₁)
    (hβ : 0 < (b : ℝ) / N - x) :
    cutSign (sequencePoint Z n ((2 : ℝ) ^ k) x p - (b : ℝ) / N) =
      cutSign (evalCut (gridCrossingCut (input Z n) ((b : ℝ) / N - x) k)
        (logPowerParams p)) := by
  have hinput : 0 < input Z n := input_pos Z n
  have ht : 0 < p.2.1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) p.2.2.1
  have h := power_grid_cut_sign (input Z n) ((b : ℝ) / N - x) p.1.1 p.2.1 k
    hinput hβ ht
  convert h using 1 <;> simp only [sequencePoint, powerPoint, logPowerParams]
  congr 1
  ring

noncomputable def sequenceParameterCuts {P : ℕ} (Z : LogScale) (x : ℝ)
    (indices grids : Fin P → ℕ) (k : ℤ) (windows : Fin P → ℝ × ℝ) : Finset AffineCut := by
  classical
  exact Finset.univ.biUnion fun i =>
    {sequenceLowerActivationCut Z (indices i) k (windows i).1,
      sequenceUpperActivationCut Z (indices i) k (windows i).2} ∪
    (liftedBoundaryBatch (grids i) x ((2 : ℝ) ^ (1 - (windows i).1))).image
      (fun b : ℤ => gridCrossingCut (input Z (indices i)) ((b : ℝ) / grids i - x) k)

theorem sequenceParameterCuts_card_le {P : ℕ} (Z : LogScale) (x : ℝ)
    (indices grids : Fin P → ℕ) (k : ℤ) (windows : Fin P → ℝ × ℝ) :
    (sequenceParameterCuts Z x indices grids k windows).card ≤
      ∑ i : Fin P, (2 + (liftedBoundaryBatch (grids i) x
        ((2 : ℝ) ^ (1 - (windows i).1))).card) := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i _
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_le_two Finset.card_image_le)

noncomputable def sequenceGridVector {s₀ s₁ : ℝ} {P : ℕ} (Z : LogScale) (x : ℝ)
    (indices grids : Fin P → ℕ) (k : ℤ) (windows : Fin P → ℝ × ℝ)
    (p : PowerParams s₀ s₁) : Fin P → Option ℤ := by
  classical
  exact fun i => if sequencePowerActivation Z (indices i) k (windows i).1 (windows i).2 p
    then some (periodicGridKey (grids i)
      (sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p)) else none

theorem sequence_periodicGridKey_eq_of_local_signs (Z : LogScale) (N : ℕ) (hN : 0 < N)
    (x R z z' : ℝ) (hz : x < z ∧ z < x + R) (hz' : x < z' ∧ z' < x + R)
    (hsig : ∀ b ∈ liftedBoundaryBatch N x R,
      cutSign (z - (b : ℝ) / N) = cutSign (z' - (b : ℝ) / N)) :
    periodicGridKey N z = periodicGridKey N z' :=
  periodicGridKey_eq_of_local_signs N hN x R z z' hz hz' hsig

theorem sequence_active_grid_key_eq_of_log_signs
    (Z : LogScale) (s₀ s₁ x u v : ℝ) (n N : ℕ) (k : ℤ)
    (hN : 0 < N) (p p' : PowerParams s₀ s₁)
    (hp : sequencePowerActivation Z n k u v p)
    (hp' : sequencePowerActivation Z n k u v p')
    (hsig : ∀ b ∈ liftedBoundaryBatch N x ((2 : ℝ) ^ (1 - u)),
      cutSign (evalCut (gridCrossingCut (input Z n) ((b : ℝ) / N - x) k)
        (logPowerParams p)) =
      cutSign (evalCut (gridCrossingCut (input Z n) ((b : ℝ) / N - x) k)
        (logPowerParams p'))) :
    periodicGridKey N (sequencePoint Z n ((2 : ℝ) ^ k) x p) =
      periodicGridKey N (sequencePoint Z n ((2 : ℝ) ^ k) x p') := by
  apply periodicGridKey_eq_of_local_signs N hN x ((2 : ℝ) ^ (1 - u))
    _ _ (sequence_active_point_range Z s₀ s₁ x u v n k p hp)
    (sequence_active_point_range Z s₀ s₁ x u v n k p' hp')
  intro b hb
  have hβ := ((mem_liftedBoundaryBatch_iff N hN x _ b).1 hb).1
  rw [sequence_grid_boundary_sign Z s₀ s₁ x n N k b hN p hβ,
    sequence_grid_boundary_sign Z s₀ s₁ x n N k b hN p' hβ]
  exact hsig b hb

theorem sequence_local_grid_representatives {P : ℕ} (Z : LogScale)
    (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁) (indices grids : Fin P → ℕ)
    (hgrids : ∀ i, 0 < grids i) (k : ℤ) (windows : Fin P → ℝ × ℝ) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * ((sequenceParameterCuts Z x indices grids k windows).card + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        sequenceGridVector Z x indices grids k windows r =
          sequenceGridVector Z x indices grids k windows p := by
  classical
  obtain ⟨reps, hcard, hsig⟩ := power_parameter_finset_sign_representatives s₀ s₁ hs
    (sequenceParameterCuts Z x indices grids k windows)
  refine ⟨reps, hcard, ?_⟩
  intro p
  obtain ⟨r, hr, hsign⟩ := hsig p
  refine ⟨r, hr, ?_⟩
  funext i
  have hlow : sequenceLowerActivationCut Z (indices i) k (windows i).1 ∈
      sequenceParameterCuts Z x indices grids k windows := by
    simp only [sequenceParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_union_left _ (by simp)⟩
  have hhigh : sequenceUpperActivationCut Z (indices i) k (windows i).2 ∈
      sequenceParameterCuts Z x indices grids k windows := by
    simp only [sequenceParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_union_left _ (by simp)⟩
  have ha : sequencePowerActivation Z (indices i) k (windows i).1 (windows i).2 r ↔
      sequencePowerActivation Z (indices i) k (windows i).1 (windows i).2 p := by
    rw [sequence_activation_cut_signs, sequence_activation_cut_signs,
      hsign _ hlow, hsign _ hhigh]
  by_cases hp : sequencePowerActivation Z (indices i) k (windows i).1 (windows i).2 p
  · have hkey := sequence_active_grid_key_eq_of_log_signs Z s₀ s₁ x (windows i).1 (windows i).2
      (indices i) (grids i) k (hgrids i) r p (ha.2 hp) hp (by
        intro b hb
        apply hsign
        simp only [sequenceParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_union_right _ (Finset.mem_image.2 ⟨b, hb, rfl⟩)⟩)
    simp only [sequenceGridVector, ite_eq_left (ha.2 hp), ite_eq_left hp, hkey]
  · have hr' : ¬ sequencePowerActivation Z (indices i) k (windows i).1 (windows i).2 r :=
      fun h => hp (ha.1 h)
    simp [sequenceGridVector, hp, hr']

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

/-- A parameter representative preserves the complete sequence routing event on a
finite outgoing batch.  The finest-grid sizes are fixed by the routing edge,
so the local selector and terminal addresses factor through the vector above. -/
theorem sequence_local_miss_iff_of_gridVector_eq
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (s₀ s₁ x : ℝ) (k : ℤ) (v : InternalNode M d)
    (children : Fin P → Fin (M - 1)) (indices : Fin P → ℕ)
    (grids : Fin P → ℕ) (windows : Fin P → ℝ × ℝ)
    (hgrid : ∀ i, grids i = 2 ^ (c.edgeStar (RoutingTemplate.selectorRoutingEdge
      ⟨v, children i⟩) + 3))
    (hwindow : ∀ i, windows i =
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ),
       (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ) +
         c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩)))
    (p p' : PowerParams s₀ s₁)
    (hvec : sequenceGridVector Z x indices grids k windows p =
      sequenceGridVector Z x indices grids k windows p')
    (ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd)) :
    sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
      (fun i => ⟨v, children i⟩) indices p ω ↔
      sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
        (fun i => ⟨v, children i⟩) indices p' ω := by
  have hactive : ∀ i, sequencePowerActivation Z (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩)) p ↔
      sequencePowerActivation Z (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩)) p' := by
    intro i
    have hh := congrFun hvec i
    simp only [sequenceGridVector] at hh
    split_ifs at hh <;> simp_all
  have hsuccess : ∀ i, sequencePowerActivation Z (indices i) k
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
      ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩)) p →
      ((ω.selectors (selectorAddress c ⟨v, children i⟩
          (sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p)) = true ∧
        ω.terminals (localTerminalAddress c hM hd ω.selectors ⟨v, children i⟩
          (sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p)) = true) ↔
      (ω.selectors (selectorAddress c ⟨v, children i⟩
          (sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p')) = true ∧
        ω.terminals (localTerminalAddress c hM hd ω.selectors ⟨v, children i⟩
          (sequencePoint Z (indices i) ((2 : ℝ) ^ k) x p')) = true)) := by
    intro i hi
    apply actual_local_success_finest_key_iff c hM hd hL ω ⟨v, children i⟩
    apply (gridAddress_eq_iff _ _ _).2
    have hh := congrFun hvec i
    have hiw : sequencePowerActivation Z (indices i) k (windows i).1 (windows i).2 p := by
      simpa [hwindow i] using hi
    have hi' := (hactive i).1 hi
    have hi'w : sequencePowerActivation Z (indices i) k (windows i).1 (windows i).2 p' := by
      simpa [hwindow i] using hi'
    simp only [sequenceGridVector, if_pos hiw, if_pos hi'w] at hh
    have hk := Option.some.inj hh
    rw [hgrid i] at hk
    exact hk
  constructor
  · intro hm i hi hs
    exact hm i ((hactive i).2 hi) ((hsuccess i ((hactive i).2 hi)).2 hs)
  · intro hm i hi hs
    exact hm i ((hactive i).1 hi) ((hsuccess i hi).1 hs)

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

theorem sequenceParameterCuts_card_le_span {P : ℕ} (Z : LogScale) (x : ℝ)
    (indices u v b : Fin P → ℕ) (k : ℤ) (ell : ℕ)
    (hspan : ∀ i, b i + 1 ≤ u i + 2 * ell) :
    (sequenceParameterCuts Z x indices
      (fun i => 2 ^ (b i + 3)) k
      (fun i => ((u i : ℝ), (v i : ℝ)))).card ≤
      P * (3 + 2 ^ (2 * ell + 3)) := by
  have hc := sequenceParameterCuts_card_le Z x indices (fun i => 2 ^ (b i + 3)) k
    (fun i => ((u i : ℝ), (v i : ℝ)))
  have hs : (∑ i : Fin P, (2 + (liftedBoundaryBatch (2 ^ (b i + 3)) x
      ((2 : ℝ) ^ (1 - (u i : ℝ)))).card)) ≤
      ∑ _i : Fin P, (2 + (1 + 2 ^ (2 * ell + 3))) := by
    apply Finset.sum_le_sum
    intro i _
    exact Nat.add_le_add_left (dyadic_boundary_batch_card_le x (u i) (b i) ell (hspan i)) 2
  exact hc.trans (by simpa [← Nat.add_assoc, Nat.mul_comm] using hs)

/-- The actual sequence counterpart of the finite local representative theorem;
all representatives preserve the complete table-valued local miss event. -/
theorem sequence_local_miss_representatives
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁) (k : ℤ)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge
      ⟨v, children i⟩) = ell) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        ∀ ω : FiniteRoutingTables (SelectorAddress c) (TerminalAddress c hd),
          sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
            (fun i => ⟨v, children i⟩) indices r ω ↔
          sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
            (fun i => ⟨v, children i⟩) indices p ω := by
  let grids : Fin P → ℕ := fun i =>
    2 ^ (c.edgeStar (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) + 3)
  let windows : Fin P → ℝ × ℝ := fun i =>
    ((c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ),
      (c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) : ℝ) +
        c.edgeLength (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
  obtain ⟨reps, hc, hr⟩ := sequence_local_grid_representatives Z s₀ s₁ x hs
    indices grids (fun i => pow_pos (by decide) _) k windows
  refine ⟨reps, hc.trans ?_, ?_⟩
  · have hcuts := sequenceParameterCuts_card_le_span Z x indices
      (fun i => c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
      (fun i => c.edgeStart (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩) + ell)
      (fun i => c.edgeStar (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩)) k ell (by
        intro i
        simpa only [hell i] using c.edge_span_bound hM hL
          (RoutingTemplate.selectorRoutingEdge ⟨v, children i⟩))
    have hcuts' : (sequenceParameterCuts Z x indices grids k windows).card ≤
        P * (3 + 2 ^ (2 * ell + 3)) := by
      simpa [grids, windows, hell] using hcuts
    gcongr
  · intro p
    obtain ⟨r, hrm, hvec⟩ := hr p
    refine ⟨r, hrm, ?_⟩
    intro ω
    apply sequence_local_miss_iff_of_gridVector_eq Z c hM hd hL s₀ s₁ x k v
      children indices grids windows
    · intro i
      rfl
    · intro i
      rfl
    · exact hvec

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

/-- Union bound after the sequence representative bridge.  This is the
fixed-parameter probability law lifted to the whole compact parameter
rectangle, with no dyadic replacement of the actual logarithms. -/
theorem sequence_continuum_joint_miss_bound
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (hU : 4 ≤ c.origin) (p s₀ s₁ x η : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hs : s₀ ≤ s₁) (k : ℤ) (bits : SelectorEdge M d → Bool)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge
      ⟨v, children i⟩) = ell)
    (hindex : Function.Injective (fun i => (children i, indices i)))
    (hgap : ∀ r : PowerParams s₀ s₁, ∀ i j, i ≠ j → children i = children j →
      3 ≤ r.1.1 * |Z.z (indices j) - Z.z (indices i)|)
    (hmany : ∀ r : PowerParams s₀ s₁, η * ((M : ℝ) - 1) * ell ≤
      (sequenceActiveLocalCandidates Z c v children indices k r).card) :
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
          (fun i => ⟨v, children i⟩) indices r ω) ≤
    tableProbability (T := TerminalAddress c hd) p
      (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
      (20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) *
      Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
  classical
  obtain ⟨reps, hcard, hrep⟩ := sequence_local_miss_representatives Z c hM hd hL
    s₀ s₁ x hs k v children indices ell hell
  have hub := tableProbability_union_bound p hp₀ hp₁ reps
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
          (fun i => ⟨v, children i⟩) indices r ω)
    (fun r ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
        (fun i => ⟨v, children i⟩) indices r ω) (by
      intro ω hω
      obtain ⟨ha, r, hr⟩ := hω
      obtain ⟨r', hr', heq⟩ := hrep r
      exact ⟨r', hr', ha, (heq ω).2 hr⟩)
  apply hub.trans
  have ha := tableProbability_nonneg (T := TerminalAddress c hd) p hp₀ hp₁
    (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors)
  calc
    _ ≤ ∑ _r ∈ reps,
        tableProbability (T := TerminalAddress c hd) p
          (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
        Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
      apply Finset.sum_le_sum
      intro r _
      rw [sequence_fixed_parameter_joint_miss Z c hM hd hL hU s₀ s₁ x k p
        bits v children indices r hindex (hgap r)]
      exact mul_le_mul_of_nonneg_left
        (fair_selector_terminal_miss_window_bound p η hp₀ hp₁ M _ ell (hmany r)) ha
    _ = tableProbability (T := TerminalAddress c hd) p
        (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
      (reps.card : ℝ) * Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      apply mul_le_mul_of_nonneg_left _ ha
      exact_mod_cast hcard

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

/-- Convenience form when the separation budget is checked at the lower
exponent endpoint of the parameter rectangle. -/
theorem sequence_continuum_joint_miss_bound_of_lower_gap
    {M d P : ℕ} (Z : LogScale) (c : RoutingTemplate M d)
    (hM : 0 < M) (hd : 0 < d) (hL : 0 < c.baseLength)
    (hU : 4 ≤ c.origin) (p s₀ s₁ x η : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hs : s₀ ≤ s₁) (k : ℤ) (bits : SelectorEdge M d → Bool)
    (v : InternalNode M d) (children : Fin P → Fin (M - 1))
    (indices : Fin P → ℕ) (ell : ℕ)
    (hell : ∀ i, c.edgeLength (RoutingTemplate.selectorRoutingEdge
      ⟨v, children i⟩) = ell)
    (hindex : Function.Injective (fun i => (children i, indices i)))
    (hgap₀ : ∀ i j, i ≠ j → children i = children j →
      3 ≤ s₀ * |Z.z (indices j) - Z.z (indices i)|)
    (hmany : ∀ r : PowerParams s₀ s₁, η * ((M : ℝ) - 1) * ell ≤
      (sequenceActiveLocalCandidates Z c v children indices k r).card) :
    tableProbability p (fun ω =>
      centerExposureAtom (actualCenterExposure c x bits) ω.selectors ∧
      ∃ r : PowerParams s₀ s₁,
        sequenceLocalAllMiss Z c hM hd s₀ s₁ x k
          (fun i => ⟨v, children i⟩) indices r ω) ≤
    tableProbability (T := TerminalAddress c hd) p
      (fun ω => centerExposureAtom (actualCenterExposure c x bits) ω.selectors) *
      (20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 : ℕ) *
      Real.exp (-(p * η * ((M : ℝ) - 1) / 2) * ell) := by
  apply sequence_continuum_joint_miss_bound Z c hM hd hL hU p s₀ s₁ x η
    hp₀ hp₁ hs k bits v children indices ell hell hindex
  · intro r i j hij hc
    calc
      3 ≤ s₀ * |Z.z (indices j) - Z.z (indices i)| := hgap₀ i j hij hc
      _ ≤ r.1.1 * |Z.z (indices j) - Z.z (indices i)| := by
        exact mul_le_mul_of_nonneg_right r.1.2.1 (abs_nonneg _)
  · exact hmany

end ErdosSimilarityGrowingGaps
