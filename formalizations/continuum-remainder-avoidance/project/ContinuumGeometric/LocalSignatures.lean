import ContinuumGeometric.BoundedGrid

/-!
At a FIXED real center, actual active output windows give a finite batch of
strictly positive lifted boundaries. The batch size is independent of the
center. Boundary equality is retained, while inactive tests impose no key.
-/
namespace ContinuumGeometric

theorem dyadic_shifted_offset (n : ℕ) (s t : ℝ) (k : ℤ) :
    t * (2 : ℝ) ^ k * (dyadic n) ^ s =
      t * (2 : ℝ) ^ ((k : ℝ) - s * n) := by
  have hinv : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  have hd : (dyadic n) ^ s = (2 : ℝ) ^ (-(s * n)) := by
    unfold dyadic
    rw [← Real.rpow_natCast_mul (by norm_num), hinv,
      Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [hd, ← Real.rpow_intCast, mul_assoc,
    ← Real.rpow_add (by norm_num)]
  congr 2

/-- Positivity and the strict upper offset bound are derived from actual activation. -/
theorem active_power_point_range (s₀ s₁ x u v : ℝ) (n : ℕ) (k : ℤ)
    (p : PowerParams s₀ s₁) (hactive : p ∈ powerActivation n k u v) :
    x < powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) ∧
      powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p) <
        x + (2 : ℝ) ^ (1 - u) := by
  have ht : 0 < p.2.1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) p.2.2.1
  have hoff : 0 < p.2.1 * (2 : ℝ) ^ k * (dyadic n) ^ p.1.1 := by
    exact mul_pos (mul_pos ht (zpow_pos (by norm_num) k))
      (Real.rpow_pos_of_pos (pow_pos (by norm_num) n) _)
  have hw : u < p.1.1 * n - k := hactive.1
  have hsmall : (2 : ℝ) ^ ((k : ℝ) - p.1.1 * n) < (2 : ℝ) ^ (-u) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hbound : p.2.1 * (2 : ℝ) ^ k * (dyadic n) ^ p.1.1 <
      (2 : ℝ) ^ (1 - u) := by
    rw [dyadic_shifted_offset]
    calc
      p.2.1 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * n) ≤
          2 * (2 : ℝ) ^ ((k : ℝ) - p.1.1 * n) :=
        mul_le_mul_of_nonneg_right p.2.2.2 (Real.rpow_pos_of_pos (by norm_num) _).le
      _ < 2 * (2 : ℝ) ^ (-u) := mul_lt_mul_of_pos_left hsmall (by norm_num)
      _ = (2 : ℝ) ^ (1 - u) := by
        calc
          2 * (2 : ℝ) ^ (-u) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-u) := by
            rw [Real.rpow_one]
          _ = (2 : ℝ) ^ ((1 : ℝ) + -u) := (Real.rpow_add (by norm_num) _ _).symm
          _ = (2 : ℝ) ^ (1 - u) := by congr 1
  change x < x + _ ∧ x + _ < x + _
  exact ⟨by linarith, by linarith⟩

noncomputable def liftedBoundaryBatch (N : ℕ) (x R : ℝ) : Finset ℤ :=
  Finset.Ioo (Int.floor ((N : ℝ) * x)) (Int.ceil ((N : ℝ) * (x + R)))

theorem mem_liftedBoundaryBatch_iff (N : ℕ) (hN : 0 < N) (x R : ℝ) (b : ℤ) :
    b ∈ liftedBoundaryBatch N x R ↔ 0 < (b : ℝ) / N - x ∧ (b : ℝ) / N - x < R := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [liftedBoundaryBatch, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]
  constructor
  · rintro ⟨hl, hu⟩
    have hl' : x < (b : ℝ) / N := (lt_div_iff₀ hNr).2 (by simpa [mul_comm] using hl)
    have hu' : (b : ℝ) / N < x + R :=
      (div_lt_iff₀ hNr).2 (by simpa [mul_comm] using hu)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hl, hu⟩
    constructor
    · simpa [mul_comm] using (lt_div_iff₀ hNr).1 (show x < (b : ℝ) / N by linarith)
    · simpa [mul_comm] using (div_lt_iff₀ hNr).1
        (show (b : ℝ) / N < x + R by linarith)

/-- The number of lifted boundaries costs at most N*R+1, independently of x. -/
theorem liftedBoundaryBatch_card_le (N : ℕ) (hN : 0 < N) (x R : ℝ) (hR : 0 < R) :
    ((liftedBoundaryBatch N x R).card : ℝ) ≤ (N : ℝ) * R + 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hspan : (N : ℝ) * x < (N : ℝ) * (x + R) := by nlinarith
  have hfc : Int.floor ((N : ℝ) * x) < Int.ceil ((N : ℝ) * (x + R)) := by
    exact_mod_cast (Int.floor_le ((N : ℝ) * x)).trans_lt
      (hspan.trans_le (Int.le_ceil ((N : ℝ) * (x + R))))
  have hcard := Int.card_Ioo_of_lt _ _ hfc
  change ((Finset.Ioo _ _).card : ℝ) ≤ _
  have hcast : ((Finset.Ioo (Int.floor ((N : ℝ) * x))
      (Int.ceil ((N : ℝ) * (x + R)))).card : ℝ) =
      (Int.ceil ((N : ℝ) * (x + R)) : ℝ) -
        (Int.floor ((N : ℝ) * x) : ℝ) - 1 := by
    exact_mod_cast hcard
  rw [hcast]
  have hf := Int.lt_floor_add_one ((N : ℝ) * x)
  have hc := Int.ceil_lt_add_one ((N : ℝ) * (x + R))
  nlinarith

/-- Signs at just the positive, relevant lifted boundaries determine actual keys. -/
theorem periodicGridKey_eq_of_local_signs (N : ℕ) (hN : 0 < N) (x R z z' : ℝ)
    (hz : x < z ∧ z < x + R) (hz' : x < z' ∧ z' < x + R)
    (hsig : ∀ b ∈ liftedBoundaryBatch N x R,
      cutSign (z - (b : ℝ) / N) = cutSign (z' - (b : ℝ) / N)) :
    periodicGridKey N z = periodicGridKey N z' := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : Int.floor ((N : ℝ) * z) = Int.floor ((N : ℝ) * z') := by
    apply le_antisymm
    · apply Int.le_floor.2
      by_contra hn
      have hneg : (N : ℝ) * z' < (Int.floor ((N : ℝ) * z) : ℝ) := lt_of_not_ge hn
      have hb : Int.floor ((N : ℝ) * z) ∈ liftedBoundaryBatch N x R := by
        rw [liftedBoundaryBatch, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]
        constructor
        · exact (mul_lt_mul_of_pos_left hz'.1 hNr).trans hneg
        · exact (Int.floor_le _).trans_lt (mul_lt_mul_of_pos_left hz.2 hNr)
      have hbad := hsig _ hb
      rw [← grid_boundary_sign_rescale N hN, ← grid_boundary_sign_rescale N hN] at hbad
      have h := (cutSign_eq_negative _).1
        (hbad.trans ((cutSign_eq_negative _).2 (by linarith)))
      linarith [Int.floor_le ((N : ℝ) * z)]
    · apply Int.le_floor.2
      by_contra hn
      have hneg : (N : ℝ) * z < (Int.floor ((N : ℝ) * z') : ℝ) := lt_of_not_ge hn
      have hb : Int.floor ((N : ℝ) * z') ∈ liftedBoundaryBatch N x R := by
        rw [liftedBoundaryBatch, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]
        constructor
        · exact (mul_lt_mul_of_pos_left hz.1 hNr).trans hneg
        · exact (Int.floor_le _).trans_lt (mul_lt_mul_of_pos_left hz'.2 hNr)
      have hbad := (hsig _ hb).symm
      rw [← grid_boundary_sign_rescale N hN, ← grid_boundary_sign_rescale N hN] at hbad
      have h := (cutSign_eq_negative _).1
        (hbad.trans ((cutSign_eq_negative _).2 (by linarith)))
      linarith [Int.floor_le ((N : ℝ) * z')]
  unfold periodicGridKey
  rw [hf]

/-- All range bounds now follow from strict activation, rather than assumed grid bounds. -/
theorem active_grid_key_eq_of_log_signs (s₀ s₁ x u v : ℝ) (n N : ℕ) (k : ℤ)
    (hN : 0 < N) (p p' : PowerParams s₀ s₁)
    (hp : p ∈ powerActivation n k u v) (hp' : p' ∈ powerActivation n k u v)
    (hsig : ∀ b ∈ liftedBoundaryBatch N x ((2 : ℝ) ^ (1 - u)),
      cutSign (evalCut (gridCrossingCut (dyadic n) ((b : ℝ) / N - x) k)
        (logPowerParams p)) =
      cutSign (evalCut (gridCrossingCut (dyadic n) ((b : ℝ) / N - x) k)
        (logPowerParams p'))) :
    periodicGridKey N (powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p)) =
      periodicGridKey N (powerPoint (dyadic n) ((2 : ℝ) ^ k) (x, p')) := by
  apply periodicGridKey_eq_of_local_signs N hN x ((2 : ℝ) ^ (1 - u))
    _ _ (active_power_point_range s₀ s₁ x u v n k p hp)
    (active_power_point_range s₀ s₁ x u v n k p' hp')
  intro b hb
  have hβ := ((mem_liftedBoundaryBatch_iff N hN x _ b).1 hb).1
  rw [actual_grid_boundary_sign s₀ s₁ x n N k b hN p hβ,
    actual_grid_boundary_sign s₀ s₁ x n N k b hN p' hβ]
  exact hsig b hb

theorem power_parameter_finset_sign_representatives (s₀ s₁ : ℝ) (hs : s₀ ≤ s₁)
    (cuts : Finset AffineCut) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (cuts.card + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps, ∀ c ∈ cuts,
        cutSign (evalCut c (logPowerParams r)) =
          cutSign (evalCut c (logPowerParams p)) := by
  classical
  let e := (Fintype.equivFin {c // c ∈ cuts}).symm
  obtain ⟨reps, hcard, hsig⟩ := power_parameter_sign_representatives s₀ s₁ hs
    (Fintype.card {c // c ∈ cuts}) (fun i => (e i).1)
  refine ⟨reps, ?_, ?_⟩
  · simpa using hcard
  · intro p
    obtain ⟨r, hr, hsign⟩ := hsig p
    refine ⟨r, hr, ?_⟩
    intro c hc
    simpa [e] using hsign (e.symm ⟨c, hc⟩)

noncomputable def localParameterCuts {P : ℕ} (x : ℝ) (indices grids : Fin P → ℕ)
    (k : ℤ) (windows : Fin P → ℝ × ℝ) : Finset AffineCut := by
  classical
  exact Finset.univ.biUnion fun i =>
    {lowerActivationCut (indices i) k (windows i).1,
      upperActivationCut (indices i) k (windows i).2} ∪
    (liftedBoundaryBatch (grids i) x ((2 : ℝ) ^ (1 - (windows i).1))).image
      (fun b : ℤ => gridCrossingCut (dyadic (indices i)) ((b : ℝ) / grids i - x) k)

theorem localParameterCuts_card_le {P : ℕ} (x : ℝ) (indices grids : Fin P → ℕ)
    (k : ℤ) (windows : Fin P → ℝ × ℝ) :
    (localParameterCuts x indices grids k windows).card ≤
      ∑ i : Fin P, (2 + (liftedBoundaryBatch (grids i) x
        ((2 : ℝ) ^ (1 - (windows i).1))).card) := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i _
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_le_two Finset.card_image_le)

/-- Inactive endpoints have value none; an active test carries its ACTUAL finest-grid key. -/
noncomputable def localGridVector {s₀ s₁ : ℝ} {P : ℕ} (x : ℝ)
    (indices grids : Fin P → ℕ) (k : ℤ) (windows : Fin P → ℝ × ℝ)
    (p : PowerParams s₀ s₁) : Fin P → Option ℤ := by
  classical
  exact fun i => if p ∈ powerActivation (indices i) k (windows i).1 (windows i).2
    then some (periodicGridKey (grids i)
      (powerPoint (dyadic (indices i)) ((2 : ℝ) ^ k) (x, p))) else none

/-- A finite, boundary-complete signature determines every active actual local address.
The representatives depend only on the FIXED center and prescribed finite tests,
not on any random selector or terminal table assignment.
-/
theorem actual_local_grid_representatives {P : ℕ} (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁)
    (indices grids : Fin P → ℕ) (hgrids : ∀ i, 0 < grids i) (k : ℤ)
    (windows : Fin P → ℝ × ℝ) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * ((localParameterCuts x indices grids k windows).card + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        localGridVector x indices grids k windows r =
          localGridVector x indices grids k windows p := by
  classical
  obtain ⟨reps, hcard, hsig⟩ := power_parameter_finset_sign_representatives s₀ s₁ hs
    (localParameterCuts x indices grids k windows)
  refine ⟨reps, hcard, ?_⟩
  intro p
  obtain ⟨r, hr, hsign⟩ := hsig p
  refine ⟨r, hr, ?_⟩
  funext i
  have hlow : lowerActivationCut (indices i) k (windows i).1 ∈
      localParameterCuts x indices grids k windows := by
    simp only [localParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_union_left _ (by simp)⟩
  have hhigh : upperActivationCut (indices i) k (windows i).2 ∈
      localParameterCuts x indices grids k windows := by
    simp only [localParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, Finset.mem_union_left _ (by simp)⟩
  have ha : r ∈ powerActivation (indices i) k (windows i).1 (windows i).2 ↔
      p ∈ powerActivation (indices i) k (windows i).1 (windows i).2 := by
    rw [activation_cut_signs, activation_cut_signs, hsign _ hlow, hsign _ hhigh]
  by_cases hp : p ∈ powerActivation (indices i) k (windows i).1 (windows i).2
  · have hkey := active_grid_key_eq_of_log_signs s₀ s₁ x (windows i).1 (windows i).2
      (indices i) (grids i) k (hgrids i) r p (ha.2 hp) hp (by
        intro b hb
        apply hsign
        simp only [localParameterCuts, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, Finset.mem_union_right _ (Finset.mem_image.2 ⟨b, hb, rfl⟩)⟩)
    simp only [localGridVector, ite_eq_left (ha.2 hp), ite_eq_left hp, hkey]
  · have hr' : r ∉ powerActivation (indices i) k (windows i).1 (windows i).2 :=
      fun h => hp (ha.1 h)
    simp [localGridVector, hp, hr']

theorem localParameterCuts_card_le_window_budget {P : ℕ} (x : ℝ)
    (indices grids : Fin P → ℕ) (hgrids : ∀ i, 0 < grids i) (k : ℤ)
    (windows : Fin P → ℝ × ℝ) :
    ((localParameterCuts x indices grids k windows).card : ℝ) ≤
      ∑ i : Fin P, (3 + (grids i : ℝ) * (2 : ℝ) ^ (1 - (windows i).1)) := by
  have hc := localParameterCuts_card_le x indices grids k windows
  have hcr : ((localParameterCuts x indices grids k windows).card : ℝ) ≤
      ∑ i : Fin P, (2 + ((liftedBoundaryBatch (grids i) x
        ((2 : ℝ) ^ (1 - (windows i).1))).card : ℝ)) := by
    exact_mod_cast hc
  apply hcr.trans
  apply Finset.sum_le_sum
  intro i _
  have hb := liftedBoundaryBatch_card_le (grids i) (hgrids i) x
    ((2 : ℝ) ^ (1 - (windows i).1)) (Real.rpow_pos_of_pos (by norm_num) _)
  linarith

/-- Actual dyadic finest grids and the local span bound give the paper's entropy cost. -/
theorem dyadic_boundary_batch_card_le (x : ℝ) (u b ell : ℕ)
    (hspan : b + 1 ≤ u + 2 * ell) :
    (liftedBoundaryBatch (2 ^ (b + 3)) x ((2 : ℝ) ^ (1 - (u : ℝ)))).card ≤
      1 + 2 ^ (2 * ell + 3) := by
  have hN : 0 < (2 : ℕ) ^ (b + 3) := pow_pos (by decide) _
  have hb := liftedBoundaryBatch_card_le (2 ^ (b + 3)) hN x
    ((2 : ℝ) ^ (1 - (u : ℝ))) (Real.rpow_pos_of_pos (by norm_num) _)
  have hpow : (((2 : ℕ) ^ (b + 3) : ℕ) : ℝ) *
      (2 : ℝ) ^ (1 - (u : ℝ)) ≤ (((2 : ℕ) ^ (2 * ell + 3) : ℕ) : ℝ) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num), ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hs : (b : ℝ) + 1 ≤ (u : ℝ) + 2 * ell := by exact_mod_cast hspan
    push_cast
    linarith
  have hcard : ((liftedBoundaryBatch (2 ^ (b + 3)) x
      ((2 : ℝ) ^ (1 - (u : ℝ)))).card : ℝ) ≤
      (1 + (((2 : ℕ) ^ (2 * ell + 3) : ℕ) : ℝ)) := by linarith
  exact_mod_cast hcard

/-- Table readouts of the PROVED actual address vector are uniform in every assignment. -/
theorem actual_local_grid_representatives_uniform {Ω Y : Type*} {P : ℕ}
    (s₀ s₁ x : ℝ) (hs : s₀ ≤ s₁) (indices grids : Fin P → ℕ)
    (hgrids : ∀ i, 0 < grids i) (k : ℤ) (windows : Fin P → ℝ × ℝ)
    (readout : Ω → (Fin P → Option ℤ) → Y) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * ((localParameterCuts x indices grids k windows).card + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps, ∀ ω : Ω,
        readout ω (localGridVector x indices grids k windows r) =
          readout ω (localGridVector x indices grids k windows p) := by
  obtain ⟨reps, hcard, hrep⟩ := actual_local_grid_representatives s₀ s₁ x hs
    indices grids hgrids k windows
  refine ⟨reps, hcard, ?_⟩
  intro p
  obtain ⟨r, hr, heq⟩ := hrep p
  exact ⟨r, hr, fun ω => congrArg (readout ω) heq⟩

theorem localParameterCuts_card_le_span {P : ℕ} (x : ℝ) (indices u v b : Fin P → ℕ)
    (k : ℤ) (ell : ℕ) (hspan : ∀ i, b i + 1 ≤ u i + 2 * ell) :
    (localParameterCuts x indices (fun i => 2 ^ (b i + 3)) k
      (fun i => ((u i : ℝ), (v i : ℝ)))).card ≤ P * (3 + 2 ^ (2 * ell + 3)) := by
  have hc := localParameterCuts_card_le x indices (fun i => 2 ^ (b i + 3)) k
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
theorem actual_local_representatives_entropy_bound {P : ℕ} (s₀ s₁ x : ℝ)
    (hs : s₀ ≤ s₁) (indices u v b : Fin P → ℕ) (k : ℤ) (ell : ℕ)
    (hspan : ∀ i, b i + 1 ≤ u i + 2 * ell) :
    ∃ reps : Finset (PowerParams s₀ s₁),
      reps.card ≤ 20 * (P * (3 + 2 ^ (2 * ell + 3)) + 5) ^ 2 ∧
      ∀ p : PowerParams s₀ s₁, ∃ r ∈ reps,
        localGridVector x indices (fun i => 2 ^ (b i + 3)) k
          (fun i => ((u i : ℝ), (v i : ℝ))) r =
        localGridVector x indices (fun i => 2 ^ (b i + 3)) k
          (fun i => ((u i : ℝ), (v i : ℝ))) p := by
  obtain ⟨reps, hcard, hrep⟩ := actual_local_grid_representatives s₀ s₁ x hs indices
    (fun i => 2 ^ (b i + 3)) (fun i => pow_pos (by decide) _) k
    (fun i => ((u i : ℝ), (v i : ℝ)))
  refine ⟨reps, hcard.trans ?_, hrep⟩
  have hc := localParameterCuts_card_le_span x indices u v b k ell hspan
  gcongr

end ContinuumGeometric
