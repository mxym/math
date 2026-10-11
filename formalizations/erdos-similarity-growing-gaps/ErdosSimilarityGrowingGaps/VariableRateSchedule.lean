import ErdosSimilarityGrowingGaps.VariableSchedule
import ErdosSimilarityGrowingGaps.RoutingTemplate

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! Scalar parameters for a late annulus.  The activation rate is chosen after
seeing the filling width `D`; the factor `K` is retained in the denominator so
that the child-wise greedy bound has exactly the hypothesis used by
`exists_common_greedy_family`. -/

noncomputable def lateActivationRate (K : ℕ) (δ D : ℝ) : ℝ :=
  1 / (2 * (K : ℝ) * (δ + D))

theorem lateActivationRate_pos (K : ℕ) (hK : 2 ≤ K)
    (δ D : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) :
    0 < lateActivationRate K δ D := by
  unfold lateActivationRate
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  positivity

theorem lateActivationRate_fill_bound (K : ℕ) (hK : 2 ≤ K)
    (δ D ell : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D) (hell : 0 ≤ ell) :
    lateActivationRate K δ D * ell ≤
      ell / (2 * ((K : ℝ) * (δ + D))) := by
  unfold lateActivationRate
  simp only [div_eq_mul_inv]
  ring_nf
  rfl

noncomputable def lateBranching (K : ℕ) (p δ D : ℝ) : ℕ :=
  variableBranching (p / (K : ℝ)) (δ + D)

noncomputable def lateDepth (K : ℕ) (p δ D : ℝ) : ℕ :=
  variableDepth (p / (K : ℝ)) (lateBranching K p δ D)

theorem lateBranching_ge_two (K : ℕ) (p δ D : ℝ) :
    2 ≤ lateBranching K p δ D := by
  exact variableBranching_ge_two _ _

theorem lateDepth_pos (K : ℕ) (hK : 2 ≤ K)
    (p δ D : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1) (hδ : 0 < δ) (hD : 0 ≤ D) :
    0 < lateDepth K p δ D := by
  unfold lateDepth
  apply Nat.ceil_pos.mpr
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hpk : 0 < p / (K : ℝ) := by positivity
  have hpk₂ : p / (K : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hKr).2
    have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hratio : 1 < 2 / (p / (K : ℝ)) := by
    apply (lt_div_iff₀ hpk).2
    nlinarith
  have hlog : 0 < Real.log (2 / (p / (K : ℝ))) := Real.log_pos hratio
  positivity

theorem lateDepth_default_budget (K : ℕ) (hK : 2 ≤ K)
    (p δ D : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1) (hδ : 0 < δ) (hD : 0 ≤ D) :
    (1 - (2 : ℝ) ^ (1 - (lateBranching K p δ D : ℝ))) ^
        lateDepth K p δ D ≤ p := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hpk : 0 < p / (K : ℝ) := by positivity
  have hpk₁ : p / (K : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hKr).2
    have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    nlinarith
  have hM := lateBranching_ge_two K p δ D
  have h := variableDepth_default_budget (p / (K : ℝ)) hpk hpk₁
    (lateBranching K p δ D) hM
  have hhalf : (p / (K : ℝ)) / 2 ≤ p := by
    have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    apply (div_le_iff₀ hKr).2
    nlinarith [hp]
  exact h.trans hhalf

theorem lateBranching_decay_pos (K : ℕ) (hK : 2 ≤ K)
    (p δ D : ℝ) (hp : 0 < p) (hδ : 0 < δ) (hD : 0 ≤ D) :
    0 < p * lateActivationRate K δ D *
        ((lateBranching K p δ D : ℝ) - 1) / 2 - 4 * Real.log 2 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hW : 0 < δ + D := by linarith
  have hη : 0 < lateActivationRate K δ D :=
    lateActivationRate_pos K hK δ D hδ hD
  have hceil : 24 * (δ + D) / (p / (K : ℝ)) ≤
      (Nat.ceil (24 * (δ + D) / (p / (K : ℝ))) : ℝ) := by
    exact Nat.le_ceil _
  have hbranch : 24 * (K : ℝ) * (δ + D) / p ≤
      ((lateBranching K p δ D : ℕ) - 1 : ℝ) := by
    unfold lateBranching variableBranching at *
    push_cast
    have hpk : (p / (K : ℝ)) ≠ 0 := by positivity
    field_simp [hpk] at hceil ⊢
    nlinarith
  have hcoef : 0 ≤ p * lateActivationRate K δ D :=
    (mul_pos hp hη).le
  have hmul := mul_le_mul_of_nonneg_left hbranch hcoef
  have hprod : (12 : ℝ) ≤
      p * lateActivationRate K δ D *
        ((lateBranching K p δ D : ℝ) - 1) := by
    have heq : p * lateActivationRate K δ D *
        (24 * (K : ℝ) * (δ + D) / p) = 12 := by
      unfold lateActivationRate
      field_simp
      ring
    rw [heq] at hmul
    exact hmul
  have hlog : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

/-! An explicit, controlled gap choice.  The linear envelope is deliberately
coarse, but it is sufficient for the variable schedule: the edge count itself
is subexponential in the late origin, so this gap remains subexponential too. -/

noncomputable def linearStableGap (edges : ℕ) (p : ℝ) : ℕ :=
  Nat.ceil (8 * (edges : ℝ) / p)

theorem pow_two_ge_add_one (n : ℕ) :
    (n : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    push_cast
    nlinarith

theorem linearStableGap_upper (edges : ℕ) (p : ℝ) (hp : 0 < p) :
    (linearStableGap edges p : ℝ) ≤ 8 * (edges : ℝ) / p + 1 := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 8 * (edges : ℝ) / p by positivity)
  dsimp [linearStableGap]
  have hc' := le_of_lt hc
  exact_mod_cast hc'

theorem linearStableGap_spec (edges : ℕ) (p : ℝ) (hp : 0 < p) :
    (edges : ℝ) * (2 : ℝ) ^ (3 - (linearStableGap edges p : ℝ)) < p := by
  by_cases he : edges = 0
  · subst edges
    simp [linearStableGap]
    exact hp
  have her : 0 < (edges : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero he)
  let g := linearStableGap edges p
  have hceil : 8 * (edges : ℝ) / p ≤ (g : ℝ) := by
    dsimp [g, linearStableGap]
    exact Nat.le_ceil _
  have hcost : (edges : ℝ) * 8 * (1 / 2 : ℝ) ^ g < p := by
    have hpow : (g : ℝ) + 1 ≤ (2 : ℝ) ^ g := pow_two_ge_add_one g
    have hpowpos : 0 < (g : ℝ) + 1 := by positivity
    have hhalf : (1 / 2 : ℝ) ^ g ≤ 1 / ((g : ℝ) + 1) := by
      rw [one_div_pow]
      exact one_div_le_one_div_of_le hpowpos hpow
    have hlin : 8 * (edges : ℝ) < p * ((g : ℝ) + 1) := by
      have hmul := (div_le_iff₀ hp).1 hceil
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hhalf
      (by positivity : 0 ≤ (edges : ℝ) * 8)
    have hfrac : (edges : ℝ) * 8 / ((g : ℝ) + 1) < p := by
      apply (div_lt_iff₀ hpowpos).2
      nlinarith
    have hfrac' : (edges : ℝ) * 8 * (1 / ((g : ℝ) + 1)) < p := by
      simpa [div_eq_mul_inv] using hfrac
    exact hmul.trans_lt hfrac'
  rw [stable_gap_cost_eq (linearStableGap edges p)]
  simpa [mul_assoc] using hcost

/-! Coarse envelopes for the affine span coefficients.  The base `8*M` in
the gap bound absorbs the additive gap term in its recurrence. -/

theorem routingLengthCoefficient_le_pow (M d : ℕ) (hM : 1 ≤ M) :
    RoutingTemplate.lengthCoefficient M d ≤ (4 * M) ^ d := by
  induction d with
  | zero => simp [RoutingTemplate.lengthCoefficient]
  | succ d ih =>
      by_cases hd : d = 0
      · subst d
        simp [RoutingTemplate.lengthCoefficient]
        omega
      · rw [RoutingTemplate.lengthCoefficient]
        simp only [if_neg hd]
        calc
          2 * M * RoutingTemplate.lengthCoefficient M d ≤
              2 * M * (4 * M) ^ d :=
            Nat.mul_le_mul_left _ ih
          _ ≤ 4 * M * (4 * M) ^ d := by
            gcongr
            omega
          _ = (4 * M) ^ d * (4 * M) := by ac_rfl
          _ = (4 * M) ^ (d + 1) := by rw [pow_succ]

theorem routingGapCoefficient_le_pow (M d : ℕ) (hM : 1 ≤ M) :
    RoutingTemplate.gapCoefficient M d ≤ (8 * M) ^ (d + 1) := by
  induction d with
  | zero => simp [RoutingTemplate.gapCoefficient]
  | succ d ih =>
      by_cases hd : d = 0
      · subst d
        simp [RoutingTemplate.gapCoefficient]
        nlinarith
      · rw [RoutingTemplate.gapCoefficient]
        simp only [if_neg hd]
        have hbase : 1 ≤ 8 * M := by omega
        have hp : 1 ≤ (8 * M) ^ (d + 1) := Nat.one_le_pow _ _ hbase
        have hsum : 1 + RoutingTemplate.gapCoefficient M d ≤
            1 + (8 * M) ^ (d + 1) := by omega
        have hmul := Nat.mul_le_mul_left (2 * M) hsum
        have htot := Nat.add_le_add hmul (show M - 1 ≤ M by omega)
        rw [show d + 1 + 1 = (d + 1) + 1 by omega, pow_succ]
        nlinarith

/-- The depth and stable gap are selected only after the annular width is known.
The gap witness is exposed separately so a later span lemma can impose its
required upper envelope without changing the activation or depth choices. -/
noncomputable def lateStableGap (K : ℕ) (p δ D : ℝ) (hp : 0 < p) : ℕ :=
  Classical.choose (exists_stable_gap_budget
    (Fintype.card (RoutingEdge (lateBranching K p δ D)
      (lateDepth K p δ D))) p hp 0)

theorem lateStableGap_spec (K : ℕ) (p δ D : ℝ) (hp : 0 < p) :
    (Fintype.card (RoutingEdge (lateBranching K p δ D)
      (lateDepth K p δ D)) : ℝ) *
      (2 : ℝ) ^ (3 - (lateStableGap K p δ D hp : ℝ)) < p := by
  exact (Classical.choose_spec (exists_stable_gap_budget
    (Fintype.card (RoutingEdge (lateBranching K p δ D)
      (lateDepth K p δ D))) p hp 0)).2

noncomputable def lateStableGapExplicit (K : ℕ) (p δ D : ℝ) : ℕ :=
  linearStableGap (Fintype.card (RoutingEdge (lateBranching K p δ D)
    (lateDepth K p δ D))) p

theorem lateStableGapExplicit_spec (K : ℕ) (p δ D : ℝ) (hp : 0 < p) :
    (Fintype.card (RoutingEdge (lateBranching K p δ D)
      (lateDepth K p δ D)) : ℝ) *
      (2 : ℝ) ^ (3 - (lateStableGapExplicit K p δ D : ℝ)) < p := by
  exact linearStableGap_spec _ p hp

theorem lateStableGapExplicit_upper (K : ℕ) (p δ D : ℝ) (hp : 0 < p) :
    (lateStableGapExplicit K p δ D : ℝ) ≤
      8 * (Fintype.card (RoutingEdge (lateBranching K p δ D)
        (lateDepth K p δ D)) : ℝ) / p + 1 := by
  exact linearStableGap_upper _ p hp

end ErdosSimilarityGrowingGaps
