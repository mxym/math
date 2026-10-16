import Spectrum.Variational
import Spectrum.PhysicalTensor
import Spectrum.ConverseLimit
import Mathlib.Analysis.MeanInequalities

open scoped BigOperators ComplexOrder Classical Topology
open Filter
open Matrix

namespace ExtractionSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Finite Holder interpolation from a genuine quadratic budget and the unit
effect cap, including zero diagonal entries. -/
theorem finite_holder_budget_bound (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) (r α : ℝ)
    (hbudget : ∑ i, z i ^ 2 ≤ r) (hαlo : 1 < α) (hαhi : α ≤ 2) :
    ∑ i, p i * z i ≤ (partition p α) ^ (1 / α) * r ^ ((α - 1) / α) := by
  let q := α / (α - 1)
  have hαp : 0 < α := lt_trans zero_lt_one hαlo
  have hdiff : 0 < α - 1 := sub_pos.mpr hαlo
  have hqp : 0 < q := div_pos hαp hdiff
  have hq2 : 2 ≤ q := by
    apply (le_div_iff₀ hdiff).mpr
    linarith
  have hpq : α.HolderConjugate q :=
    (Real.holderConjugate_iff_eq_conjExponent hαlo).mpr rfl
  have hsum : ∑ i, (z i) ^ q ≤ r := by
    calc
      ∑ i, (z i) ^ q ≤ ∑ i, z i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.rpow_two] using
          Real.rpow_le_rpow_of_exponent_ge' (hz i).1 (hz i).2 (by norm_num : (0 : ℝ) ≤ 2) hq2
      _ ≤ r := hbudget
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hpq
    (fun i _ => hp i) (fun i _ => (hz i).1)
  have hrpow := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hz i).1 q) hsum
    (div_nonneg zero_le_one hqp.le)
  have hqinv : 1 / q = (α - 1) / α := by dsimp [q]; field_simp
  exact hH.trans (by simpa only [hqinv, partition] using
    mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg (Finset.sum_nonneg
      (fun i _ => Real.rpow_nonneg (hp i) α)) (1 / α)))

/-- Rescaling proves the finite capped version without dropping the quadratic
budget. The cap beta is an actual numerical matrix order cap at the next step. -/
theorem finite_capped_holder_bound (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (β : ℝ) (hβ : 0 < β) (hz : ∀ i, 0 ≤ z i ∧ z i ≤ β) (r α : ℝ)
    (hbudget : ∑ i, z i ^ 2 ≤ r) (hαlo : 1 < α) (hαhi : α ≤ 2) :
    ∑ i, p i * z i ≤ β * ((partition p α) ^ (1 / α) *
      (r / β ^ 2) ^ ((α - 1) / α)) := by
  have hcap (i : ι) : 0 ≤ z i / β ∧ z i / β ≤ 1 :=
    ⟨div_nonneg (hz i).1 hβ.le, (div_le_one hβ).mpr (hz i).2⟩
  have hb : ∑ i, (z i / β) ^ 2 ≤ r / β ^ 2 := by
    simp only [div_pow, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right hbudget (sq_nonneg β)
  have h := finite_holder_budget_bound p (fun i => z i / β) hp hcap
    (r / β ^ 2) α hb hαlo hαhi
  have he : ∑ i, p i * z i = β * ∑ i, p i * (z i / β) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left h hβ.le

variable [DecidableEq ι]

/-- A capped matrix effect obeys the finite Holder bound in any explicitly
constructed spectral basis. Every diagonal norm and order bound is derived. -/
theorem diagonalized_effect_holder_bound (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (V : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (β : ℝ) (hβ : 0 < β)
    (hcap : (β • (1 : Matrix ι ι ℂ) - M).PosSemidef)
    (r α : ℝ) (hbudget : (M * M).trace.re ≤ r) (hαlo : 1 < α) (hαhi : α ≤ 2) :
    (M * ((V : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (p i : ℂ)) *
      (V : Matrix ι ι ℂ)ᴴ)).trace.re ≤ β * ((partition p α) ^ (1 / α) *
        (r / β ^ 2) ^ ((α - 1) / α)) := by
  let Q := (V : Matrix ι ι ℂ)ᴴ * M * V
  let z : ι → ℝ := fun i => (Q i i).re
  have hQ : Q.PosSemidef := hM.conjTranspose_mul_mul_same _
  have hV : (V : Matrix ι ι ℂ)ᴴ * V = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hβQ : (β • (1 : Matrix ι ι ℂ) - Q).PosSemidef := by
    have h := hcap.conjTranspose_mul_mul_same (V : Matrix ι ι ℂ)
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hV] using h
  have hz (i : ι) : 0 ≤ z i ∧ z i ≤ β := by
    have h0 := (RCLike.nonneg_iff.mp (hQ.diag_nonneg (i := i))).1
    have h1 := (RCLike.nonneg_iff.mp (hβQ.diag_nonneg (i := i))).1
    change 0 ≤ (Q i i).re ∧ (Q i i).re ≤ β
    constructor
    · exact h0
    · simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        Complex.sub_re, Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] using sub_nonneg.mp h1
  have hzb : ∑ i, z i ^ 2 ≤ r := by
    calc
      ∑ i, z i ^ 2 ≤ (Q * Q).trace.re := diagonal_square_le_trace_square Q hQ.isHermitian
      _ = (M * M).trace.re := congrArg Complex.re (trace_square_unitary_congruence M V)
      _ ≤ r := hbudget
  rw [Extraction.trace_congruence_diagonal]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have he : (∑ i, (((V : Matrix ι ι ℂ)ᴴ * M * V) i i).re * p i) =
      ∑ i, p i * z i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [he]
  exact finite_capped_holder_bound p z hp β hβ hz r α hzb hαlo hαhi

variable {a b d κ : Type*} [Fintype a] [Fintype b] [Fintype d] [Fintype κ]
  [DecidableEq a] [DecidableEq b] [DecidableEq d] [Nonempty d]

/-- The finite Renyi/Holder converse for a physical channel and every original
global unitary. The effect order and HS budget are derived from the channel. -/
theorem kraus_target_holder_bound
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (X : Matrix (a × b) (a × b) ℂ) (hX : APPT.Quantum.IsDensity X)
    (U : Matrix.unitaryGroup (a × b) ℂ) (α : ℝ) (hαlo : 1 < α) (hαhi : α ≤ 2) :
    (Extraction.bellProjector (d := d) * Extraction.krausApply A
      ((U : Matrix _ _ ℂ) * X * (U : Matrix _ _ ℂ)ᴴ)).trace.re ≤
      (partition hX.1.isHermitian.eigenvalues α) ^ (1 / α) *
        ((Fintype.card a * Fintype.card b : ℝ) / (Fintype.card d : ℝ)^2) ^ ((α - 1) / α) := by
  let V := hX.1.isHermitian.eigenvectorUnitary
  have hsp : (U : Matrix _ _ ℂ) * X * (U : Matrix _ _ ℂ)ᴴ =
      ((U * V : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        Matrix.diagonal (fun i => (hX.1.isHermitian.eigenvalues i : ℂ)) *
      ((U * V : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)ᴴ := by
    have h := hX.1.isHermitian.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] at h
    conv_lhs => rw [h]
    simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rfl
  rw [Extraction.target_overlap_eq, hsp]
  have hM := Extraction.targetEffect_rains A hcomplete hpt
  have h := diagonalized_effect_holder_bound hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (U * V) (Extraction.targetEffect A)
    hM.1 1 (by norm_num) (by simpa only [one_smul] using hM.2.1) _ α
    (Extraction.rainsEffect_trace_square_le _ _ hM) hαlo hαhi
  simpa only [one_pow, div_one, one_mul] using h

theorem iidLaw_partition (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ) (α : ℝ) :
    partition (iidLaw p k) α = (partition p α) ^ k := by
  unfold partition
  calc
    (∑ w, (iidLaw p k w) ^ α) = ∑ w : Fin k → ι, ∏ j, (p (w j)) ^ α := by
      apply Finset.sum_congr rfl
      intro w _
      exact (Real.finsetProd_rpow Finset.univ (fun j => p (w j)) (fun j _ => hp _) α).symm
    _ = _ := (Fintype.sum_pow (fun i => (p i) ^ α) k).symm

theorem partition_reindex {κ : Type*} [Fintype κ]
    (p : ι → ℝ) (e : κ ≃ ι) (α : ℝ) :
    partition (p ∘ e) α = partition p α := e.sum_comp fun i => (p i) ^ α

/-- Normalization gives a strictly positive moment even when the law contains
zeros. No positive-spectrum assumption is imposed on a density matrix. -/
theorem partition_pos_of_normalized (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (α : ℝ) : 0 < partition p α := by
  have hsum : 0 < ∑ i, p i := by rw [hs]; norm_num
  obtain ⟨i, hiU, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hp j)).mp hsum
  exact Finset.sum_pos' (fun j _ => Real.rpow_nonneg (hp j) α)
    ⟨i, hiU, Real.rpow_pos_of_pos hi α⟩

theorem holder_moment_eq_exp (Z : ℝ) (hZ : 0 < Z) (k : ℕ)
    (r : ℝ) (hr : 0 < r) (α : ℝ) :
    (Z ^ k) ^ (1 / α) * r ^ ((α - 1) / α) =
      Real.exp ((k : ℝ) * Real.log Z / α + Real.log r * ((α - 1) / α)) := by
  rw [Real.rpow_def_of_pos (pow_pos hZ k), Real.rpow_def_of_pos hr,
    ← Real.exp_add, Real.log_pow]
  congr 1
  ring

/-- An actual finite Holder moment bound has the asserted exponential rate.
The formulation avoids the totalized logarithm of a possibly zero fidelity. -/
theorem holder_bound_eventually_exponential (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (F r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (c α : ℝ)
    (hu : ∀ n, F n ≤ ((partition p α) ^ n) ^ (1 / α) *
      (r n) ^ ((α - 1) / α))
    (hrate : Tendsto (fun n : ℕ => Real.log (r n) / n) atTop (𝓝 c))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, F n ≤
      Real.exp (-(n : ℝ) * (dualObjective p c α - η)) := by
  have hlim := (tendsto_const_nhds (x := Real.log (partition p α) / α)).add
    (hrate.const_mul ((α - 1) / α))
  have he : Real.log (partition p α) / α + ((α - 1) / α) * c =
      -dualObjective p c α := by unfold dualObjective; ring
  have hh : Tendsto (fun n : ℕ => Real.log (partition p α) / α +
      ((α - 1) / α) * (Real.log (r n) / n)) atTop
      (𝓝 (-dualObjective p c α)) := by
    rw [← he]
    exact hlim
  filter_upwards [hh.eventually_lt_const (show -dualObjective p c α <
    -dualObjective p c α + η by linarith), eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hprod := mul_lt_mul_of_pos_left hn hnR
  have hcancel : (n : ℝ) * (((α - 1) / α) * (Real.log (r n) / n)) =
      Real.log (r n) * ((α - 1) / α) := by field_simp
  have hexp : (n : ℝ) * Real.log (partition p α) / α +
      Real.log (r n) * ((α - 1) / α) ≤
        -(n : ℝ) * (dualObjective p c α - η) := by
    rw [mul_add, hcancel] at hprod
    convert hprod.le using 1 <;> ring
  exact (hu n).trans (by
    rw [holder_moment_eq_exp _ (partition_pos_of_normalized p hp hs α) n _ (hr n)]
    exact Real.exp_le_exp.mpr hexp)

/-- The physical iid Holder/Renyi bound, with the actual tensor spectral
moments derived as powers of the one-copy spectral moment. -/
theorem kraus_tensor_holder_bound (X : Matrix (a × b) (a × b) ℂ)
    (hX : APPT.Quantum.IsDensity X) (k : ℕ)
    (A : κ → Matrix (d × d) ((Fin k → a) × (Fin k → b)) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup ((Fin k → a) × (Fin k → b)) ℂ)
    (α : ℝ) (hαlo : 1 < α) (hαhi : α ≤ 2) :
    (Extraction.bellProjector (d := d) * Extraction.krausApply A
      ((U : Matrix _ _ ℂ) * bipartiteTensor X k * (U : Matrix _ _ ℂ)ᴴ)).trace.re ≤
      ((partition hX.1.isHermitian.eigenvalues α) ^ k) ^ (1 / α) *
        ((Fintype.card (Fin k → a) * Fintype.card (Fin k → b) : ℝ) /
          (Fintype.card d : ℝ)^2) ^ ((α - 1) / α) := by
  let e := bipartiteWordEquiv (a := a) (b := b) k
  let p := hX.1.isHermitian.eigenvalues
  let q := iidLaw p k ∘ e
  let V := reindexUnitary e (tensorUnitary hX.1.isHermitian.eigenvectorUnitary k)
  have hsp : (U : Matrix _ _ ℂ) * bipartiteTensor X k * (U : Matrix _ _ ℂ)ᴴ =
      ((U * V : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        Matrix.diagonal (fun w => (q w : ℂ)) *
      ((U * V : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)ᴴ := by
    rw [bipartiteTensor_spectral X hX.1.isHermitian k]
    simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rfl
  rw [Extraction.target_overlap_eq, hsp]
  have hM := Extraction.targetEffect_rains A hcomplete hpt
  have h := diagonalized_effect_holder_bound q
    (fun w => iidLaw_nonneg p (fun i => hX.1.eigenvalues_nonneg i) k (e w))
    (U * V) (Extraction.targetEffect A) hM.1 1 (by norm_num)
    (by simpa only [one_smul] using hM.2.1) _ α
    (Extraction.rainsEffect_trace_square_le _ _ hM) hαlo hαhi
  have hpart : partition q α = (partition p α) ^ k :=
    (partition_reindex (iidLaw p k) e α).trans (iidLaw_partition p
      (fun i => hX.1.eigenvalues_nonneg i) k α)
  rw [hpart] at h
  simpa only [one_pow, div_one, one_mul] using h

variable {d' ν : ℕ → Type*} [∀ n, Fintype (d' n)] [∀ n, DecidableEq (d' n)]
  [∀ n, Nonempty (d' n)] [∀ n, Fintype (ν n)] [Nonempty a] [Nonempty b]

/-- A proved exponential converse for the original density and actual
physical channel sequence, expressed through one-copy Renyi moments. -/
theorem kraus_tensor_exponential_converse
    (X : Matrix (a × b) (a × b) ℂ) (hX : APPT.Quantum.IsDensity X)
    (A : (n : ℕ) → ν n → Matrix (d' n × d' n) ((Fin n → a) × (Fin n → b)) ℂ)
    (hcomplete : ∀ n, ∑ j, (A n j)ᴴ * A n j = 1)
    (hpt : ∀ n, Extraction.PTConjugatePositive (A n))
    (U : (n : ℕ) → Matrix.unitaryGroup ((Fin n → a) × (Fin n → b)) ℂ)
    (R α : ℝ) (hαlo : 1 < α) (hαhi : α ≤ 2)
    (hR : Tendsto (fun n : ℕ => Real.log (Fintype.card (d' n)) / n) atTop (𝓝 R))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, tensorFidelity X n (A n) (U n) ≤
      Real.exp (-(n : ℝ) *
        (dualObjective hX.1.isHermitian.eigenvalues
          (Real.log (Fintype.card a) + Real.log (Fintype.card b) - 2 * R) α - η)) := by
  apply holder_bound_eventually_exponential hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX)
    (fun n => tensorFidelity X n (A n) (U n))
    (fun n => (Fintype.card (Fin n → a) * Fintype.card (Fin n → b) : ℝ) /
      (Fintype.card (d' n) : ℝ)^2) (fun n => by positivity)
    _ α _ (tensor_budget_rate_limit R hR) η hη
  intro n
  exact kraus_tensor_holder_bound X hX n (A n) (hcomplete n) (hpt n) (U n) α hαlo hαhi

/-- The endpoint alpha=1 is supplied by the trace-preserving effect cap,
including density matrices of non-full rank. -/
theorem tensorFidelity_le_one
    (X : Matrix (a × b) (a × b) ℂ) (hX : APPT.Quantum.IsDensity X) (n : ℕ)
    (A : ν n → Matrix (d' n × d' n) ((Fin n → a) × (Fin n → b)) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup ((Fin n → a) × (Fin n → b)) ℂ) :
    tensorFidelity X n A U ≤ 1 := by
  apply Extraction.kraus_target_overlap_le_one A hcomplete hpt
  have hT := bipartiteTensor_density X hX n
  refine ⟨hT.1.mul_mul_conjTranspose_same _, ?_⟩
  have hU : (U : Matrix ((Fin n → a) × (Fin n → b)) ((Fin n → a) × (Fin n → b)) ℂ)ᴴ *
      (U : Matrix ((Fin n → a) × (Fin n → b)) ((Fin n → a) × (Fin n → b)) ℂ) = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  exact hT.2

end
end ExtractionSpectrum

namespace ExtractionSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The finite scalar variational infimum is attained by a Renyi parameter,
also on the positive support of a singular law. -/
theorem nonnegative_variational_dual_attainment (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (c : ℝ) :
    ∃ α ∈ Set.Icc (1 : ℝ) 2,
      (⨅ q : ProbabilityVector (PositiveSupport p), primalObjective (supportLaw p) c q.1) =
        dualObjective p c α := by
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  obtain ⟨q, α, hq, hqs, hα, he, hmin, _⟩ :=
    escort_variational_certificate (supportLaw p) (fun i => i.2) (supportLaw_sum p hp hs) c
  let q0 : ProbabilityVector (PositiveSupport p) := ⟨q, hq, hqs⟩
  letI : Nonempty (ProbabilityVector (PositiveSupport p)) := ⟨q0⟩
  have hlo : BddBelow (Set.range (fun r : ProbabilityVector (PositiveSupport p) =>
      primalObjective (supportLaw p) c r.1)) := by
    refine ⟨primalObjective (supportLaw p) c q, ?_⟩
    rintro v ⟨r, rfl⟩
    exact hmin r.1 r.2.1 r.2.2
  have hInf : (⨅ r : ProbabilityVector (PositiveSupport p),
      primalObjective (supportLaw p) c r.1) = primalObjective (supportLaw p) c q :=
    le_antisymm (ciInf_le hlo q0) (le_ciInf fun r => hmin r.1 r.2.1 r.2.2)
  have hαp : 0 < α := lt_of_lt_of_le zero_lt_one hα.1
  have hpart : partition (supportLaw p) α = partition p α :=
    positiveSupport_sum p hp (fun x => x ^ α) (Real.zero_rpow (ne_of_gt hαp))
  refine ⟨α, hα, ?_⟩
  rw [hInf, he]
  unfold dualObjective
  rw [hpart]

/-- Optimizing the physical Holder converse gives the full variational
exponent as a one-sided operational bound, with no logarithm of zero fidelity. -/
theorem holder_variational_eventually_exponential (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (F r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hF : ∀ n, F n ≤ 1)
    (hu : ∀ α : ℝ, 1 < α → α ≤ 2 → ∀ n,
      F n ≤ ((partition p α) ^ n) ^ (1 / α) * (r n) ^ ((α - 1) / α))
    (c : ℝ) (hrate : Tendsto (fun n : ℕ => Real.log (r n) / n) atTop (𝓝 c))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, F n ≤ Real.exp (-(n : ℝ) *
      ((⨅ q : ProbabilityVector (PositiveSupport p),
        primalObjective (supportLaw p) c q.1) - η)) := by
  obtain ⟨α, hα, hE⟩ := nonnegative_variational_dual_attainment p hp hs c
  rw [hE]
  by_cases h1 : α = 1
  · rw [h1, dualObjective_one p hs c]
    apply Eventually.of_forall
    intro n
    exact (hF n).trans (Real.one_le_exp_iff.mpr (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [mul_nonneg hn hη.le]))
  · exact holder_bound_eventually_exponential p hp hs F r hr c α
      (hu α (lt_of_le_of_ne hα.1 (Ne.symm h1)) hα.2) hrate η hη

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
  [Nonempty a] [Nonempty b]
  {d ν : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
  [∀ n, Nonempty (d n)] [∀ n, Fintype (ν n)]

/-- The variational fidelity-exponent converse for actual iid complex
density matrices, arbitrary global preprocessing unitaries, and complete
transpose-conjugate-positive Kraus channels. Every spectral and moment bridge
and the optimizing parameter are internally proved. This is a one-sided
operational theorem; no matching-achievability conclusion is asserted. -/
theorem kraus_tensor_variational_exponential_converse
    (X : Matrix (a × b) (a × b) ℂ) (hX : APPT.Quantum.IsDensity X)
    (A : (n : ℕ) → ν n → Matrix (d n × d n) ((Fin n → a) × (Fin n → b)) ℂ)
    (hcomplete : ∀ n, ∑ j, (A n j)ᴴ * A n j = 1)
    (hpt : ∀ n, Extraction.PTConjugatePositive (A n))
    (U : (n : ℕ) → Matrix.unitaryGroup ((Fin n → a) × (Fin n → b)) ℂ)
    (R : ℝ)
    (hR : Tendsto (fun n : ℕ => Real.log (Fintype.card (d n)) / n) atTop (𝓝 R))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, tensorFidelity X n (A n) (U n) ≤ Real.exp (-(n : ℝ) *
      ((⨅ q : ProbabilityVector (PositiveSupport hX.1.isHermitian.eigenvalues),
        divergence q.1 (supportLaw hX.1.isHermitian.eigenvalues) +
          max 0 (entropy q.1 -
            (Real.log (Fintype.card a) + Real.log (Fintype.card b) - 2 * R)) / 2) - η)) := by
  exact holder_variational_eventually_exponential hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX)
    (fun n => tensorFidelity X n (A n) (U n))
    (fun n => (Fintype.card (Fin n → a) * Fintype.card (Fin n → b) : ℝ) /
      (Fintype.card (d n) : ℝ)^2) (fun n => by positivity)
    (fun n => tensorFidelity_le_one X hX n (A n) (hcomplete n) (hpt n) (U n))
    (fun α hαlo hαhi n => kraus_tensor_holder_bound X hX n (A n)
      (hcomplete n) (hpt n) (U n) α hαlo hαhi)
    _ (tensor_budget_rate_limit R hR) η hη

end
end ExtractionSpectrum
