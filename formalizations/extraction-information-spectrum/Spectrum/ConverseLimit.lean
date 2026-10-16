import Spectrum.PhysicalTensor
import Spectrum.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology ComplexOrder Classical
open Matrix

namespace ExtractionSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The finite information-spectrum inequality and the proved finite iid law
imply a strong converse whenever the normalized log budget stays below entropy. -/
theorem information_bound_tendsto_zero (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (F r : ℕ → ℝ) (c : ℝ)
    (hF : ∀ n, 0 ≤ F n)
    (hu : ∀ n t, F n ≤ iidInformationEvent p n (Real.log (r n) + t) + Real.exp (-t / 2))
    (hrate : Tendsto (fun n => Real.log (r n) / n) atTop (𝓝 c))
    (hc : c < entropy p) : Tendsto F atTop (𝓝 0) := by
  let δ := (entropy p - c) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hbelow : c + 2 * δ < entropy p := by dsimp [δ]; linarith
  have hmass := iidInformationEvent_law_of_large_numbers p hp hs (c + 2 * δ)
    (ne_of_lt hbelow)
  simp only [not_lt_of_ge hbelow.le, ite_false] at hmass
  have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) * δ) / 2)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun n : ℕ => (n : ℝ) * (δ / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin using 1 <;>
      ext n <;> congr 1 <;> ring
  have hlimit : Tendsto (fun n : ℕ =>
      iidInformationEvent p n ((n : ℝ) * (c + 2 * δ)) +
        Real.exp (-((n : ℝ) * δ) / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using hmass.add hexp
  apply squeeze_zero' (Eventually.of_forall hF) _ hlimit
  filter_upwards [hrate.eventually_lt_const (show c < c + δ by linarith),
    eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hcut : Real.log (r n) + (n : ℝ) * δ ≤ (n : ℝ) * (c + 2 * δ) := by
    have hh := (div_lt_iff₀ hnR).mp hn
    nlinarith
  exact (hu n ((n : ℝ) * δ)).trans
    (add_le_add (iidInformationEvent_mono p hp n hcut) le_rfl)

/-- The finite physical information-spectrum estimate implies the Gaussian
converse for every admissible moving cutoff and diverging smoothing sequence. -/
theorem information_bound_limsup_gaussian (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < varentropy p)
    (F r t : ℕ → ℝ) (y : ℝ) (hF : ∀ n, 0 ≤ F n)
    (hu : ∀ n s, F n ≤ iidInformationEvent p n (Real.log (r n) + s) + Real.exp (-s / 2))
    (ht : Tendsto t atTop atTop)
    (hcut : Tendsto (fun n : ℕ =>
      (Real.log (r n) + t n - n * entropy p) / Real.sqrt n) atTop (𝓝 y)) :
    Filter.limsup F atTop ≤ (gaussianReal 0 (varentropy p).toNNReal).real (Set.Iic y) := by
  have hmass := iidInformationEvent_gaussian_moving p hp hs hv
    (fun n => Real.log (r n) + t n) y hcut
  have hexp : Tendsto (fun n => Real.exp (-t n / 2)) atTop (𝓝 0) := by
    have hlin := ht.atTop_mul_const (show (0 : ℝ) < 1 / 2 by norm_num)
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin using 1
    ext n
    congr 1
    ring
  have hlimit : Tendsto (fun n : ℕ =>
      iidInformationEvent p n (Real.log (r n) + t n) + Real.exp (-t n / 2)) atTop
      (𝓝 ((gaussianReal 0 (varentropy p).toNNReal).real (Set.Iic y))) := by
    simpa only [add_zero] using hmass.add hexp
  rw [← hlimit.limsup_eq]
  exact limsup_le_limsup (Eventually.of_forall fun n => hu n (t n))
    (isCoboundedUnder_le_of_le atTop hF) hlimit.isBoundedUnder_le

/-- A concrete diverging cutoff that is negligible on the Gaussian scale. -/
def gaussianSmoothing (n : ℕ) : ℝ := Real.sqrt (Real.sqrt n)

theorem gaussianSmoothing_tendsto : Tendsto gaussianSmoothing atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

theorem gaussianSmoothing_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => gaussianSmoothing n / Real.sqrt n) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp gaussianSmoothing_tendsto
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hq : 0 < gaussianSmoothing n := Real.sqrt_pos.mpr hs
  change (gaussianSmoothing n)⁻¹ = gaussianSmoothing n / Real.sqrt n
  rw [inv_eq_one_div]
  apply (div_eq_div_iff (ne_of_gt hq) (ne_of_gt hs)).mpr
  simpa only [gaussianSmoothing, one_mul, ← pow_two] using
    (Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))).symm

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
  [Nonempty a] [Nonempty b]
  {d ν : ℕ → Type*} [∀ n, Fintype (d n)] [∀ n, DecidableEq (d n)]
  [∀ n, Nonempty (d n)] [∀ n, Fintype (ν n)]

/-- Actual output fidelity of a sequence of channels on canonically regrouped
iid copies, retaining the original global-unitary and complete Kraus semantics. -/
def tensorFidelity (X : Matrix (a × b) (a × b) ℂ) (n : ℕ)
    (A : ν n → Matrix (d n × d n) ((Fin n → a) × (Fin n → b)) ℂ)
    (U : Matrix.unitaryGroup ((Fin n → a) × (Fin n → b)) ℂ) : ℝ :=
  (Extraction.bellProjector (d := d n) * Extraction.krausApply A
    ((U : Matrix _ _ ℂ) * bipartiteTensor X n * (U : Matrix _ _ ℂ)ᴴ)).trace.re

theorem tensorFidelity_nonneg (X : Matrix (a × b) (a × b) ℂ)
    (hX : APPT.Quantum.IsDensity X) (n : ℕ)
    (A : ν n → Matrix (d n × d n) ((Fin n → a) × (Fin n → b)) ℂ)
    (U : Matrix.unitaryGroup ((Fin n → a) × (Fin n → b)) ℂ) :
    0 ≤ tensorFidelity X n A U := by
  exact Extraction.positive_product_trace_re _ _
    (Extraction.bellProjector_density (d := d n)).1
    (Extraction.krausApply_posSemidef A _
      ((bipartiteTensor_density X hX n).1.mul_mul_conjTranspose_same _))

/-- The normalized finite-dimensional Rains budget has the required limit
under the ordinary logarithmic Bell-target rate assumption. -/
theorem tensor_budget_rate_limit (R : ℝ)
    (hR : Tendsto (fun n : ℕ => Real.log (Fintype.card (d n)) / n) atTop (𝓝 R)) :
    Tendsto (fun n : ℕ =>
      Real.log ((Fintype.card (Fin n → a) * Fintype.card (Fin n → b) : ℝ) /
        (Fintype.card (d n) : ℝ)^2) / n) atTop
      (𝓝 (Real.log (Fintype.card a) + Real.log (Fintype.card b) - 2 * R)) := by
  have he (n : ℕ) :
      Real.log ((Fintype.card (Fin n → a) * Fintype.card (Fin n → b) : ℝ) /
        (Fintype.card (d n) : ℝ)^2) =
      (n : ℝ) * (Real.log (Fintype.card a) + Real.log (Fintype.card b)) -
        2 * Real.log (Fintype.card (d n)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    ring
  have h : Tendsto (fun n : ℕ =>
      (Real.log (Fintype.card a) + Real.log (Fintype.card b)) -
        2 * (Real.log (Fintype.card (d n)) / n)) atTop
      (𝓝 (Real.log (Fintype.card a) + Real.log (Fintype.card b) - 2 * R)) :=
    tendsto_const_nhds.sub (hR.const_mul 2)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [he]
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp

/-- Entropic strong converse for actual iid quantum channels and all input
global unitaries. The spectral iid law and its weak law are internally proved. -/
theorem kraus_tensor_entropy_strong_converse (X : Matrix (a × b) (a × b) ℂ)
    (hX : APPT.Quantum.IsDensity X)
    (A : (n : ℕ) → ν n → Matrix (d n × d n) ((Fin n → a) × (Fin n → b)) ℂ)
    (hcomplete : ∀ n, ∑ j, (A n j)ᴴ * A n j = 1)
    (hpt : ∀ n, Extraction.PTConjugatePositive (A n))
    (U : (n : ℕ) → Matrix.unitaryGroup ((Fin n → a) × (Fin n → b)) ℂ)
    (c : ℝ)
    (hrate : Tendsto (fun n : ℕ =>
      Real.log ((Fintype.card (Fin n → a) * Fintype.card (Fin n → b) : ℝ) /
        (Fintype.card (d n) : ℝ)^2) / n) atTop (𝓝 c))
    (hc : c < entropy hX.1.isHermitian.eigenvalues) :
    Tendsto (fun n => tensorFidelity X n (A n) (U n)) atTop (𝓝 0) := by
  letI : MeasurableSpace (a × b) := ⊤
  exact information_bound_tendsto_zero hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX)
    (fun n => tensorFidelity X n (A n) (U n))
    (fun n => (Fintype.card (Fin n → a) * Fintype.card (Fin n → b) : ℝ) /
      (Fintype.card (d n) : ℝ)^2) c
    (fun n => tensorFidelity_nonneg X hX n (A n) (U n))
    (fun n t => kraus_tensor_information_bound X hX n (A n) (hcomplete n) (hpt n) (U n) t)
    hrate hc

/-- Operational entropy-limited strong converse in the rate notation of the
paper: every actual channel sequence has fidelity tending to zero when
`R > (log D - H(p))/2`, without assuming a probability limit or spectrum model. -/
theorem kraus_tensor_rate_strong_converse (X : Matrix (a × b) (a × b) ℂ)
    (hX : APPT.Quantum.IsDensity X)
    (A : (n : ℕ) → ν n → Matrix (d n × d n) ((Fin n → a) × (Fin n → b)) ℂ)
    (hcomplete : ∀ n, ∑ j, (A n j)ᴴ * A n j = 1)
    (hpt : ∀ n, Extraction.PTConjugatePositive (A n))
    (U : (n : ℕ) → Matrix.unitaryGroup ((Fin n → a) × (Fin n → b)) ℂ)
    (R : ℝ)
    (hR : Tendsto (fun n : ℕ => Real.log (Fintype.card (d n)) / n) atTop (𝓝 R))
    (habove : (Real.log (Fintype.card a) + Real.log (Fintype.card b) -
      entropy hX.1.isHermitian.eigenvalues) / 2 < R) :
    Tendsto (fun n => tensorFidelity X n (A n) (U n)) atTop (𝓝 0) := by
  exact kraus_tensor_entropy_strong_converse X hX A hcomplete hpt U _
    (tensor_budget_rate_limit R hR) (by linarith)

/-- The Gaussian upper half of the paper's second-order threshold, for the
original complex density, its actual iid tensor powers, physical channels, and
every global preprocessing unitary. The CLT is proved through the finite law. -/
theorem kraus_tensor_gaussian_converse (X : Matrix (a × b) (a × b) ℂ)
    (hX : APPT.Quantum.IsDensity X)
    (A : (n : ℕ) → ν n → Matrix (d n × d n) ((Fin n → a) × (Fin n → b)) ℂ)
    (hcomplete : ∀ n, ∑ j, (A n j)ᴴ * A n j = 1)
    (hpt : ∀ n, Extraction.PTConjugatePositive (A n))
    (U : (n : ℕ) → Matrix.unitaryGroup ((Fin n → a) × (Fin n → b)) ℂ)
    (hv : 0 < varentropy hX.1.isHermitian.eigenvalues) (z : ℝ)
    (hsecond : Tendsto (fun n : ℕ =>
      (Real.log (Fintype.card (d n)) - (n : ℝ) *
        ((Real.log (Fintype.card a) + Real.log (Fintype.card b) -
          entropy hX.1.isHermitian.eigenvalues) / 2)) / Real.sqrt n) atTop (𝓝 z)) :
    Filter.limsup (fun n => tensorFidelity X n (A n) (U n)) atTop ≤
      (gaussianReal 0 (varentropy hX.1.isHermitian.eigenvalues).toNNReal).real
        (Set.Iic (-2 * z)) := by
  letI : MeasurableSpace (a × b) := ⊤
  let r : ℕ → ℝ := fun n =>
    (Fintype.card (Fin n → a) * Fintype.card (Fin n → b) : ℝ) /
      (Fintype.card (d n) : ℝ)^2
  have he (n : ℕ) : Real.log (r n) =
      (n : ℝ) * (Real.log (Fintype.card a) + Real.log (Fintype.card b)) -
        2 * Real.log (Fintype.card (d n)) := by
    simp only [r, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    ring
  have hh := (hsecond.const_mul (-2)).add gaussianSmoothing_div_sqrt_tendsto
  have hcut : Tendsto (fun n : ℕ =>
      (Real.log (r n) + gaussianSmoothing n - n * entropy hX.1.isHermitian.eigenvalues) /
        Real.sqrt n) atTop (𝓝 (-2 * z)) := by
    apply (show Tendsto _ atTop (𝓝 (-2 * z)) from by simpa only [add_zero] using hh).congr'
    filter_upwards with n
    rw [he]
    ring
  exact information_bound_limsup_gaussian hX.1.isHermitian.eigenvalues
    (fun i => hX.1.eigenvalues_nonneg i) (density_eigenvalues_sum X hX) hv
    (fun n => tensorFidelity X n (A n) (U n)) r gaussianSmoothing (-2 * z)
    (fun n => tensorFidelity_nonneg X hX n (A n) (U n))
    (fun n t => kraus_tensor_information_bound X hX n (A n) (hcomplete n) (hpt n) (U n) t)
    gaussianSmoothing_tendsto hcut

end
end ExtractionSpectrum
