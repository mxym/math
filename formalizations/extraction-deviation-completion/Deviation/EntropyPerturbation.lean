import Deviation.PrefixTail

open scoped BigOperators Topology
open Set Filter ExtractionSpectrum

namespace ExtractionDeviation
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixture (q u : ι → ℝ) (t : ℝ) (i : ι) : ℝ := (1-t)*q i+t*u i

theorem mixture_nonneg (q u : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hu : ∀ i, 0 ≤ u i)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (i : ι) : 0 ≤ mixture q u t i :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hq i)) (mul_nonneg ht.1 (hu i))

theorem mixture_sum (q u : ι → ℝ) (hq : ∑ i, q i = 1) (hu : ∑ i, u i = 1) (t : ℝ) :
    ∑ i, mixture q u t i = 1 := by
  simp only [mixture, Finset.sum_add_distrib, ← Finset.mul_sum, hq, hu, mul_one]
  ring

theorem entropy_eq_sum_negMulLog (q : ι → ℝ) : entropy q = ∑ i, Real.negMulLog (q i) := by
  unfold entropy finiteMean selfInformation Real.negMulLog
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem entropy_mixture_lower (q u : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hu : ∀ i, 0 ≤ u i)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (1-t)*entropy q+t*entropy u ≤ entropy (mixture q u t) := by
  simp only [entropy_eq_sum_negMulLog, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [smul_eq_mul, mixture] using
    Real.concaveOn_negMulLog.2 (hq i) (hu i) (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- The finite algebraic divergence expression is continuous even at zero `q`
coordinates. Its physical use below always restricts to the positive support of `p`. -/
theorem divergence_continuous (p : ι → ℝ) : Continuous (fun q : ι → ℝ => divergence q p) := by
  unfold divergence
  simp_rw [mul_sub]
  apply continuous_finset_sum
  intro i hi
  exact (Real.continuous_mul_log.comp (continuous_apply i)).sub
    ((show Continuous (fun q : ι → ℝ => q i) from continuous_apply i).mul_const (Real.log (p i)))

theorem mixture_divergence_continuous (q u p : ι → ℝ) :
    Continuous (fun t : ℝ => divergence (mixture q u t) p) := by
  apply (divergence_continuous p).comp
  apply continuous_pi
  intro i
  unfold mixture
  fun_prop

/-- Strictly raise a law's entropy toward any higher-entropy law while changing
its divergence by arbitrarily little. This supplies the missing strict side of
the reliability variational boundary without a differentiability assumption. -/
theorem exists_mixture_entropy_gt (q u p : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hqs : ∑ i, q i = 1)
    (hu : ∀ i, 0 ≤ u i) (hus : ∑ i, u i = 1)
    (c : ℝ) (hqH : entropy q = c) (huH : c < entropy u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ι → ℝ, (∀ i, 0 ≤ r i) ∧ (∑ i, r i = 1) ∧ c < entropy r ∧
      divergence r p < divergence q p+ε := by
  have hzero : mixture q u 0 = q := by ext i; simp [mixture]
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, divergence (mixture q u t) p < divergence q p+ε := by
    have h := (mixture_divergence_continuous q u p).continuousAt (x := 0)
    have hbound : divergence (mixture q u 0) p < divergence q p+ε := by rw [hzero]; linarith
    exact h.eventually (Iio_mem_nhds hbound)
  obtain ⟨δ,hδ,hδall⟩ := Metric.eventually_nhds_iff.mp hevent
  let t := min δ 1/2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by have h := min_le_left δ 1; dsimp [t]; linarith
  have ht1 : t < 1 := by have h := min_le_right δ 1; dsimp [t]; linarith
  have hD : divergence (mixture q u t) p < divergence q p+ε :=
    hδall (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using htδ)
  have hH := entropy_mixture_lower q u hq hu t ⟨ht.le,ht1.le⟩
  rw [hqH] at hH
  refine ⟨mixture q u t,mixture_nonneg q u hq hu t ⟨ht.le,ht1.le⟩,
    mixture_sum q u hqs hus t,?_,hD⟩
  nlinarith [mul_pos ht (sub_pos.mpr huH)]

/-- Extend a law on the positive support by exact zeros on the original alphabet. -/
def extendSupport (p : ι → ℝ) (q : PositiveSupport p → ℝ) (i : ι) : ℝ :=
  if h : 0 < p i then q ⟨i,h⟩ else 0

theorem extendSupport_sum_comp (p : ι → ℝ) (q : PositiveSupport p → ℝ)
    (f : ι → ℝ → ℝ) (hzero : ∀ i, f i 0 = 0) :
    (∑ i, f i (extendSupport p q i)) = ∑ j : PositiveSupport p, f j (q j) := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < p i)
    (fun i => f i (extendSupport p q i))
  have hpos : (∑ j : PositiveSupport p, f j (extendSupport p q j)) =
      ∑ j : PositiveSupport p, f j (q j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [extendSupport, dif_pos j.2]
  have hneg : (∑ j : {i // ¬ 0 < p i}, f j (extendSupport p q j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [extendSupport, dif_neg j.2, hzero]
  rw [hpos,hneg,add_zero] at h
  exact h.symm

theorem extendSupport_nonneg (p : ι → ℝ) (q : PositiveSupport p → ℝ)
    (hq : ∀ i, 0 ≤ q i) (i : ι) : 0 ≤ extendSupport p q i := by
  unfold extendSupport
  split_ifs
  · exact hq _
  · exact le_rfl

theorem extendSupport_sum (p : ι → ℝ) (q : PositiveSupport p → ℝ) :
    ∑ i, extendSupport p q i = ∑ j, q j :=
  extendSupport_sum_comp p q (fun _ x => x) (fun _ => rfl)

theorem extendSupport_entropy (p : ι → ℝ) (q : PositiveSupport p → ℝ) :
    entropy (extendSupport p q) = entropy q := by
  unfold entropy finiteMean selfInformation
  exact extendSupport_sum_comp p q (fun _ x => x*(-Real.log x)) (fun _ => by simp)

theorem extendSupport_divergence (p : ι → ℝ) (q : PositiveSupport p → ℝ) :
    divergence (extendSupport p q) p = divergence q (supportLaw p) := by
  unfold divergence
  exact extendSupport_sum_comp p q (fun i x => x*(Real.log x-Real.log (p i))) (fun _ => by simp)

theorem extendSupport_support (p : ι → ℝ) (q : PositiveSupport p → ℝ) (i : ι)
    (hi : 0 < extendSupport p q i) : 0 < p i := by
  by_contra hn
  simp only [extendSupport, dif_neg hn] at hi
  exact (lt_irrefl 0) hi

def strictDirectExponent (p : ι → ℝ) (c : ℝ) : ℝ :=
  ⨅ q : {q : ProbabilityVector (PositiveSupport p) // c ≤ entropy q.1},
    divergence q.1.1 (supportLaw p)

variable [Nonempty ι]

/-- The constrained entropy infimum can be approached from the strict
`H(q)>c` side, on the original alphabet and preserving all zero probabilities. -/
theorem strictDirectExponent_approx_above (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (c : ℝ) (hlo : entropy p < c)
    (hhi : c < Real.log (Fintype.card (PositiveSupport p))) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      (∀ i, 0 < q i → 0 < p i) ∧ c < entropy q ∧
      divergence q p < strictDirectExponent p c+ε := by
  letI : Nonempty (PositiveSupport p) := positiveSupport_nonempty p hp hs
  let s := supportLaw p
  have hsH : entropy s < c := by rw [supportLaw_entropy p hp]; exact hlo
  obtain ⟨q,α,hq,hqs,hH,hα,he,hmin,hmax⟩ :=
    strict_direct_variational_certificate s (fun i => i.2) (supportLaw_sum p hp hs) c hsH hhi
  let q0 : {r : ProbabilityVector (PositiveSupport p) // c ≤ entropy r.1} :=
    ⟨⟨q,hq,hqs⟩,hH.ge⟩
  letI : Nonempty {r : ProbabilityVector (PositiveSupport p) // c ≤ entropy r.1} := ⟨q0⟩
  have hbd : BddBelow (Set.range (fun r :
      {r : ProbabilityVector (PositiveSupport p) // c ≤ entropy r.1} => divergence r.1.1 s)) := by
    refine ⟨divergence q s,?_⟩
    rintro v ⟨r,rfl⟩
    exact hmin r.1.1 r.1.2.1 r.1.2.2 r.2
  have hInf : strictDirectExponent p c = divergence q s :=
    le_antisymm (ciInf_le hbd q0)
      (le_ciInf (fun r => hmin r.1.1 r.1.2.1 r.1.2.2 r.2))
  let u := escort s 0
  have hu : ∀ i, 0 ≤ u i := fun i => (escort_pos s (fun i => i.2) 0 i).le
  have hus : ∑ i, u i = 1 := escort_sum s (fun i => i.2) 0
  have huH : c < entropy u := by rw [escort_zero_entropy]; exact hhi
  obtain ⟨r,hr,hrs,hrH,hrD⟩ := exists_mixture_entropy_gt q u s hq hqs hu hus c hH huH ε hε
  refine ⟨extendSupport p r,extendSupport_nonneg p r hr,?_,extendSupport_support p r,?_,?_⟩
  · rw [extendSupport_sum,hrs]
  · rw [extendSupport_entropy]
    exact hrH
  · rw [extendSupport_divergence,hInf]
    exact hrD

end
end ExtractionDeviation
