import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.NhdsWithin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

-- Source: FiniteMarginals.lean

/-! Actual finite probability laws, signed marginal kernels, and total variation.
The feature matrix is arbitrary; image indicators will instantiate it.
No optimization theorem is assumed. -/

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I]

def Probability (p : I → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

def TV (v : I → ℝ) : ℝ := (∑ i, |v i|) / 2

def Kernel (A : J → I → ℝ) (v : I → ℝ) : Prop :=
  (∑ i, v i = 0) ∧ ∀ j, ∑ i, A j i * v i = 0

def Match (A : J → I → ℝ) (p q : I → ℝ) : Prop :=
  ∀ j, ∑ i, A j i * p i = ∑ i, A j i * q i

theorem tv_nonneg (v : I → ℝ) : 0 ≤ TV v := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem tv_eq_zero_iff (v : I → ℝ) : TV v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hs : ∑ i, |v i| = 0 := by dsimp [TV] at h; linarith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (v i)).mp hs
    funext i
    exact abs_eq_zero.mp (hi i (Finset.mem_univ i))
  · rintro rfl
    simp [TV]

theorem tv_pos (v : I → ℝ) (h : v ≠ 0) : 0 < TV v :=
  lt_of_le_of_ne (tv_nonneg v) (Ne.symm (mt (tv_eq_zero_iff v).mp h))

theorem tv_smul (a : ℝ) (v : I → ℝ) :
    TV (fun i => a * v i) = |a| * TV v := by
  simp only [TV, abs_mul, ← Finset.mul_sum]
  ring

theorem tv_neg (v : I → ℝ) : TV (fun i => -v i) = TV v := by
  simp [TV]

theorem kernel_of_match (A : J → I → ℝ) (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q) (hm : Match A p q) :
    Kernel A (fun i => p i - q i) := by
  constructor
  · simp only [Finset.sum_sub_distrib, hp.2, hq.2, sub_self]
  · intro j
    simp only [mul_sub, Finset.sum_sub_distrib, hm j, sub_self]

theorem tv_probability_difference_le_one (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q) :
    TV (fun i => p i - q i) ≤ 1 := by
  have hs : ∑ i, |p i - q i| ≤ ∑ i, (p i + q i) := by
    apply Finset.sum_le_sum
    intro i _
    calc
      |p i - q i| ≤ |p i| + |q i| := abs_sub _ _
      _ = p i + q i := by rw [abs_of_nonneg (hp.1 i), abs_of_nonneg (hq.1 i)]
  simp only [Finset.sum_add_distrib, hp.2, hq.2] at hs
  dsimp [TV]
  linarith

def posPart (v : I → ℝ) (i : I) : ℝ := max (v i) 0
def negPart (v : I → ℝ) (i : I) : ℝ := max (-v i) 0

omit [Fintype I] in
theorem part_difference (v : I → ℝ) (i : I) :
    posPart v i - negPart v i = v i := by
  dsimp [posPart, negPart]
  by_cases h : 0 ≤ v i
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

omit [Fintype I] in
theorem part_sum (v : I → ℝ) (i : I) :
    posPart v i + negPart v i = |v i| := by
  dsimp [posPart, negPart]
  by_cases h : 0 ≤ v i
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith),
      abs_of_neg (lt_of_not_ge h)]
    ring

theorem part_masses (v : I → ℝ) (h : ∑ i, v i = 0) :
    (∑ i, posPart v i) = TV v ∧ (∑ i, negPart v i) = TV v := by
  have hd : (∑ i, posPart v i) - (∑ i, negPart v i) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [part_difference] using h
  have hs : (∑ i, posPart v i) + (∑ i, negPart v i) = ∑ i, |v i| := by
    rw [← Finset.sum_add_distrib]
    simp only [part_sum]
  dsimp [TV]
  constructor <;> linarith

def jordanP (v : I → ℝ) (i : I) : ℝ := posPart v i / TV v
def jordanQ (v : I → ℝ) (i : I) : ℝ := negPart v i / TV v

theorem jordan_probabilities (A : J → I → ℝ) (v : I → ℝ)
    (hv : Kernel A v) (hne : v ≠ 0) :
    Probability (jordanP v) ∧ Probability (jordanQ v) := by
  have hd := tv_pos v hne
  have hm := part_masses v hv.1
  constructor
  · constructor
    · intro i
      exact div_nonneg (le_max_right _ _) hd.le
    · simp only [jordanP, ← Finset.sum_div, hm.1, div_self hd.ne']
  · constructor
    · intro i
      exact div_nonneg (le_max_right _ _) hd.le
    · simp only [jordanQ, ← Finset.sum_div, hm.2, div_self hd.ne']

theorem jordan_difference (v : I → ℝ) (i : I) :
    jordanP v i - jordanQ v i = v i / TV v := by
  dsimp [jordanP, jordanQ]
  rw [← sub_div, part_difference]

theorem jordan_match (A : J → I → ℝ) (v : I → ℝ)
    (hv : Kernel A v) : Match A (jordanP v) (jordanQ v) := by
  intro j
  apply sub_eq_zero.mp
  calc
    (∑ i, A j i * jordanP v i) - (∑ i, A j i * jordanQ v i) =
        ∑ i, A j i * (jordanP v i - jordanQ v i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ i, A j i * v i) / TV v := by
      simp only [jordan_difference, mul_div_assoc, Finset.sum_div]
    _ = 0 := by rw [hv.2 j, zero_div]

theorem jordan_disjoint (v : I → ℝ) (i : I) :
    jordanP v i = 0 ∨ jordanQ v i = 0 := by
  by_cases h : 0 ≤ v i
  · right
    simp [jordanQ, negPart, max_eq_right (show -v i ≤ 0 by linarith)]
  · left
    simp [jordanP, posPart, max_eq_right (le_of_not_ge h)]

theorem jordan_tv_one (v : I → ℝ) (hne : v ≠ 0) :
    TV (fun i => jordanP v i - jordanQ v i) = 1 := by
  have hd := tv_pos v hne
  simp_rw [jordan_difference, div_eq_mul_inv, mul_comm (v _) (TV v)⁻¹]
  rw [tv_smul, abs_of_pos (inv_pos.mpr hd), inv_mul_cancel₀ hd.ne']

end
end OrbitalMarginals

-- Source: SharpResponse.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I]

def SignedBound (A : J → I → ℝ) (i : I) (C : ℝ) : Prop :=
  ∀ v, Kernel A v → |v i| ≤ C * TV v

def PairBound (A : J → I → ℝ) (i : I) (C : ℝ) : Prop :=
  ∀ p q, Probability p → Probability q → Match A p q → p i - q i ≤ C

theorem signedBound_iff_pairBound (A : J → I → ℝ) (i : I) (C : ℝ)
    (hC : 0 ≤ C) : SignedBound A i C ↔ PairBound A i C := by
  constructor
  · intro h p q hp hq hm
    calc
      p i - q i ≤ |p i - q i| := le_abs_self _
      _ ≤ C * TV (fun j => p j - q j) := h _ (kernel_of_match A p q hp hq hm)
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (tv_probability_difference_le_one p q hp hq) hC
      _ = C := mul_one _
  · intro h v hv
    by_cases hz : v = 0
    · subst v
      simp [TV]
    have hd := tv_pos v hz
    have hpq := jordan_probabilities A v hv hz
    have hm := jordan_match A v hv
    have hpos := h (jordanP v) (jordanQ v) hpq.1 hpq.2 hm
    have hneg := h (jordanQ v) (jordanP v) hpq.2 hpq.1 (fun j => (hm j).symm)
    rw [jordan_difference] at hpos
    have hneg' : -(v i / TV v) ≤ C := by
      rw [← jordan_difference v i]
      linarith
    have hab : |v i / TV v| ≤ C := abs_le.mpr ⟨by linarith, hpos⟩
    rwa [abs_div, abs_of_pos hd, div_le_iff₀ hd] at hab

variable [Nonempty I]

def uniform (_i : I) : ℝ := (Fintype.card I : ℝ)⁻¹

theorem uniform_pos (i : I) : 0 < uniform i := by
  dsimp [uniform]
  exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem uniform_probability : Probability (uniform : I → ℝ) := by
  constructor
  · intro i
    exact (uniform_pos i).le
  · simp only [uniform, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

def UniformLawBound (A : J → I → ℝ) (i : I) (C : ℝ) : Prop :=
  ∀ p, Probability p → Match A p uniform →
    |p i - uniform i| ≤ C * TV (fun j => p j - uniform j)

theorem kernel_small_perturbation (A : J → I → ℝ) (v : I → ℝ)
    (hv : Kernel A v) :
    ∃ ε : ℝ, 0 < ε ∧ Probability (fun i => uniform i + ε * v i) ∧
      Match A (fun i => uniform i + ε * v i) uniform := by
  classical
  let S : ℝ := ∑ i, |v i|
  let a : ℝ := (Fintype.card I : ℝ)⁻¹
  let ε : ℝ := a / (1 + S)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha : 0 < a := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hden : 0 < 1 + S := by linarith
  have hε : 0 < ε := div_pos ha hden
  have hid : ε * (1 + S) = a := by
    dsimp [ε]
    exact div_mul_cancel₀ _ hden.ne'
  refine ⟨ε, hε, ⟨?_, ?_⟩, ?_⟩
  · intro i
    have hab : |v i| ≤ S := Finset.single_le_sum
      (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)
    have hl : -S ≤ v i := by linarith [neg_abs_le (v i)]
    have hmul := mul_le_mul_of_nonneg_left hl hε.le
    change 0 ≤ a + ε * v i
    nlinarith
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hv.1, mul_zero, add_zero]
    exact uniform_probability.2
  · intro j
    simp only [mul_add, mul_left_comm (A j _) ε, Finset.sum_add_distrib,
      ← Finset.mul_sum, hv.2 j, mul_zero, add_zero]

theorem uniformLawBound_iff_signedBound (A : J → I → ℝ) (i : I) (C : ℝ) :
    UniformLawBound A i C ↔ SignedBound A i C := by
  constructor
  · intro h v hv
    obtain ⟨ε, hε, hp, hm⟩ := kernel_small_perturbation A v hv
    have hb := h _ hp hm
    simp only [add_sub_cancel_left] at hb
    rw [abs_mul, abs_of_pos hε, tv_smul, abs_of_pos hε] at hb
    have : ε * |v i| ≤ ε * (C * TV v) := by nlinarith [hb]
    exact le_of_mul_le_mul_left this hε
  · intro h p hp hm
    exact h _ (kernel_of_match A p uniform hp uniform_probability hm)

theorem uniformLawBound_iff_pairBound (A : J → I → ℝ) (i : I) (C : ℝ)
    (hC : 0 ≤ C) : UniformLawBound A i C ↔ PairBound A i C :=
  (uniformLawBound_iff_signedBound A i C).trans (signedBound_iff_pairBound A i C hC)

end
end OrbitalMarginals

-- Source: Attainment.lean

open scoped BigOperators
open Set

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I]

theorem isClosed_probability : IsClosed {p : I → ℝ | Probability p} := by
  have hnonneg : IsClosed {p : I → ℝ | ∀ i, 0 ≤ p i} := by
    have h := isClosed_iInter (fun i : I =>
      isClosed_le (continuous_const : Continuous (fun _ : I → ℝ => (0 : ℝ)))
        (continuous_apply i))
    convert h using 1
    ext p
    simp
  have hsum : IsClosed {p : I → ℝ | ∑ i, p i = 1} := by
    apply isClosed_eq
    · fun_prop
    · fun_prop
  exact hnonneg.inter hsum

theorem probability_subset_cube : {p : I → ℝ | Probability p} ⊆
    Icc (0 : I → ℝ) 1 := by
  intro p hp
  constructor
  · exact hp.1
  · intro i
    calc
      p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
      _ = 1 := hp.2

theorem isCompact_probability : IsCompact {p : I → ℝ | Probability p} :=
  (isCompact_Icc : IsCompact (Icc (0 : I → ℝ) 1)).of_isClosed_subset
    isClosed_probability probability_subset_cube

def feasiblePairs (A : J → I → ℝ) : Set ((I → ℝ) × (I → ℝ)) :=
  {pq | Probability pq.1 ∧ Probability pq.2 ∧ Match A pq.1 pq.2}

theorem isClosed_feasiblePairs (A : J → I → ℝ) : IsClosed (feasiblePairs A) := by
  have hp := isClosed_probability.preimage
    (continuous_fst : Continuous (fun pq : (I → ℝ) × (I → ℝ) => pq.1))
  have hq := isClosed_probability.preimage
    (continuous_snd : Continuous (fun pq : (I → ℝ) × (I → ℝ) => pq.2))
  have hm : IsClosed {pq : (I → ℝ) × (I → ℝ) | Match A pq.1 pq.2} := by
    have h := isClosed_iInter fun j : J =>
      isClosed_eq
        (show Continuous (fun pq : (I → ℝ) × (I → ℝ) => ∑ i, A j i * pq.1 i) by
          fun_prop)
        (show Continuous (fun pq : (I → ℝ) × (I → ℝ) => ∑ i, A j i * pq.2 i) by
          fun_prop)
    convert h using 1
    ext pq
    simp [Match]
  exact hp.inter (hq.inter hm)

theorem isCompact_feasiblePairs (A : J → I → ℝ) : IsCompact (feasiblePairs A) := by
  exact (isCompact_probability.prod isCompact_probability).of_isClosed_subset
    (isClosed_feasiblePairs A) (fun _ h => ⟨h.1, h.2.1⟩)

variable [Nonempty I]

theorem feasiblePairs_nonempty (A : J → I → ℝ) : (feasiblePairs A).Nonempty :=
  ⟨(uniform, uniform), uniform_probability, uniform_probability, fun _ => rfl⟩

theorem exists_optimal_pair (A : J → I → ℝ) (i : I) :
    ∃ p q : I → ℝ, Probability p ∧ Probability q ∧ Match A p q ∧
      0 ≤ p i - q i ∧ PairBound A i (p i - q i) := by
  obtain ⟨pq, hpq, hmax⟩ := (isCompact_feasiblePairs A).exists_isMaxOn
    (feasiblePairs_nonempty A)
    (show Continuous (fun pq : (I → ℝ) × (I → ℝ) => pq.1 i - pq.2 i) by
      fun_prop).continuousOn
  refine ⟨pq.1, pq.2, hpq.1, hpq.2.1, hpq.2.2, ?_, ?_⟩
  · have h0 := hmax (show (uniform, uniform) ∈ feasiblePairs A from
      ⟨uniform_probability, uniform_probability, fun _ => rfl⟩)
    change uniform i - uniform i ≤ pq.1 i - pq.2 i at h0
    simpa only [sub_self] using h0
  · intro p q hp hq hm
    exact hmax (show (p, q) ∈ feasiblePairs A from ⟨hp, hq, hm⟩)

theorem exists_sharp_uniform_response (A : J → I → ℝ) (i : I) :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ 1 ∧ UniformLawBound A i C ∧
      ∀ D : ℝ, 0 ≤ D → UniformLawBound A i D → C ≤ D := by
  obtain ⟨p, q, hp, hq, hm, hC, hbound⟩ := exists_optimal_pair A i
  refine ⟨p i - q i, hC, ?_,
    (uniformLawBound_iff_pairBound A i _ hC).mpr hbound, ?_⟩
  · have hpi : p i ≤ 1 := (probability_subset_cube hp).2 i
    linarith [hq.1 i]
  · intro D hD hb
    exact (uniformLawBound_iff_pairBound A i D hD).mp hb p q hp hq hm

end
end OrbitalMarginals

-- Source: Duality.lean

open scoped BigOperators
open Set

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I] [Fintype J]

def dualScore (A : J → I → ℝ) (i : I) (coeff : J → ℝ) (g : I) : ℝ := by
  classical
  exact (if g = i then 1 else 0) - ∑ j, coeff j * A j g

def IntervalDual (A : J → I → ℝ) (i : I) (C : ℝ) : Prop :=
  ∃ coeff : J → ℝ, ∃ a b : ℝ,
    (∀ g, a ≤ dualScore A i coeff g ∧ dualScore A i coeff g ≤ b) ∧ b - a ≤ C

theorem score_expectation (A : J → I → ℝ) (i : I) (coeff : J → ℝ) (p : I → ℝ) :
    (∑ g, p g * dualScore A i coeff g) = p i - ∑ j, coeff j * (∑ g, A j g * p g) := by
  classical
  simp only [dualScore, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · simp
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro g _
    ring

theorem intervalDual_pairBound (A : J → I → ℝ) (i : I) (C : ℝ)
    (hd : IntervalDual A i C) : PairBound A i C := by
  obtain ⟨coeff, a, b, hrange, hwidth⟩ := hd
  intro p q hp hq hm
  change ∀ j, (∑ g, A j g * p g) = ∑ g, A j g * q g at hm
  have hupper : (∑ g, p g * dualScore A i coeff g) ≤ b := by
    calc
      (∑ g, p g * dualScore A i coeff g) ≤ ∑ g, p g * b :=
        Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hrange g).2 (hp.1 g)
      _ = b := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hlower : a ≤ ∑ g, q g * dualScore A i coeff g := by
    calc
      a = ∑ g, q g * a := by rw [← Finset.sum_mul, hq.2, one_mul]
      _ ≤ ∑ g, q g * dualScore A i coeff g :=
        Finset.sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hrange g).1 (hq.1 g)
  have hdiff : (∑ g, p g * dualScore A i coeff g) -
      (∑ g, q g * dualScore A i coeff g) = p i - q i := by
    rw [score_expectation, score_expectation]
    simp_rw [hm]
    ring
  linarith

abbrev L1Vector (I : Type*) := PiLp 1 (fun _ : I => ℝ)

def constraintMap (A : J → I → ℝ) : L1Vector I →ₗ[ℝ] (Option J → ℝ) where
  toFun v j := match j with
    | none => ∑ i, v i
    | some j => ∑ i, A j i * v i
  map_add' x y := by
    funext j
    cases j <;> simp [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext j
    cases j <;> simp [PiLp.smul_apply, Finset.mul_sum, mul_left_comm]

omit [Nonempty I] [Fintype J] in
theorem mem_constraint_kernel (A : J → I → ℝ) (x : L1Vector I) :
    x ∈ LinearMap.ker (constraintMap A) ↔ Kernel A (WithLp.ofLp x) := by
  constructor
  · intro h
    have hh := LinearMap.mem_ker.mp h
    exact ⟨congrFun hh none, fun j => congrFun hh (some j)⟩
  · intro h
    apply LinearMap.mem_ker.mpr
    funext j
    cases j with
    | none => exact h.1
    | some j => exact h.2 j

def kernelCoordinate (A : J → I → ℝ) (i : I) :
    LinearMap.ker (constraintMap A) →L[ℝ] ℝ :=
  ((PiLp.projₗ 1 (𝕜 := ℝ) (fun _ : I => ℝ) i).comp (LinearMap.ker (constraintMap A)).subtype).toContinuousLinearMap

omit [Nonempty I] in
theorem l1_norm (x : L1Vector I) : ‖x‖ = 2 * TV (WithLp.ofLp x) := by
  rw [PiLp.norm_eq_of_L1]
  simp only [Real.norm_eq_abs, TV]
  ring

omit [Nonempty I] [Fintype J] in
theorem coordinate_norm_is_sharp (A : J → I → ℝ) (i : I) (C : ℝ)
    (hC : 0 ≤ C) (hb : SignedBound A i C)
    (hminimal : ∀ D : ℝ, 0 ≤ D → SignedBound A i D → C ≤ D) :
    2 * ‖kernelCoordinate A i‖ = C := by
  let f := kernelCoordinate A i
  have hn : ‖f‖ ≤ C / 2 := by
    apply f.opNorm_le_bound (by positivity)
    intro x
    have hh := hb (WithLp.ofLp x.1) ((mem_constraint_kernel A x.1).mp x.2)
    change |x.1 i| ≤ C / 2 * ‖x.1‖
    rw [l1_norm]
    nlinarith [hh]
  have hbound : SignedBound A i (2 * ‖f‖) := by
    intro v hv
    let x : LinearMap.ker (constraintMap A) :=
      ⟨WithLp.toLp 1 v, (mem_constraint_kernel A (WithLp.toLp 1 v)).mpr hv⟩
    have hh := f.le_opNorm x
    change |v i| ≤ (2 * ‖f‖) * TV v
    have hn' : ‖x‖ = 2 * TV v := l1_norm x.1
    change |v i| ≤ ‖f‖ * ‖x‖ at hh
    rw [hn'] at hh
    nlinarith [hh]
  have hlow := hminimal (2 * ‖f‖) (by positivity) hbound
  change 2 * ‖f‖ = C
  linarith

omit [Nonempty I] in
theorem exists_exact_interval_dual (A : J → I → ℝ) (i : I) (C : ℝ)
    (hC : 0 ≤ C) (hb : SignedBound A i C)
    (hminimal : ∀ D : ℝ, 0 ≤ D → SignedBound A i D → C ≤ D) :
    ∃ coeff : J → ℝ, ∃ a b : ℝ,
      (∀ g, a ≤ dualScore A i coeff g ∧ dualScore A i coeff g ≤ b) ∧ b - a = C := by
  classical
  let K := LinearMap.ker (constraintMap A)
  let f := kernelCoordinate A i
  obtain ⟨g, hg, hnorm⟩ := exists_extension_norm_eq K f
  let ℓ : L1Vector I →ₗ[ℝ] ℝ := PiLp.projₗ 1 (𝕜 := ℝ) (fun _ : I => ℝ) i - g.toLinearMap
  have hann : ℓ ∈ K.dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator (W := K) ℓ).mpr
    intro x hx
    have h := hg (⟨x, hx⟩ : K)
    change g x = x i at h
    change x i - g x = 0
    exact sub_eq_zero.mpr h.symm
  have hrange : ℓ ∈ LinearMap.range (constraintMap A).dualMap := by
    rwa [(constraintMap A).range_dualMap_eq_dualAnnihilator_ker]
  obtain ⟨l, hl⟩ := hrange
  let c : ℝ := l (fun t : Option J => if none = t then 1 else 0)
  let coeff : J → ℝ := fun j => l (fun t : Option J => if some j = t then 1 else 0)
  have hscore : ∀ x, dualScore A i coeff x = c + g (PiLp.single 1 x (1 : ℝ)) := by
    intro x
    let sx : L1Vector I := PiLp.single 1 x 1
    have hs : constraintMap A sx = fun t : Option J =>
        match t with
        | none => 1
        | some j => A j x := by
      funext t
      cases t <;> simp [constraintMap, sx, PiLp.single_apply]
    have he := congrArg (fun z : L1Vector I →ₗ[ℝ] ℝ => z sx) hl
    change l (constraintMap A sx) = sx i - g sx at he
    have hex := LinearMap.pi_apply_eq_sum_univ l (constraintMap A sx)
    rw [Fintype.sum_option] at hex
    have hex' : l (constraintMap A sx) = c + ∑ j, coeff j * A j x := by
      simpa only [hs, smul_eq_mul, c, coeff, one_mul, mul_comm] using hex
    have hsi : sx i = if x = i then 1 else 0 := by
      simp [sx, PiLp.single_apply, eq_comm]
    dsimp [dualScore]
    change (if x = i then 1 else 0) - ∑ j, coeff j * A j x = c + g sx
    rw [hsi] at he
    linarith
  have hcoeff : ∀ x, |g (PiLp.single 1 x (1 : ℝ))| ≤ ‖f‖ := by
    intro x
    have h := g.le_opNorm (PiLp.single 1 x (1 : ℝ))
    have hs : ‖(PiLp.single 1 x (1 : ℝ) : L1Vector I)‖ = 1 := by
      rw [PiLp.norm_eq_of_L1]
      simp only [PiLp.single_apply, Real.norm_eq_abs]
      simp_rw [apply_ite abs]
      simp
    simpa only [Real.norm_eq_abs, hs, mul_one, hnorm] using h
  refine ⟨coeff, c - ‖f‖, c + ‖f‖, ?_, ?_⟩
  · intro x
    rw [hscore]
    have h := abs_le.mp (hcoeff x)
    constructor <;> linarith
  · have h := coordinate_norm_is_sharp A i C hC hb hminimal
    change 2 * ‖f‖ = C at h
    linarith

theorem exact_real_primal_dual (A : J → I → ℝ) (i : I) :
    ∃ C : ℝ, ∃ p q : I → ℝ, ∃ coeff : J → ℝ, ∃ a b : ℝ,
      0 ≤ C ∧ C ≤ 1 ∧ Probability p ∧ Probability q ∧ Match A p q ∧
      p i - q i = C ∧ PairBound A i C ∧ UniformLawBound A i C ∧
      (∀ g, a ≤ dualScore A i coeff g ∧ dualScore A i coeff g ≤ b) ∧ b - a = C := by
  obtain ⟨p, q, hp, hq, hm, hC, hpair⟩ := exists_optimal_pair A i
  let C := p i - q i
  have hs : SignedBound A i C := (signedBound_iff_pairBound A i C hC).mpr hpair
  have hminimal : ∀ D : ℝ, 0 ≤ D → SignedBound A i D → C ≤ D := by
    intro D hD hb
    exact (signedBound_iff_pairBound A i D hD).mp hb p q hp hq hm
  obtain ⟨coeff, a, b, hr, hw⟩ := exists_exact_interval_dual A i C hC hs hminimal
  refine ⟨C, p, q, coeff, a, b, hC, ?_, hp, hq, hm, rfl, hpair, ?_, hr, hw⟩
  · have hpi : p i ≤ 1 := (probability_subset_cube hp).2 i
    linarith [hq.1 i]
  · exact (uniformLawBound_iff_signedBound A i C).mpr hs

end
end OrbitalMarginals

-- Source: Oscillation.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I] [Fintype J]

def scoreMax (A : J → I → ℝ) (i : I) (coeff : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (dualScore A i coeff)

def scoreMin (A : J → I → ℝ) (i : I) (coeff : J → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (dualScore A i coeff)

def oscillation (A : J → I → ℝ) (i : I) (coeff : J → ℝ) : ℝ :=
  scoreMax A i coeff - scoreMin A i coeff

theorem score_range (A : J → I → ℝ) (i : I) (coeff : J → ℝ) (g : I) :
    scoreMin A i coeff ≤ dualScore A i coeff g ∧ dualScore A i coeff g ≤ scoreMax A i coeff := by
  exact ⟨Finset.inf'_le _ (Finset.mem_univ g), Finset.le_sup' _ (Finset.mem_univ g)⟩

theorem oscillation_nonneg (A : J → I → ℝ) (i : I) (coeff : J → ℝ) :
    0 ≤ oscillation A i coeff := by
  have h := score_range A i coeff i
  dsimp [oscillation]
  linarith

theorem oscillation_pairBound (A : J → I → ℝ) (i : I) (coeff : J → ℝ) :
    PairBound A i (oscillation A i coeff) := by
  exact intervalDual_pairBound A i _
    ⟨coeff, scoreMin A i coeff, scoreMax A i coeff, score_range A i coeff, le_rfl⟩

/-- The unreduced real primal and dual attain the same sharp response.
Both the probability variables and every dual coefficient are constructed,
without any assumed strong-duality or optimization premise. -/
theorem exact_oscillation_duality (A : J → I → ℝ) (i : I) :
    ∃ p q : I → ℝ, ∃ coeff : J → ℝ,
      Probability p ∧ Probability q ∧ Match A p q ∧
      p i - q i = oscillation A i coeff ∧
      PairBound A i (p i - q i) ∧ UniformLawBound A i (p i - q i) ∧
      ∀ otherCoeff : J → ℝ, p i - q i ≤ oscillation A i otherCoeff := by
  obtain ⟨C, p, q, coeff, a, b, hC, _, hp, hq, hm, heq, hb, hu, hr, hw⟩ :=
    exact_real_primal_dual A i
  have hmax : scoreMax A i coeff ≤ b := by
    exact Finset.sup'_le _ _ fun g _ => (hr g).2
  have hmin : a ≤ scoreMin A i coeff := by
    exact Finset.le_inf' _ _ fun g _ => (hr g).1
  have hupper : oscillation A i coeff ≤ C := by
    dsimp [oscillation]
    linarith
  have hlow : C ≤ oscillation A i coeff := by
    rw [← heq]
    exact oscillation_pairBound A i coeff p q hp hq hm
  have hosc : C = oscillation A i coeff := le_antisymm hlow hupper
  refine ⟨p, q, coeff, hp, hq, hm, heq.trans hosc, ?_, ?_, ?_⟩
  · simpa only [heq] using hb
  · simpa only [heq] using hu
  · intro otherCoeff
    exact oscillation_pairBound A i otherCoeff p q hp hq hm

end
end OrbitalMarginals

-- Source: GroupAction.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

def imageFeatures (xy : Ω × Ω) (g : G) : ℝ :=
  if g • xy.1 = xy.2 then 1 else 0

def imageMass (p : G → ℝ) (x y : Ω) : ℝ :=
  ∑ g, if g • x = y then p g else 0

omit [Fintype Ω] in
theorem match_iff_imageMass (p q : G → ℝ) : Match (imageFeatures (G := G) (Ω := Ω)) p q ↔
    ∀ x y : Ω, imageMass p x y = imageMass q x y := by
  constructor
  · intro h x y
    simpa [imageFeatures, imageMass] using h (x, y)
  · intro h xy
    simpa [imageFeatures, imageMass] using h xy.1 xy.2

def translate (σ : G) (v : G → ℝ) (g : G) : ℝ := v (σ * g)

theorem sum_translate (σ : G) (v : G → ℝ) :
    (∑ g, translate σ v g) = ∑ g, v g := by
  simpa [translate] using Equiv.sum_comp (Equiv.mulLeft σ) v

theorem tv_translate (σ : G) (v : G → ℝ) : TV (translate σ v) = TV v := by
  dsimp [TV, translate]
  congr 1
  simpa using Equiv.sum_comp (Equiv.mulLeft σ) (fun g => |v g|)

omit [Fintype G] [Fintype Ω] in
theorem imageFeature_translate (σ g : G) (x y : Ω) :
    imageFeatures (x, y) g = imageFeatures (x, σ • y) (σ * g) := by
  simp [imageFeatures, mul_smul, smul_left_cancel_iff]

theorem kernel_translate (σ : G) (v : G → ℝ) (hv : Kernel (imageFeatures (G := G) (Ω := Ω)) v) :
    Kernel (imageFeatures (G := G) (Ω := Ω)) (translate σ v) := by
  constructor
  · exact (sum_translate σ v).trans hv.1
  · rintro ⟨x, y⟩
    calc
      (∑ g, imageFeatures (x, y) g * translate σ v g) =
          ∑ g, imageFeatures (x, σ • y) (σ * g) * v (σ * g) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [imageFeature_translate σ g x y]
        rfl
      _ = ∑ g, imageFeatures (x, σ • y) g * v g := by
        simpa using Equiv.sum_comp (Equiv.mulLeft σ)
          (fun g => imageFeatures (x, σ • y) g * v g)
      _ = 0 := hv.2 (x, σ • y)

theorem signedBound_all_atoms (C : ℝ) (h : SignedBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) C) :
    ∀ σ : G, SignedBound (imageFeatures (G := G) (Ω := Ω)) σ C := by
  intro σ v hv
  have hh := h (translate σ v) (kernel_translate σ v hv)
  simpa only [translate, mul_one, tv_translate] using hh

theorem uniformBound_all_atoms (C : ℝ) (h : UniformLawBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) C) :
    ∀ σ : G, UniformLawBound (imageFeatures (G := G) (Ω := Ω)) σ C := by
  intro σ
  apply (uniformLawBound_iff_signedBound (imageFeatures (G := G) (Ω := Ω)) σ C).mpr
  exact signedBound_all_atoms C
    ((uniformLawBound_iff_signedBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) C).mp h) σ

/-- Actual finite-group image constraints and actual probability laws.
The sharp real primal/dual response applies without faithfulness or transitivity. -/
theorem group_action_exact_response :
    ∃ p q : G → ℝ, ∃ coeff : Ω × Ω → ℝ,
      Probability p ∧ Probability q ∧
      (∀ x y : Ω, imageMass p x y = imageMass q x y) ∧
      p 1 - q 1 = oscillation (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff ∧
      (∀ σ : G, ∀ ν : G → ℝ, Probability ν →
        (∀ x y : Ω, imageMass ν x y = imageMass (uniform : G → ℝ) x y) →
        |ν σ - uniform σ| ≤ (p 1 - q 1) * TV (fun g => ν g - uniform g)) ∧
      ∀ otherCoeff : Ω × Ω → ℝ, p 1 - q 1 ≤ oscillation (imageFeatures (G := G) (Ω := Ω)) (1 : G) otherCoeff := by
  obtain ⟨p, q, coeff, hp, hq, hm, ho, _, hu, hmin⟩ :=
    exact_oscillation_duality (imageFeatures (G := G) (Ω := Ω)) (1 : G)
  refine ⟨p, q, coeff, hp, hq, (match_iff_imageMass p q).mp hm, ho, ?_, hmin⟩
  intro σ ν hν hmatch
  exact uniformBound_all_atoms (p 1 - q 1) hu σ ν hν
    ((match_iff_imageMass ν uniform).mpr hmatch)

end
end OrbitalMarginals

-- Source: CentralReduction.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

def conjugationEquiv (h : G) : G ≃ G where
  toFun g := h * g * h⁻¹
  invFun g := h⁻¹ * g * h
  left_inv g := by group
  right_inv g := by group

def conjugate (h : G) (v : G → ℝ) (g : G) : ℝ := v (h * g * h⁻¹)

def centralAverage (v : G → ℝ) (g : G) : ℝ :=
  (∑ h, conjugate h v g) / (Fintype.card G : ℝ)

def Central (v : G → ℝ) : Prop := ∀ h g, v (h * g * h⁻¹) = v g

theorem sum_conjugate (h : G) (v : G → ℝ) : (∑ g, conjugate h v g) = ∑ g, v g := by
  simpa [conjugate, conjugationEquiv] using Equiv.sum_comp (conjugationEquiv h) v

omit [Fintype G] [Fintype Ω] in
theorem imageFeature_conjugate (h g : G) (x y : Ω) :
    imageFeatures (x, y) g = imageFeatures (h • x, h • y) (h * g * h⁻¹) := by
  simp [imageFeatures, mul_smul, smul_left_cancel_iff]

omit [Fintype Ω] in
theorem kernel_conjugate (h : G) (v : G → ℝ) (hv : Kernel (imageFeatures (G := G) (Ω := Ω)) v) :
    Kernel (imageFeatures (G := G) (Ω := Ω)) (conjugate h v) := by
  constructor
  · exact (sum_conjugate h v).trans hv.1
  · rintro ⟨x, y⟩
    calc
      (∑ g, imageFeatures (x, y) g * conjugate h v g) =
          ∑ g, imageFeatures (h • x, h • y) (h * g * h⁻¹) * v (h * g * h⁻¹) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [imageFeature_conjugate h g x y]
        rfl
      _ = ∑ g, imageFeatures (h • x, h • y) g * v g := by
        simpa [conjugationEquiv] using Equiv.sum_comp (conjugationEquiv h)
          (fun g => imageFeatures (h • x, h • y) g * v g)
      _ = 0 := hv.2 (h • x, h • y)

theorem centralAverage_one (v : G → ℝ) : centralAverage v 1 = v 1 := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [centralAverage, conjugate, hc]

theorem centralAverage_central (v : G → ℝ) : Central (centralAverage v) := by
  intro s g
  dsimp [centralAverage, conjugate]
  congr 1
  calc
    (∑ h, v (h * (s * g * s⁻¹) * h⁻¹)) =
        ∑ h, v ((h * s) * g * (h * s)⁻¹) := by
      apply Finset.sum_congr rfl
      intro h _
      apply congrArg v
      group
    _ = ∑ h, v (h * g * h⁻¹) := by
      simpa using Equiv.sum_comp (Equiv.mulRight s) (fun h => v (h * g * h⁻¹))

theorem centralAverage_probability (p : G → ℝ) (hp : Probability p) :
    Probability (centralAverage p) := by
  have hc : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · intro g
    exact div_nonneg (Finset.sum_nonneg fun h _ => hp.1 _) hc.le
  · dsimp [centralAverage]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [sum_conjugate, hp.2]
    simp [hc.ne']

theorem centralAverage_kernel (v : G → ℝ) (hv : Kernel (imageFeatures (G := G) (Ω := Ω)) v) :
    Kernel (imageFeatures (G := G) (Ω := Ω)) (centralAverage v) := by
  constructor
  · dsimp [centralAverage]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp_rw [sum_conjugate, hv.1]
    simp
  · intro xy
    dsimp [centralAverage]
    simp only [← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
    rw [Finset.sum_comm]
    have hh : ∀ h, (∑ g, imageFeatures xy g * conjugate h v g) = 0 :=
      fun h => (kernel_conjugate h v hv).2 xy
    simp_rw [hh]
    simp

theorem centralAverage_sub (p q : G → ℝ) :
    centralAverage (fun g => p g - q g) = fun g => centralAverage p g - centralAverage q g := by
  funext g
  simp [centralAverage, conjugate, Finset.sum_sub_distrib, sub_div]

omit [Fintype Ω] in
theorem match_of_difference_kernel (p q : G → ℝ)
    (h : Kernel (imageFeatures (G := G) (Ω := Ω)) (fun g => p g - q g)) : Match (imageFeatures (G := G) (Ω := Ω)) p q := by
  intro xy
  apply sub_eq_zero.mp
  simpa only [mul_sub, Finset.sum_sub_distrib] using h.2 xy

theorem centralAverage_match (p q : G → ℝ) (hp : Probability p) (hq : Probability q)
    (hm : Match (imageFeatures (G := G) (Ω := Ω)) p q) : Match (imageFeatures (G := G) (Ω := Ω)) (centralAverage p) (centralAverage q) := by
  apply match_of_difference_kernel
  rw [← centralAverage_sub]
  exact centralAverage_kernel _ (kernel_of_match (imageFeatures (G := G) (Ω := Ω)) p q hp hq hm)

theorem group_action_central_primal :
    ∃ p q : G → ℝ, ∃ coeff : Ω × Ω → ℝ,
      Probability p ∧ Probability q ∧ Central p ∧ Central q ∧
      (∀ x y : Ω, imageMass p x y = imageMass q x y) ∧
      p 1 - q 1 = oscillation (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff ∧
      PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (p 1 - q 1) ∧
      ∀ otherCoeff : Ω × Ω → ℝ, p 1 - q 1 ≤ oscillation (imageFeatures (G := G) (Ω := Ω)) (1 : G) otherCoeff := by
  obtain ⟨p, q, coeff, hp, hq, hm, ho, hb, _, hmin⟩ :=
    exact_oscillation_duality (imageFeatures (G := G) (Ω := Ω)) (1 : G)
  refine ⟨centralAverage p, centralAverage q, coeff,
    centralAverage_probability p hp, centralAverage_probability q hq,
    centralAverage_central p, centralAverage_central q,
    (match_iff_imageMass _ _).mp (centralAverage_match p q hp hq hm), ?_, ?_, ?_⟩
  · simpa only [centralAverage_one] using ho
  · simpa only [centralAverage_one] using hb
  · simpa only [centralAverage_one] using hmin

end
end OrbitalMarginals

-- Source: SharpAttainment.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I]

theorem optimal_pair_tv_one (A : J → I → ℝ) (i : I) (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q) (hm : Match A p q)
    (hpos : 0 < p i - q i) (hb : PairBound A i (p i - q i)) :
    TV (fun g => p g - q g) = 1 := by
  have hs := (signedBound_iff_pairBound A i (p i - q i) hpos.le).mpr hb
  have hh := hs _ (kernel_of_match A p q hp hq hm)
  rw [abs_of_pos hpos] at hh
  have hu := tv_probability_difference_le_one p q hp hq
  apply le_antisymm hu
  nlinarith

theorem probability_parts_disjoint_of_tv_one (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q)
    (htv : TV (fun g => p g - q g) = 1) : ∀ g, p g = 0 ∨ q g = 0 := by
  let f : I → ℝ := fun g => p g + q g - |p g - q g|
  have hf : ∀ g, 0 ≤ f g := by
    intro g
    dsimp [f]
    have hh := abs_sub (p g) (q g)
    rw [abs_of_nonneg (hp.1 g), abs_of_nonneg (hq.1 g)] at hh
    linarith
  have hsum : ∑ g, f g = 0 := by
    have habs : ∑ g, |p g - q g| = 2 := by dsimp [TV] at htv; linarith
    simp only [f, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2, hq.2, habs]
    norm_num
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun g _ => hf g).mp hsum
  intro g
  have hz := hzero g (Finset.mem_univ g)
  dsimp [f] at hz
  by_cases h : q g ≤ p g
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr h)] at hz
    linarith
  · left
    rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge h))] at hz
    linarith

theorem probability_perturbation_smaller (v : I → ℝ) (ε δ : ℝ)
    (hδ : 0 ≤ δ) (hle : δ ≤ ε)
    (hp : Probability (fun g => uniform g + ε * v g))
    (hv : ∑ g, v g = 0) : Probability (fun g => uniform g + δ * v g) := by
  constructor
  · intro g
    by_cases h : 0 ≤ v g
    · exact add_nonneg (uniform_pos g).le (mul_nonneg hδ h)
    · have hh := mul_le_mul_of_nonpos_right hle (le_of_not_ge h)
      linarith [hp.1 g]
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hv, mul_zero, add_zero]
    exact uniform_probability.2

theorem perturbation_match (A : J → I → ℝ) (v : I → ℝ)
    (hv : Kernel A v) (δ : ℝ) :
    Match A (fun g => uniform g + δ * v g) uniform := by
  intro j
  simp only [mul_add, mul_left_comm (A j _) δ, Finset.sum_add_distrib,
    ← Finset.mul_sum, hv.2 j, mul_zero, add_zero]

theorem positive_optimum_attained_locally (A : J → I → ℝ) (i : I)
    (p q : I → ℝ) (hp : Probability p) (hq : Probability q) (hm : Match A p q)
    (hpos : 0 < p i - q i) (hb : PairBound A i (p i - q i)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε →
      Probability (fun g => uniform g + δ * (p g - q g)) ∧
      Match A (fun g => uniform g + δ * (p g - q g)) uniform ∧
      TV (fun g => (uniform g + δ * (p g - q g)) - uniform g) = δ ∧
      (uniform i + δ * (p i - q i)) - uniform i = (p i - q i) * δ := by
  have hv := kernel_of_match A p q hp hq hm
  obtain ⟨ε, hε, hprob, _⟩ := kernel_small_perturbation A _ hv
  have htv := optimal_pair_tv_one A i p q hp hq hm hpos hb
  refine ⟨ε, hε, fun δ hδ hle => ⟨
    probability_perturbation_smaller _ ε δ hδ hle hprob hv.1,
    perturbation_match A _ hv δ, ?_, ?_⟩⟩
  · simp only [add_sub_cancel_left, tv_smul, abs_of_nonneg hδ, htv, mul_one]
  · ring

end
end OrbitalMarginals

-- Source: RationalProjection.lean

open scoped BigOperators
open Set

namespace OrbitalMarginals

noncomputable section

/-- A rational-linear functional fixes rational constants and preserves the signs
of any specified finite collection of nonnegative real numbers.  Positivity is
only asserted on the supplied finite set, never globally on the real line. -/
theorem finite_rational_projection (s : Finset ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, f 1 = 1 ∧ ∀ x ∈ s, 0 ≤ x → 0 ≤ f x := by
  classical
  let t : Finset ℝ := insert 1 s
  let S : Submodule ℚ ℝ := Submodule.span ℚ (t : Set ℝ)
  let b := Module.finBasis ℚ S
  let K := Fin (Module.finrank ℚ S)
  let X := {x : ℝ // x ∈ t.filter (fun x => 0 < x)}
  letI : Fintype X := (t.filter (fun x => 0 < x)).fintypeCoeSort
  let sx : X → S := fun x => ⟨x.1, Submodule.subset_span (Finset.mem_filter.mp x.2).1⟩
  let L : X → (K → ℝ) → ℝ := fun x w =>
    ∑ i, ((b.repr (sx x) i : ℚ) : ℝ) * w i
  let U : Set (K → ℝ) := {w | ∀ x : X, 0 < L x w}
  have hU : IsOpen U := by
    have hh : IsOpen (⋂ x : X, {w | 0 < L x w}) :=
      isOpen_iInter_of_finite fun x => isOpen_lt continuous_const (by dsimp [L]; fun_prop)
    convert hh using 1
    ext w
    simp [U]
  let v : K → ℝ := fun i => (b i).1
  have hv : v ∈ U := by
    intro x
    have he : L x v = x.1 := by
      have hh := congrArg (fun z : S => (z : ℝ)) (b.sum_repr (sx x))
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def] using hh
    rw [he]
    exact (Finset.mem_filter.mp x.2).2
  have hd : DenseRange (fun r : K → ℚ => fun i => (r i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨r, hr⟩ := hd.exists_mem_open hU ⟨v, hv⟩
  let fs : S →ₗ[ℚ] ℚ := b.constr ℚ r
  obtain ⟨g, hg⟩ := fs.exists_extend
  have hgx (x : X) : 0 < g x.1 := by
    have he : (g x.1 : ℝ) = L x (fun i => (r i : ℝ)) := by
      have hh := congrArg (fun f : S →ₗ[ℚ] ℚ => f (sx x)) hg
      change g x.1 = fs (sx x) at hh
      rw [hh]
      simp [fs, Module.Basis.constr_apply_fintype, L]
    exact_mod_cast (he.symm ▸ hr x)
  have h1 : 0 < g 1 := by
    exact hgx ⟨1, by simp [t]⟩
  let f : ℝ →ₗ[ℚ] ℚ := (g 1)⁻¹ • g
  refine ⟨f, ?_, ?_⟩
  · simp [f, h1.ne']
  · intro x hx hnonneg
    by_cases hz : x = 0
    · simp [hz]
    · have hxpos : 0 < x := lt_of_le_of_ne hnonneg (Ne.symm hz)
      have hh := hgx ⟨x, by simp [t, hx, hxpos]⟩
      change 0 ≤ (g 1)⁻¹ * g x
      positivity

/-- Evaluation on a rational multiple commutes with the rational projection. -/
theorem rational_projection_mul (f : ℝ →ₗ[ℚ] ℚ) (c : ℚ) (x : ℝ) :
    f ((c : ℝ) * x) = c * f x := by
  simpa only [Rat.smul_def, Rat.cast_id] using f.map_smul c x

end
end OrbitalMarginals

-- Source: RationalDuality.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I] [Fintype J]

def rationalFeatures (A : J → I → ℚ) : J → I → ℝ := fun j g => (A j g : ℝ)

def rationalLaw (p : I → ℚ) : I → ℝ := fun g => (p g : ℝ)

/-- Rationalize a zero-gap primal/dual witness simultaneously.  Applying a
rational-linear map separately to arbitrarily rounded data would not suffice. -/
theorem rationalize_pair_dual (A : J → I → ℚ) (i : I)
    (p q : I → ℝ) (coeff : J → ℝ) (a b : ℝ)
    (hp : Probability p) (hq : Probability q) (hm : Match (rationalFeatures A) p q)
    (hr : ∀ g, a ≤ dualScore (rationalFeatures A) i coeff g ∧
      dualScore (rationalFeatures A) i coeff g ≤ b)
    (hgap : p i - q i = b - a) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, f 1 = 1 ∧
      Probability (fun g => (f (p g) : ℝ)) ∧
      Probability (fun g => (f (q g) : ℝ)) ∧
      Match (rationalFeatures A) (fun g => (f (p g) : ℝ)) (fun g => (f (q g) : ℝ)) ∧
      (f (p i) : ℝ) - (f (q i) : ℝ) = (f b : ℝ) - (f a : ℝ) ∧
      ∀ g, (f a : ℝ) ≤ dualScore (rationalFeatures A) i (fun j => (f (coeff j) : ℝ)) g ∧
        dualScore (rationalFeatures A) i (fun j => (f (coeff j) : ℝ)) g ≤ (f b : ℝ) := by
  classical
  let lower : I → ℝ := fun g => dualScore (rationalFeatures A) i coeff g - a
  let upper : I → ℝ := fun g => b - dualScore (rationalFeatures A) i coeff g
  let s : Finset ℝ := Finset.univ.image p ∪ Finset.univ.image q ∪
    Finset.univ.image lower ∪ Finset.univ.image upper
  obtain ⟨f, hf1, hf⟩ := finite_rational_projection s
  have hprob (v : I → ℝ) (hv : Probability v) (hvs : ∀ g, v g ∈ s) :
      Probability (fun g => (f (v g) : ℝ)) := by
    constructor
    · intro g
      change 0 ≤ (f (v g) : ℝ)
      exact_mod_cast hf (v g) (hvs g) (hv.1 g)
    · have he : ∑ g, f (v g) = 1 := by rw [← map_sum, hv.2, hf1]
      change (∑ g, (f (v g) : ℝ)) = 1
      exact_mod_cast he
  have hp' := hprob p hp (fun g => by simp [s])
  have hq' := hprob q hq (fun g => by simp [s])
  have hm' : Match (rationalFeatures A) (fun g => (f (p g) : ℝ))
      (fun g => (f (q g) : ℝ)) := by
    intro j
    have he : (∑ g, A j g * f (p g)) = ∑ g, A j g * f (q g) := by
      have hh := congrArg f (hm j)
      simpa only [rationalFeatures, map_sum, rational_projection_mul] using hh
    change (∑ g, (A j g : ℝ) * (f (p g) : ℝ)) = ∑ g, (A j g : ℝ) * (f (q g) : ℝ)
    exact_mod_cast he
  let scoreQ : I → ℚ := fun g => (if g = i then 1 else 0) - ∑ j, f (coeff j) * A j g
  have hscore (g : I) : f (dualScore (rationalFeatures A) i coeff g) = scoreQ g := by
    simp only [dualScore, rationalFeatures, map_sub, map_sum, scoreQ]
    congr 1
    · split_ifs <;> simp [hf1]
    · apply Finset.sum_congr rfl
      intro j _
      simpa only [mul_comm] using rational_projection_mul f (A j g) (coeff j)
  have hcast (g : I) : dualScore (rationalFeatures A) i (fun j => (f (coeff j) : ℝ)) g =
      (scoreQ g : ℝ) := by
    by_cases h : g = i <;> simp [dualScore, rationalFeatures, scoreQ, h]
  refine ⟨f, hf1, hp', hq', hm', ?_, ?_⟩
  · have he := congrArg f hgap
    simp only [map_sub] at he
    exact_mod_cast he
  · intro g
    have hlo := hf (lower g) (by simp [s]) (sub_nonneg.mpr (hr g).1)
    have hup := hf (upper g) (by simp [s]) (sub_nonneg.mpr (hr g).2)
    simp only [lower, upper, map_sub, hscore] at hlo hup
    rw [hcast]
    constructor
    · exact_mod_cast (by linarith : f a ≤ scoreQ g)
    · exact_mod_cast (by linarith : scoreQ g ≤ f b)

/-- Every finite rational feature system has rational optimal primal and dual
solutions; no LP solver, vertex-existence axiom, or rationality premise is used. -/
theorem exact_rational_primal_dual (A : J → I → ℚ) (i : I) :
    ∃ C : ℚ, ∃ p q : I → ℚ, ∃ coeff : J → ℚ, ∃ a b : ℚ,
      0 ≤ C ∧ C ≤ 1 ∧
      Probability (rationalLaw p) ∧ Probability (rationalLaw q) ∧
      Match (rationalFeatures A) (rationalLaw p) (rationalLaw q) ∧
      p i - q i = C ∧ b - a = C ∧
      (∀ g, (a : ℝ) ≤ dualScore (rationalFeatures A) i (fun j => (coeff j : ℝ)) g ∧
        dualScore (rationalFeatures A) i (fun j => (coeff j : ℝ)) g ≤ (b : ℝ)) ∧
      PairBound (rationalFeatures A) i (C : ℝ) ∧
      UniformLawBound (rationalFeatures A) i (C : ℝ) := by
  obtain ⟨C, p, q, coeff, a, b, hC, hC1, hp, hq, hm, heq, hb, _, hr, hw⟩ :=
    exact_real_primal_dual (rationalFeatures A) i
  obtain ⟨f, _, hp', hq', hm', hg, hr'⟩ :=
    rationalize_pair_dual A i p q coeff a b hp hq hm hr (heq.trans hw.symm)
  let c : ℚ := f (p i) - f (q i)
  have hnew : PairBound (rationalFeatures A) i (c : ℝ) := by
    apply intervalDual_pairBound
    refine ⟨(fun j => (f (coeff j) : ℝ)), (f a : ℝ), (f b : ℝ), hr', ?_⟩
    dsimp [c]
    push_cast
    exact le_of_eq hg.symm
  have hc : (c : ℝ) = C := by
    have hle := hb _ _ hp' hq' hm'
    have hge := hnew p q hp hq hm
    dsimp [c] at hge ⊢
    push_cast at hge ⊢
    linarith [heq]
  refine ⟨c, (fun g => f (p g)), (fun g => f (q g)), (fun j => f (coeff j)),
    f a, f b, ?_, ?_, hp', hq', hm', rfl, ?_, hr', hnew, ?_⟩
  · exact_mod_cast hc ▸ hC
  · exact_mod_cast hc ▸ hC1
  · exact_mod_cast hg.symm
  · rw [hc]
    exact (uniformLawBound_iff_pairBound (rationalFeatures A) i C hC).mpr hb

end
end OrbitalMarginals

-- Source: FiniteFibers.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I K J : Type*} [Fintype I] [Fintype K] [DecidableEq K]

def fiber (f : I → K) (k : K) : Finset I := Finset.univ.filter (fun i => f i = k)

def fiberSize (f : I → K) (k : K) : ℝ := (fiber f k).card

def pushLaw (f : I → K) (v : I → ℝ) (k : K) : ℝ := ∑ i ∈ fiber f k, v i

def liftLaw (f : I → K) (p : K → ℝ) (i : I) : ℝ := p (f i) / fiberSize f (f i)

theorem fiberSize_pos (f : I → K) (hf : Function.Surjective f) (k : K) :
    0 < fiberSize f k := by
  obtain ⟨i, hi⟩ := hf k
  have hh : (fiber f k).Nonempty := ⟨i, by simp [fiber, hi]⟩
  dsimp [fiberSize]
  exact_mod_cast Finset.card_pos.mpr hh

theorem sum_pushLaw (f : I → K) (v : I → ℝ) :
    (∑ k, pushLaw f v k) = ∑ i, v i :=
  Finset.sum_fiberwise Finset.univ f v

theorem pushLaw_liftLaw (f : I → K) (hf : Function.Surjective f) (p : K → ℝ) :
    pushLaw f (liftLaw f p) = p := by
  funext k
  dsimp [pushLaw]
  calc
    (∑ i ∈ fiber f k, liftLaw f p i) = ∑ _i ∈ fiber f k, p k / fiberSize f k := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [liftLaw, (Finset.mem_filter.mp hi).2]
    _ = p k := by
      rw [Finset.sum_const, nsmul_eq_mul]
      change fiberSize f k * (p k / fiberSize f k) = p k
      field_simp [(fiberSize_pos f hf k).ne']

theorem sum_liftLaw (f : I → K) (hf : Function.Surjective f) (p : K → ℝ) :
    (∑ i, liftLaw f p i) = ∑ k, p k := by
  rw [← sum_pushLaw f, pushLaw_liftLaw f hf]

theorem pushLaw_probability (f : I → K) (v : I → ℝ) (hv : Probability v) :
    Probability (pushLaw f v) :=
  ⟨fun k => Finset.sum_nonneg (fun i _ => hv.1 i), (sum_pushLaw f v).trans hv.2⟩

theorem liftLaw_probability (f : I → K) (hf : Function.Surjective f)
    (p : K → ℝ) (hp : Probability p) : Probability (liftLaw f p) :=
  ⟨fun i => div_nonneg (hp.1 _) (fiberSize_pos f hf _).le,
    (sum_liftLaw f hf p).trans hp.2⟩

theorem liftLaw_pushLaw (f : I → K) (v : I → ℝ)
    (hconstant : ∀ i j, f i = f j → v i = v j) : liftLaw f (pushLaw f v) = v := by
  funext i
  have hs : pushLaw f v (f i) = fiberSize f (f i) * v i := by
    dsimp [pushLaw, fiberSize]
    calc
      (∑ j ∈ fiber f (f i), v j) = ∑ _j ∈ fiber f (f i), v i := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hconstant j i (Finset.mem_filter.mp hj).2
      _ = _ := by simp
  have hh : (fiber f (f i)).Nonempty := ⟨i, by simp [fiber]⟩
  have hn : fiberSize f (f i) ≠ 0 := by
    dsimp [fiberSize]
    exact_mod_cast (Finset.card_pos.mpr hh).ne'
  simp [liftLaw, hs, hn]

theorem fiber_moment (f : I → K) (M : K → ℝ) (v : I → ℝ) :
    (∑ i, M (f i) * v i) = ∑ k, M k * pushLaw f v k := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun i => M (f i) * v i)]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [pushLaw]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem lift_match (f : I → K) (hf : Function.Surjective f) (M : J → K → ℝ)
    (p q : K → ℝ) :
    Match (fun j i => M j (f i)) (liftLaw f p) (liftLaw f q) ↔ Match M p q := by
  have he (v : K → ℝ) (j : J) :
      (∑ i, M j (f i) * liftLaw f v i) = ∑ k, M j k * v k := by
    rw [fiber_moment f (M j), pushLaw_liftLaw f hf]
  constructor <;> intro h j
  · rw [← he p j, ← he q j]
    exact h j
  · rw [he p j, he q j]
    exact h j

end
end OrbitalMarginals

-- Source: OrbitalReduction.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

abbrev Orbitals (G Ω : Type*) [Group G] [MulAction G Ω] :=
  MulAction.orbitRel.Quotient G (Ω × Ω)

noncomputable instance : Fintype (Orbitals G Ω) := Fintype.ofFinite _

noncomputable instance : DecidableEq (Orbitals G Ω) := Classical.decEq _

def orbitalOf (xy : Ω × Ω) : Orbitals G Ω := Quotient.mk'' xy

theorem orbitalOf_smul (h : G) (xy : Ω × Ω) :
    orbitalOf (G := G) (h • xy) = orbitalOf (G := G) xy :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

def orbitalFeatures (o : Orbitals G Ω) (g : G) : ℝ :=
  ∑ x : Ω, if orbitalOf (G := G) (x, g • x) = o then 1 else 0

def averagedCoefficient (coeff : Ω × Ω → ℝ) (xy : Ω × Ω) : ℝ :=
  (∑ h : G, coeff (h • xy)) / (Fintype.card G : ℝ)

theorem averagedCoefficient_smul (coeff : Ω × Ω → ℝ) (s : G) (xy : Ω × Ω) :
    averagedCoefficient (G := G) coeff (s • xy) = averagedCoefficient (G := G) coeff xy := by
  dsimp [averagedCoefficient]
  congr 1
  have hh := Equiv.sum_comp (Equiv.mulRight s) (fun h => coeff (h • xy))
  change (∑ h, coeff ((h * s) • xy)) = ∑ h, coeff (h • xy) at hh
  simpa only [mul_smul] using hh

def orbitalCoefficient (coeff : Ω × Ω → ℝ) : Orbitals G Ω → ℝ :=
  Quotient.lift (averagedCoefficient (G := G) coeff) (by
    intro xy zw hr
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hr)
    rw [← hh]
    exact averagedCoefficient_smul coeff h zw)

theorem orbitalCoefficient_apply (coeff : Ω × Ω → ℝ) (xy : Ω × Ω) :
    orbitalCoefficient coeff (orbitalOf (G := G) xy) = averagedCoefficient (G := G) coeff xy := rfl

theorem orbital_score_expansion (coeff : Orbitals G Ω → ℝ) (g : G) :
    (∑ o, coeff o * orbitalFeatures o g) =
      ∑ xy : Ω × Ω, coeff (orbitalOf (G := G) xy) * imageFeatures xy g := by
  classical
  calc
    (∑ o, coeff o * orbitalFeatures o g) =
        ∑ x : Ω, coeff (orbitalOf (G := G) (x, g • x)) := by
      simp only [orbitalFeatures, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [eq_comm]
    _ = ∑ xy : Ω × Ω, coeff (orbitalOf (G := G) xy) * imageFeatures xy g := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      simp [imageFeatures, eq_comm]

theorem averaged_score (coeff : Ω × Ω → ℝ) (g : G) :
    dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) (averagedCoefficient (G := G) coeff) g =
      (∑ h : G, dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff
        (h * g * h⁻¹)) / (Fintype.card G : ℝ) := by
  classical
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hid (h : G) : (h * g * h⁻¹ = 1) ↔ g = 1 := by
    constructor
    · intro he
      calc
        g = h⁻¹ * (h * g * h⁻¹) * h := by group
        _ = 1 := by rw [he]; group
    · intro he
      rw [he]
      group
  have hexpand :
      (∑ xy : Ω × Ω, averagedCoefficient (G := G) coeff xy * imageFeatures xy g) =
        (∑ h : G, ∑ xy : Ω × Ω, coeff xy * imageFeatures xy (h * g * h⁻¹)) /
          (Fintype.card G : ℝ) := by
    simp only [averagedCoefficient, div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    calc
      (∑ xy : Ω × Ω, coeff (h • xy) * imageFeatures xy g) =
          ∑ xy : Ω × Ω, coeff (h • xy) * imageFeatures (h • xy) (h * g * h⁻¹) := by
        apply Finset.sum_congr rfl
        rintro ⟨x, y⟩ _
        rw [imageFeature_conjugate h g x y]
        rfl
      _ = ∑ xy : Ω × Ω, coeff xy * imageFeatures xy (h * g * h⁻¹) := by
        exact Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Ω × Ω))
          (fun xy : Ω × Ω => coeff xy * imageFeatures xy (h * g * h⁻¹))
  simp only [dualScore, hid, Finset.sum_sub_distrib]
  rw [hexpand]
  by_cases he : g = 1 <;> simp [sub_div, he, hc, neg_div]

theorem orbital_dual_range (coeff : Ω × Ω → ℝ) (a b : ℝ)
    (hr : ∀ g : G, a ≤ dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff g ∧
      dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff g ≤ b) :
    ∀ g : G, a ≤ dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
        (orbitalCoefficient coeff) g ∧
      dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
        (orbitalCoefficient coeff) g ≤ b := by
  classical
  have hc : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  intro g
  have hs : dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
      (orbitalCoefficient coeff) g =
      (∑ h : G, dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff
        (h * g * h⁻¹)) / (Fintype.card G : ℝ) := by
    rw [← averaged_score]
    simp only [dualScore, orbital_score_expansion, orbitalCoefficient_apply]
  rw [hs]
  constructor
  · apply (le_div_iff₀ hc).mpr
    calc
      a * (Fintype.card G : ℝ) = ∑ _h : G, a := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun h _ => (hr _).1
  · apply (div_le_iff₀ hc).mpr
    calc
      _ ≤ ∑ _h : G, b := Finset.sum_le_sum fun h _ => (hr _).2
      _ = b * (Fintype.card G : ℝ) := by simp [mul_comm]

theorem match_image_implies_orbital (p q : G → ℝ)
    (hm : Match (imageFeatures (G := G) (Ω := Ω)) p q) :
    Match (orbitalFeatures (G := G) (Ω := Ω)) p q := by
  classical
  intro o
  have hexpand (v : G → ℝ) :
      (∑ g, orbitalFeatures o g * v g) =
        ∑ xy : Ω × Ω, (if orbitalOf (G := G) xy = o then 1 else 0) *
          (∑ g, imageFeatures xy g * v g) := by
    have hh (g : G) := orbital_score_expansion
      (fun o' => if o' = o then 1 else 0) g
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hh
    simp_rw [hh, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xy _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> ring
  rw [hexpand p, hexpand q]
  apply Finset.sum_congr rfl
  intro xy _
  rw [hm xy]

/-- The unreduced real primal has an optimal orbital dual, with all moments and
all probability laws interpreted by their actual finite sums. -/
theorem exact_orbital_duality :
    ∃ p q : G → ℝ, ∃ coeff : Orbitals G Ω → ℝ,
      Probability p ∧ Probability q ∧ Central p ∧ Central q ∧
      Match (imageFeatures (G := G) (Ω := Ω)) p q ∧
      p 1 - q 1 = oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff ∧
      PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (p 1 - q 1) ∧
      ∀ otherCoeff : Orbitals G Ω → ℝ,
        p 1 - q 1 ≤ oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) otherCoeff := by
  classical
  obtain ⟨p, q, raw, hp, hq, hpc, hqc, hm, ho, hb, _⟩ :=
    group_action_central_primal (G := G) (Ω := Ω)
  have hmatch := (match_iff_imageMass p q).mpr hm
  let coeff : Orbitals G Ω → ℝ := orbitalCoefficient raw
  have hr := orbital_dual_range raw
    (scoreMin (imageFeatures (G := G) (Ω := Ω)) (1 : G) raw)
    (scoreMax (imageFeatures (G := G) (Ω := Ω)) (1 : G) raw)
    (score_range _ _ _)
  have hupper : oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff ≤ p 1 - q 1 := by
    rw [ho]
    dsimp [oscillation]
    have h1 : scoreMax (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff ≤
        scoreMax (imageFeatures (G := G) (Ω := Ω)) (1 : G) raw :=
      Finset.sup'_le _ _ fun g _ => (hr g).2
    have h2 : scoreMin (imageFeatures (G := G) (Ω := Ω)) (1 : G) raw ≤
        scoreMin (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff :=
      Finset.le_inf' _ _ fun g _ => (hr g).1
    linarith
  have hpair := match_image_implies_orbital p q hmatch
  have hmin (other : Orbitals G Ω → ℝ) :
      p 1 - q 1 ≤ oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) other :=
    (oscillation_pairBound _ _ other) p q hp hq hpair
  exact ⟨p, q, coeff, hp, hq, hpc, hqc, hmatch, le_antisymm (hmin coeff) hupper, hb, hmin⟩

end
end OrbitalMarginals

-- Source: OrbitalConstraints.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

theorem orbital_moment_expansion (o : Orbitals G Ω) (v : G → ℝ) :
    (∑ g, orbitalFeatures o g * v g) =
      ∑ xy : Ω × Ω, (if orbitalOf (G := G) xy = o then (1 : ℝ) else 0) *
        (∑ g, imageFeatures xy g * v g) := by
  classical
  have hh (g : G) := orbital_score_expansion
    (fun o' : Orbitals G Ω => if o' = o then (1 : ℝ) else 0) g
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hh
  simp_rw [hh, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xy _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> ring

theorem central_image_moment_smul (p : G → ℝ) (hp : Central p)
    (h : G) (xy : Ω × Ω) :
    (∑ g, imageFeatures (h • xy) g * p g) = ∑ g, imageFeatures xy g * p g := by
  calc
    (∑ g, imageFeatures (h • xy) g * p g) =
        ∑ g, imageFeatures (h • xy) (h * g * h⁻¹) * p (h * g * h⁻¹) :=
      (Equiv.sum_comp (conjugationEquiv h) _).symm
    _ = ∑ g, imageFeatures xy g * p g := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hp h g]
      change imageFeatures (h • xy.1, h • xy.2) (h * g * h⁻¹) * p g =
        imageFeatures (xy.1, xy.2) g * p g
      rw [← imageFeature_conjugate h g xy.1 xy.2]

theorem central_image_moment_orbital (p : G → ℝ) (hp : Central p)
    (xy zw : Ω × Ω) (he : orbitalOf (G := G) xy = orbitalOf (G := G) zw) :
    (∑ g, imageFeatures xy g * p g) = ∑ g, imageFeatures zw g * p g := by
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact he))
  rw [← hh]
  exact central_image_moment_smul p hp h zw

theorem central_match_iff_orbital (p q : G → ℝ) (hp : Central p) (hq : Central q) :
    Match (imageFeatures (G := G) (Ω := Ω)) p q ↔
      Match (orbitalFeatures (G := G) (Ω := Ω)) p q := by
  constructor
  · exact match_image_implies_orbital p q
  · intro hm xy
    classical
    let o := orbitalOf (G := G) xy
    let t : Finset (Ω × Ω) := Finset.univ.filter (fun zw => orbitalOf (G := G) zw = o)
    have ht : 0 < (t.card : ℝ) := by
      have hne : t.Nonempty := ⟨xy, by simp [t, o]⟩
      exact_mod_cast Finset.card_pos.mpr hne
    have hexpand (v : G → ℝ) (hv : Central v) :
        (∑ g, orbitalFeatures o g * v g) = (t.card : ℝ) * (∑ g, imageFeatures xy g * v g) := by
      rw [orbital_moment_expansion]
      calc
        (∑ zw : Ω × Ω, (if orbitalOf (G := G) zw = o then (1 : ℝ) else 0) *
            (∑ g, imageFeatures zw g * v g)) =
            ∑ zw ∈ t, (∑ g, imageFeatures zw g * v g) := by
          simp [t, Finset.sum_filter, ite_mul]
        _ = ∑ _zw ∈ t, (∑ g, imageFeatures xy g * v g) := by
          apply Finset.sum_congr rfl
          intro zw hzw
          exact central_image_moment_orbital v hv zw xy (Finset.mem_filter.mp hzw).2
        _ = _ := by simp
    have hh := hm o
    rw [hexpand p hp, hexpand q hq] at hh
    exact (mul_left_cancel₀ ht.ne') hh

theorem orbitalFeatures_conjugate (o : Orbitals G Ω) (h g : G) :
    orbitalFeatures o (h * g * h⁻¹) = orbitalFeatures o g := by
  classical
  dsimp [orbitalFeatures]
  calc
    (∑ x : Ω, if orbitalOf (G := G) (x, (h * g * h⁻¹) • x) = o then (1 : ℝ) else 0) =
        ∑ x : Ω, if orbitalOf (G := G) (h • x, (h * g * h⁻¹) • (h • x)) = o
          then (1 : ℝ) else 0 := (Equiv.sum_comp (MulAction.toPerm h) _).symm
    _ = ∑ x : Ω, if orbitalOf (G := G) (x, g • x) = o then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      have hxy : (h • x, (h * g * h⁻¹) • (h • x)) = h • (x, g • x) := by
        simp [mul_smul]
      rw [hxy, orbitalOf_smul]

end
end OrbitalMarginals

-- Source: SharpConstant.lean

open scoped BigOperators
open Set

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I]

def kernelRatios (A : J → I → ℝ) (i : I) : Set ℝ :=
  {r | ∃ v : I → ℝ, Kernel A v ∧ v ≠ 0 ∧ r = |v i| / TV v}

/-- The inserted zero gives the correct value also when the kernel is trivial. -/
def sharpConstant (A : J → I → ℝ) (i : I) : ℝ := sSup (insert 0 (kernelRatios A i))

theorem sharpConstant_eq_optimum (A : J → I → ℝ) (i : I) (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q) (hm : Match A p q)
    (hb : PairBound A i (p i - q i)) : sharpConstant A i = p i - q i := by
  have hC : 0 ≤ p i - q i := by
    have hh := hb uniform uniform uniform_probability uniform_probability (fun _ => rfl)
    simpa only [sub_self] using hh
  have hs := (signedBound_iff_pairBound A i (p i - q i) hC).mpr hb
  have hupper : ∀ r ∈ insert 0 (kernelRatios A i), r ≤ p i - q i := by
    intro r hr
    rcases hr with rfl | hr
    · exact hC
    · obtain ⟨v, hv, hne, rfl⟩ := hr
      exact (div_le_iff₀ (tv_pos v hne)).mpr (hs v hv)
  have hbounded : BddAbove (insert 0 (kernelRatios A i)) := ⟨p i - q i, hupper⟩
  have hnonempty : (insert 0 (kernelRatios A i)).Nonempty := ⟨0, Or.inl rfl⟩
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · by_cases hz : p i - q i = 0
    · rw [hz]
      exact le_csSup hbounded (Or.inl rfl)
    · have hpos : 0 < p i - q i := lt_of_le_of_ne hC (Ne.symm hz)
      have htv := optimal_pair_tv_one A i p q hp hq hm hpos hb
      have hv : (fun g => p g - q g) ≠ 0 := by
        intro he
        have hh := congrFun he i
        exact hz hh
      apply le_csSup hbounded
      right
      refine ⟨(fun g => p g - q g), kernel_of_match A p q hp hq hm, hv, ?_⟩
      simp only [htv, div_one, abs_of_pos hpos]

theorem sharpConstant_trivial_kernel (A : J → I → ℝ) (i : I)
    (h : ∀ v, Kernel A v → v = 0) : sharpConstant A i = 0 := by
  have hr : kernelRatios A i = ∅ := by
    ext r
    constructor
    · rintro ⟨v, hv, hne, _⟩
      exact (hne (h v hv)).elim
    · simp
  simp [sharpConstant, hr]

end
end OrbitalMarginals

-- Source: ClassReduction.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

noncomputable instance : Fintype (ConjClasses G) := Fintype.ofFinite _
noncomputable instance : DecidableEq (ConjClasses G) := Classical.decEq _

def orbitalFeaturesQ (o : Orbitals G Ω) (g : G) : ℚ :=
  ∑ x : Ω, if orbitalOf (G := G) (x, g • x) = o then 1 else 0

theorem cast_orbitalFeaturesQ (o : Orbitals G Ω) (g : G) :
    (orbitalFeaturesQ o g : ℝ) = orbitalFeatures o g := by
  simp only [orbitalFeaturesQ, orbitalFeatures, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> norm_num

def classFeaturesQ (o : Orbitals G Ω) : ConjClasses G → ℚ :=
  Quotient.lift (orbitalFeaturesQ o) (by
    intro g k h
    obtain ⟨s, hs⟩ := isConj_iff.mp h
    apply Rat.cast_injective (α := ℝ)
    simp only [cast_orbitalFeaturesQ]
    rw [← hs, orbitalFeatures_conjugate])

theorem classFeaturesQ_mk (o : Orbitals G Ω) (g : G) :
    classFeaturesQ o (ConjClasses.mk g) = orbitalFeaturesQ o g := rfl

theorem real_classFeatures_mk (o : Orbitals G Ω) (g : G) :
    rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)) o (ConjClasses.mk g) =
      orbitalFeatures o g := cast_orbitalFeaturesQ o g

theorem class_mk_conjugate (h g : G) :
    ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  apply IsConj.symm
  exact isConj_iff.mpr ⟨h, rfl⟩

theorem class_identity_iff (g : G) : ConjClasses.mk g = (1 : ConjClasses G) ↔ g = 1 := by
  rw [ConjClasses.one_eq_mk_one, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]

theorem class_fiber_identity : fiber (ConjClasses.mk : G → ConjClasses G) 1 = {1} := by
  classical
  ext g
  simp [fiber, class_identity_iff]

theorem class_lift_identity (p : ConjClasses G → ℝ) :
    liftLaw ConjClasses.mk p (1 : G) = p 1 := by
  simp [liftLaw, fiberSize, ← ConjClasses.one_eq_mk_one, class_fiber_identity]

theorem class_push_identity (p : G → ℝ) : pushLaw ConjClasses.mk p 1 = p (1 : G) := by
  simp [pushLaw, class_fiber_identity]

theorem class_lift_central (p : ConjClasses G → ℝ) : Central (liftLaw ConjClasses.mk p) := by
  intro h g
  simp only [liftLaw, class_mk_conjugate]

theorem central_class_constant (p : G → ℝ) (hp : Central p) (g k : G)
    (he : ConjClasses.mk g = ConjClasses.mk k) : p g = p k := by
  obtain ⟨h, hh⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he)
  rw [← hh, hp h g]

theorem class_lift_push (p : G → ℝ) (hp : Central p) :
    liftLaw ConjClasses.mk (pushLaw ConjClasses.mk p) = p :=
  liftLaw_pushLaw _ p (central_class_constant p hp)

/-- This matrix is exactly the original mean of the integer orbital counts on
an actual conjugacy class, including its nonzero normalization denominator. -/
theorem class_matrix_is_average (o : Orbitals G Ω) (c : ConjClasses G) :
    (classFeaturesQ o c : ℝ) =
      (∑ g ∈ fiber ConjClasses.mk c, orbitalFeatures o g) / fiberSize ConjClasses.mk c := by
  have hc := fiberSize_pos (ConjClasses.mk : G → ConjClasses G) ConjClasses.mk_surjective c
  have hs : (∑ g ∈ fiber ConjClasses.mk c, orbitalFeatures o g) =
      fiberSize ConjClasses.mk c * (classFeaturesQ o c : ℝ) := by
    calc
      _ = ∑ _g ∈ fiber ConjClasses.mk c, (classFeaturesQ o c : ℝ) := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [← real_classFeatures_mk]
        change (classFeaturesQ o (ConjClasses.mk g) : ℝ) = (classFeaturesQ o c : ℝ)
        rw [(Finset.mem_filter.mp hg).2]
      _ = _ := by simp [fiberSize]
  rw [hs]
  field_simp

theorem class_lift_match (p q : ConjClasses G → ℝ) :
    Match (imageFeatures (G := G) (Ω := Ω)) (liftLaw ConjClasses.mk p) (liftLaw ConjClasses.mk q) ↔
      Match (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω))) p q := by
  rw [central_match_iff_orbital _ _ (class_lift_central p) (class_lift_central q)]
  have he : orbitalFeatures (G := G) (Ω := Ω) =
      fun o g => rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)) o (ConjClasses.mk g) := by
    funext o g
    exact (real_classFeatures_mk o g).symm
  rw [he]
  exact lift_match ConjClasses.mk ConjClasses.mk_surjective _ p q

theorem central_class_match (p q : G → ℝ) (hp : Central p) (hq : Central q) :
    Match (imageFeatures (G := G) (Ω := Ω)) p q ↔
      Match (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (pushLaw ConjClasses.mk p) (pushLaw ConjClasses.mk q) := by
  rw [← class_lift_match, class_lift_push p hp, class_lift_push q hq]

theorem orbital_score_class (coeff : Orbitals G Ω → ℝ) (g : G) :
    dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff g =
      dualScore (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) coeff (ConjClasses.mk g) := by
  classical
  simp only [dualScore, real_classFeatures_mk, class_identity_iff]

theorem class_oscillation (coeff : Orbitals G Ω → ℝ) :
    oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff =
      oscillation (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) coeff := by
  have hmax : scoreMax (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff =
      scoreMax (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) coeff := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro g _
      rw [orbital_score_class]
      exact (score_range _ _ _ _).2
    · apply Finset.sup'_le
      intro c _
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rw [← orbital_score_class]
      exact (score_range _ _ _ _).2
  have hmin : scoreMin (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff =
      scoreMin (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) coeff := by
    apply le_antisymm
    · apply Finset.le_inf'
      intro c _
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rw [← orbital_score_class]
      exact (score_range _ _ _ _).1
    · apply Finset.le_inf'
      intro g _
      rw [orbital_score_class]
      exact (score_range _ _ _ _).1
  simp only [oscillation, hmax, hmin]

end
end OrbitalMarginals

-- Source: UniversalOrbitalTheorem.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

/-- The complete sharp response statement: actual rational optimizers on
conjugacy classes, the actual orbital matrix, the signed-kernel supremum,
all atom locations, and disjoint sharp probability perturbations. -/
theorem universal_orbital_theorem :
    ∃ C : ℚ, ∃ p q : ConjClasses G → ℚ, ∃ coeff : Orbitals G Ω → ℚ,
      0 ≤ C ∧ C ≤ 1 ∧
      Probability (rationalLaw p) ∧ Probability (rationalLaw q) ∧
      Match (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (rationalLaw p) (rationalLaw q) ∧ p 1 - q 1 = C ∧
      (C : ℝ) = sharpConstant (imageFeatures (G := G) (Ω := Ω)) (1 : G) ∧
      (C : ℝ) = oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
        (fun o => (coeff o : ℝ)) ∧
      (C : ℝ) = oscillation (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) (fun o => (coeff o : ℝ)) ∧
      PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (C : ℝ) ∧
      PairBound (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) (C : ℝ) ∧
      (∀ other : Orbitals G Ω → ℝ, (C : ℝ) ≤
        oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) other) ∧
      (∀ σ : G, UniformLawBound (imageFeatures (G := G) (Ω := Ω)) σ (C : ℝ)) ∧
      (let P := liftLaw ConjClasses.mk (rationalLaw p)
       let Q := liftLaw ConjClasses.mk (rationalLaw q)
       Probability P ∧ Probability Q ∧ Central P ∧ Central Q ∧
       Match (imageFeatures (G := G) (Ω := Ω)) P Q ∧ P 1 - Q 1 = (C : ℝ) ∧
       ((0 : ℚ) < C →
         (∀ g, P g = 0 ∨ Q g = 0) ∧
         ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε →
           Probability (fun g => uniform g + δ * (P g - Q g)) ∧
           Match (imageFeatures (G := G) (Ω := Ω))
             (fun g => uniform g + δ * (P g - Q g)) uniform ∧
           TV (fun g => (uniform g + δ * (P g - Q g)) - uniform g) = δ ∧
           (uniform (1 : G) + δ * (P 1 - Q 1)) - uniform (1 : G) = (C : ℝ) * δ)) := by
  classical
  let M := classFeaturesQ (G := G) (Ω := Ω)
  obtain ⟨C, p, q, coeff, a, b, hC, hC1, hp, hq, hm, hobj, hw, hr, hb, _⟩ :=
    exact_rational_primal_dual M (1 : ConjClasses G)
  let P := liftLaw ConjClasses.mk (rationalLaw p)
  let Q := liftLaw ConjClasses.mk (rationalLaw q)
  have hP : Probability P := liftLaw_probability _ ConjClasses.mk_surjective _ hp
  have hQ : Probability Q := liftLaw_probability _ ConjClasses.mk_surjective _ hq
  have hPC : Central P := class_lift_central _
  have hQC : Central Q := class_lift_central _
  have hmatch : Match (imageFeatures (G := G) (Ω := Ω)) P Q :=
    (class_lift_match _ _).mpr hm
  have heq : P 1 - Q 1 = (C : ℝ) := by
    simp only [P, Q, class_lift_identity, rationalLaw]
    exact_mod_cast hobj
  have hwidth : (b : ℝ) - (a : ℝ) = (C : ℝ) := by exact_mod_cast hw
  have horange : ∀ g : G, (a : ℝ) ≤
        dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) (fun o => (coeff o : ℝ)) g ∧
      dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) (fun o => (coeff o : ℝ)) g ≤ (b : ℝ) := by
    intro g
    rw [orbital_score_class]
    exact hr (ConjClasses.mk g)
  have hob : PairBound (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) (C : ℝ) :=
    intervalDual_pairBound _ _ _ ⟨(fun o => (coeff o : ℝ)), a, b, horange, hwidth.le⟩
  have hib : PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (C : ℝ) := by
    intro v w hv hww hmw
    exact hob v w hv hww (match_image_implies_orbital v w hmw)
  have hoptimal : PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (P 1 - Q 1) := by
    rw [heq]
    exact hib
  have hs := sharpConstant_eq_optimum (imageFeatures (G := G) (Ω := Ω)) (1 : G)
    P Q hP hQ hmatch hoptimal
  have ho : (C : ℝ) = oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
      (fun o => (coeff o : ℝ)) := by
    apply le_antisymm
    · rw [← heq]
      exact oscillation_pairBound _ _ _ P Q hP hQ (match_image_implies_orbital P Q hmatch)
    · have hmax : scoreMax (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
          (fun o => (coeff o : ℝ)) ≤ (b : ℝ) :=
        Finset.sup'_le _ _ (fun g _ => (horange g).2)
      have hmin : (a : ℝ) ≤ scoreMin (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
          (fun o => (coeff o : ℝ)) :=
        Finset.le_inf' _ _ (fun g _ => (horange g).1)
      dsimp [oscillation]
      linarith [hwidth]
  refine ⟨C, p, q, coeff, hC, hC1, hp, hq, hm, hobj, ?_, ho, ?_, hib, hb, ?_, ?_, ?_⟩
  · exact (hs.trans heq).symm
  · exact ho.trans (class_oscillation _)
  · intro other
    rw [← heq]
    exact oscillation_pairBound _ _ other P Q hP hQ (match_image_implies_orbital P Q hmatch)
  · exact uniformBound_all_atoms _ ((uniformLawBound_iff_pairBound
      (imageFeatures (G := G) (Ω := Ω)) (1 : G) (C : ℝ) (by exact_mod_cast hC)).mpr hib)
  · refine ⟨hP, hQ, hPC, hQC, hmatch, heq, ?_⟩
    intro hpos
    have hpositive : 0 < P 1 - Q 1 := by rw [heq]; exact_mod_cast hpos
    refine ⟨probability_parts_disjoint_of_tv_one P Q hP hQ
      (optimal_pair_tv_one _ _ P Q hP hQ hmatch hpositive hoptimal), ?_⟩
    simpa only [P, Q, class_lift_identity, rationalLaw, ← Rat.cast_sub, hobj] using positive_optimum_attained_locally
      (imageFeatures (G := G) (Ω := Ω)) (1 : G) P Q hP hQ hmatch hpositive hoptimal

end
end OrbitalMarginals

-- Source: AllAtoms.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

/-- Translation gives equality of the actual kernel-ratio sets, not just a
transported upper bound.  Therefore optimality holds at every atom. -/
theorem kernelRatios_all_atoms (σ : G) :
    kernelRatios (imageFeatures (G := G) (Ω := Ω)) σ =
      kernelRatios (imageFeatures (G := G) (Ω := Ω)) (1 : G) := by
  ext r
  constructor
  · rintro ⟨v, hv, hne, he⟩
    have htne : translate σ v ≠ 0 := by
      intro ht
      have hz : TV v = 0 := by rw [← tv_translate σ v, ht]; simp [TV]
      exact hne ((tv_eq_zero_iff v).mp hz)
    refine ⟨translate σ v, kernel_translate σ v hv, htne, ?_⟩
    simpa only [translate, mul_one, tv_translate] using he
  · rintro ⟨v, hv, hne, he⟩
    have htne : translate σ⁻¹ v ≠ 0 := by
      intro ht
      have hz : TV v = 0 := by rw [← tv_translate σ⁻¹ v, ht]; simp [TV]
      exact hne ((tv_eq_zero_iff v).mp hz)
    refine ⟨translate σ⁻¹ v, kernel_translate σ⁻¹ v hv, htne, ?_⟩
    simpa only [translate, inv_mul_cancel, tv_translate] using he

theorem sharpConstant_all_atoms (σ : G) :
    sharpConstant (imageFeatures (G := G) (Ω := Ω)) σ =
      sharpConstant (imageFeatures (G := G) (Ω := Ω)) (1 : G) := by
  simp only [sharpConstant, kernelRatios_all_atoms]

/-- Every normalized actual kernel vector produces a full interval of sharp
probability perturbations. -/
theorem normalized_kernel_attainment {I J : Type*} [Fintype I] [Nonempty I]
    (A : J → I → ℝ) (i : I) (v : I → ℝ) (C : ℝ)
    (hv : Kernel A v) (htv : TV v = 1) (hi : v i = C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε →
      Probability (fun g => uniform g + δ * v g) ∧
      Match A (fun g => uniform g + δ * v g) uniform ∧
      TV (fun g => (uniform g + δ * v g) - uniform g) = δ ∧
      (uniform i + δ * v i) - uniform i = C * δ := by
  obtain ⟨ε, hε, hprob, _⟩ := kernel_small_perturbation A v hv
  refine ⟨ε, hε, fun δ hδ hle => ⟨
    probability_perturbation_smaller v ε δ hδ hle hprob hv.1,
    perturbation_match A v hv δ, ?_, ?_⟩⟩
  · simp only [add_sub_cancel_left, tv_smul, abs_of_nonneg hδ, htv, mul_one]
  · rw [hi]
    ring

theorem sharp_attainment_all_atoms (p q : G → ℝ) (hp : Probability p) (hq : Probability q)
    (hm : Match (imageFeatures (G := G) (Ω := Ω)) p q)
    (hpos : 0 < p 1 - q 1)
    (hb : PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (p 1 - q 1)) :
    ∀ σ : G, ∃ v : G → ℝ, Kernel (imageFeatures (G := G) (Ω := Ω)) v ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε →
        Probability (fun g => uniform g + δ * v g) ∧
        Match (imageFeatures (G := G) (Ω := Ω)) (fun g => uniform g + δ * v g) uniform ∧
        TV (fun g => (uniform g + δ * v g) - uniform g) = δ ∧
        (uniform σ + δ * v σ) - uniform σ = (p 1 - q 1) * δ := by
  intro σ
  let v := translate σ⁻¹ (fun g => p g - q g)
  have hv := kernel_translate σ⁻¹ _
    (kernel_of_match (imageFeatures (G := G) (Ω := Ω)) p q hp hq hm)
  have ht : TV v = 1 := by
    rw [tv_translate]
    exact optimal_pair_tv_one _ _ p q hp hq hm hpos hb
  have hi : v σ = p 1 - q 1 := by simp [v, translate]
  exact ⟨v, hv, normalized_kernel_attainment _ σ v _ hv ht hi⟩

end
end OrbitalMarginals

-- Source: SpanFormulation.lean

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

def identityIndicator (g : G) : ℝ := by
  classical
  exact if g = 1 then 1 else 0

def functionOscillation (f : G → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.inf' Finset.univ_nonempty f

theorem orbital_span_exact_minimum :
    ∃ φ : G → ℝ,
      φ ∈ Submodule.span ℝ (Set.range (orbitalFeatures (G := G) (Ω := Ω))) ∧
      sharpConstant (imageFeatures (G := G) (Ω := Ω)) (1 : G) =
        functionOscillation (fun g => identityIndicator g - φ g) ∧
      ∀ ψ : G → ℝ, ψ ∈ Submodule.span ℝ (Set.range (orbitalFeatures (G := G) (Ω := Ω))) →
        sharpConstant (imageFeatures (G := G) (Ω := Ω)) (1 : G) ≤
          functionOscillation (fun g => identityIndicator g - ψ g) := by
  classical
  obtain ⟨C, p, q, coeff, _, _, _, _, _, _, hs, ho, _, _, _, hmin, _⟩ :=
    universal_orbital_theorem (G := G) (Ω := Ω)
  let φ : G → ℝ := ∑ o, (coeff o : ℝ) • orbitalFeatures o
  have hφ : φ ∈ Submodule.span ℝ (Set.range (orbitalFeatures (G := G) (Ω := Ω))) := by
    apply Submodule.sum_mem
    intro o _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self o))
  refine ⟨φ, hφ, ?_, ?_⟩
  · have he : φ = fun g => ∑ o, (coeff o : ℝ) * orbitalFeatures o g := by
      funext g
      simp [φ]
    rw [← hs, ho, he]
    rfl
  · intro ψ hψ
    obtain ⟨other, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hψ
    have he' : ψ = fun g => ∑ o, other o * orbitalFeatures o g := by
      rw [← he]
      funext g
      simp
    rw [he', ← hs]
    exact hmin other

end
end OrbitalMarginals

-- Source: Controls.lean

open scoped BigOperators

namespace OrbitalMarginals

/-- With no features on two atoms, the actual sharp coefficient is one. -/
theorem empty_features_nonvacuous :
    sharpConstant (fun _ : Empty => fun _ : Fin 2 => (0 : ℝ)) (0 : Fin 2) = 1 := by
  let p : Fin 2 → ℝ := fun g => if g = 0 then 1 else 0
  let q : Fin 2 → ℝ := fun g => if g = 1 then 1 else 0
  have hp : Probability p := by
    constructor
    · intro g
      dsimp [p]
      split_ifs <;> norm_num
    · norm_num [p, Fin.sum_univ_two]
  have hq : Probability q := by
    constructor
    · intro g
      dsimp [q]
      split_ifs <;> norm_num
    · norm_num [q, Fin.sum_univ_two]
  have hm : Match (fun _ : Empty => fun _ : Fin 2 => (0 : ℝ)) p q := by
    intro j
    cases j
  have hb : PairBound (fun _ : Empty => fun _ : Fin 2 => (0 : ℝ)) (0 : Fin 2) 1 := by
    intro P Q hP hQ _
    have he := hP.2
    rw [Fin.sum_univ_two] at he
    linarith [hP.1 1, hQ.1 0]
  have ho : p 0 - q 0 = 1 := by norm_num [p, q]
  have hb' : PairBound (fun _ : Empty => fun _ : Fin 2 => (0 : ℝ)) (0 : Fin 2) (p 0 - q 0) := by
    rwa [ho]
  exact (sharpConstant_eq_optimum _ _ p q hp hq hm hb').trans ho

/-- A one-atom zero-mass kernel is trivial, giving the actual zero endpoint. -/
theorem one_atom_zero_endpoint :
    sharpConstant (fun _ : Empty => fun _ : Unit => (0 : ℝ)) () = 0 := by
  apply sharpConstant_trivial_kernel
  intro v hv
  funext g
  cases g
  simpa using hv.1

/-- Concrete omitted-hypothesis counterexample: positive mass differs from TV.
Jordan normalization cannot be used without zero total signed mass. -/
theorem jordan_requires_zero_mass :
    TV (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) = 1 / 2 ∧
      (∑ i : Fin 2, jordanP (fun j : Fin 2 => if j = 0 then (1 : ℝ) else 0) i) = 2 := by
  norm_num [TV, jordanP, posPart, Fin.sum_univ_two]

end OrbitalMarginals
