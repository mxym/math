import Attainment
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas

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
