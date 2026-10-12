/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealGroups


set_option autoImplicit false


open scoped NumberField WithZero Classical
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-! ### Simultaneous approximation at the places in a modulus -/

/-- The finite primes in `m`, together with all infinite places. -/
abbrev ApproximationPlace (m : Modulus K) :=
  (↥m.finitePart.support) ⊕ InfinitePlace K

/-- The absolute value represented by an approximation place. -/
abbrev approximationAbsoluteValue (m : Modulus K) :
    ApproximationPlace m → AbsoluteValue K ℝ
  | Sum.inl v => NumberField.HeightOneSpectrum.adicAbv K v.1
  | Sum.inr w => w.1

theorem adicAbv_isNontrivial
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.mpr hx0
  · apply ne_of_lt
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv

theorem adicAbv_not_isEquiv_of_ne
    {v w : HeightOneSpectrum (𝓞 K)} (hvw : v ≠ w) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv
      (NumberField.HeightOneSpectrum.adicAbv K w) := by
  intro h
  have hnotle : ¬ v.asIdeal ≤ w.asIdeal := by
    intro hvw_le
    have htop_le : (⊤ : Ideal (𝓞 K)) ≤ w.asIdeal := by
      rw [← (v.isCoprime_of_ne w hvw).sup_eq]
      exact sup_le hvw_le le_rfl
    exact w.isPrime.ne_top (top_unique htop_le)
  obtain ⟨x, hxv, hxw⟩ := Set.not_subset.mp hnotle
  have hvlt :
      NumberField.HeightOneSpectrum.adicAbv K v
        (algebraMap (𝓞 K) K x) < 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv
  have hweq :
      NumberField.HeightOneSpectrum.adicAbv K w
        (algebraMap (𝓞 K) K x) = 1 := by
    rw [← FinitePlace.norm_embedding]
    exact (FinitePlace.norm_eq_one_iff_notMem (K := K) w x).2 hxw
  exact (ne_of_lt hvlt) (h.eq_one_iff.mpr hweq)

theorem adicAbv_not_isEquiv_infinitePlace
    (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro h
  have hle :
      w.1 ((2 : ℕ) : K) ≤ 1 :=
    h.le_one_iff.mp
      (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2)
  have hw :
      w.1 ((2 : ℕ) : K) = (2 : ℝ) :=
    NumberField.InfinitePlace.map_natCast w 2
  have hfalse : (2 : ℝ) ≤ 1 := hw ▸ hle
  norm_num at hfalse

theorem approximationAbsoluteValue_isNontrivial
    (m : Modulus K) :
    ∀ i, (approximationAbsoluteValue m i).IsNontrivial
  | Sum.inl v => by
      change
        (NumberField.HeightOneSpectrum.adicAbv K v.1).IsNontrivial
      exact adicAbv_isNontrivial v.1
  | Sum.inr w => by
      change w.1.IsNontrivial
      exact w.isNontrivial

theorem approximationAbsoluteValue_pairwise
    (m : Modulus K) :
    Pairwise fun i j =>
      ¬ (approximationAbsoluteValue m i).IsEquiv
        (approximationAbsoluteValue m j) := by
  intro i j hij
  cases i with
  | inl v =>
      cases j with
      | inl w =>
          apply adicAbv_not_isEquiv_of_ne
          intro hvw
          apply hij
          exact congrArg Sum.inl (Subtype.ext hvw)
      | inr w =>
          exact adicAbv_not_isEquiv_infinitePlace v.1 w
  | inr v =>
      cases j with
      | inl w =>
          exact fun h =>
            adicAbv_not_isEquiv_infinitePlace w.1 v h.symm
      | inr w =>
          intro h
          apply hij
          congr
          change v.1.IsEquiv w.1 at h
          exact
            (InfinitePlace.eq_iff_isEquiv (K := K)).mpr h

/-- The corresponding product of local completions. -/
abbrev approximationCompletion (m : Modulus K) :
    ApproximationPlace m → Type _
  | Sum.inl v => v.1.adicCompletion K
  | Sum.inr w => w.Completion

noncomputable instance approximationCompletionTopologicalSpace
    (m : Modulus K) (i : ApproximationPlace m) :
    TopologicalSpace (approximationCompletion m i) := by
  cases i <;> simp only [approximationCompletion] <;> infer_instance

/-- Coordinatewise completion of the valued copies of `K`. -/
def approximationCompletionMap (m : Modulus K) :
    ∀ i : ApproximationPlace m,
      WithAbs (approximationAbsoluteValue m i) →
        approximationCompletion m i
  | Sum.inl v =>
      fun x =>
        FinitePlace.embedding v.1
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v.1) x)
  | Sum.inr w => fun x => (x : w.Completion)

theorem denseRange_finiteApproximationCompletionMap
    (v : HeightOneSpectrum (𝓞 K)) :
    DenseRange
      (fun x :
          WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
        FinitePlace.embedding v
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x)) := by
  have hrange :
      Set.range
          (fun x :
              WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
            FinitePlace.embedding v
              (WithAbs.equiv
                (NumberField.HeightOneSpectrum.adicAbv K v) x)) =
        Set.range (algebraMap K (v.adicCompletion K)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact
        ⟨WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine
        ⟨(WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v)).symm x, ?_⟩
      rfl
  rw [DenseRange, hrange]
  exact v.denseRange_algebraMap K

theorem continuous_finiteApproximationCompletionMap
    (v : HeightOneSpectrum (𝓞 K)) :
    Continuous
      (fun x :
          WithAbs (NumberField.HeightOneSpectrum.adicAbv K v) =>
        FinitePlace.embedding v
          (WithAbs.equiv
            (NumberField.HeightOneSpectrum.adicAbv K v) x)) := by
  apply Isometry.continuous
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub,
    FinitePlace.norm_embedding]
  rfl

theorem denseRange_approximationCompletionMap
    (m : Modulus K) :
    ∀ i, DenseRange (approximationCompletionMap m i)
  | Sum.inl v => denseRange_finiteApproximationCompletionMap v.1
  | Sum.inr w =>
      NumberField.InfinitePlace.Completion.denseRange_coe w

theorem continuous_approximationCompletionMap
    (m : Modulus K) :
    ∀ i, Continuous (approximationCompletionMap m i)
  | Sum.inl v => continuous_finiteApproximationCompletionMap v.1
  | Sum.inr w =>
      NumberField.InfinitePlace.Completion.continuous_coe w

/-- The diagonal embedding into the finite product of the relevant
completions. -/
def approximationEmbedding (m : Modulus K) :
    K → (i : ApproximationPlace m) → approximationCompletion m i :=
  (Pi.map (approximationCompletionMap m)) ∘
    algebraMap K
      ((i : ApproximationPlace m) →
        WithAbs (approximationAbsoluteValue m i))

@[simp]
theorem approximationEmbedding_finite
    (m : Modulus K) (x : K) (v : ↥m.finitePart.support) :
    approximationEmbedding m x (Sum.inl v) =
      FinitePlace.embedding v.1 x :=
  rfl

@[simp]
theorem approximationEmbedding_infinite
    (m : Modulus K) (x : K) (w : InfinitePlace K) :
    approximationEmbedding m x (Sum.inr w) =
      (x : w.Completion) :=
  rfl

theorem denseRange_approximationEmbedding (m : Modulus K) :
    DenseRange (approximationEmbedding m) := by
  exact
    (DenseRange.piMap
      (denseRange_approximationCompletionMap m)).comp
      (AbsoluteValue.denseRange_algebraMap_pi
        (approximationAbsoluteValue_isNontrivial m)
        (approximationAbsoluteValue_pairwise m))
      (.piMap (continuous_approximationCompletionMap m))

/-- The open set of field elements whose ratio with a fixed unit lies in
a prescribed open unit set. -/
def unitRatioSet
    {F : Type*} [Field F] (a : Fˣ) (U : Subgroup Fˣ) :
    Set F :=
  Units.val '' (fun y : Fˣ => a * y⁻¹) ⁻¹' (U : Set Fˣ)

/-- The unit-ratio set associated to an open set of units is open. -/
theorem isOpen_unitRatioSet
    {F : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalRing F] [ContinuousInv₀ F] [T1Space F]
    (a : Fˣ) (U : Subgroup Fˣ)
    (hU : IsOpen (U : Set Fˣ)) :
    IsOpen (unitRatioSet a U) := by
  apply IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap
  exact hU.preimage (continuous_const.mul continuous_inv)

/-- The value of the distinguished unit belongs to its unit-ratio set. -/
theorem val_mem_unitRatioSet
    {F : Type*} [Field F] (a : Fˣ) (U : Subgroup Fˣ) :
    (a : F) ∈ unitRatioSet a U := by
  exact ⟨a, by simp, rfl⟩

/-- The open local conditions that make `a / x` prime to `m`. -/
def approximationTarget (m : Modulus K) (a : IdeleGroup K) :
    ∀ i : ApproximationPlace m, Set (approximationCompletion m i)
  | Sum.inl v =>
      unitRatioSet (a.2 v.1)
        (localHigherUnitGroup v.1 (m.finitePart v.1))
  | Sum.inr w =>
      unitRatioSet
        (ContinuousMulEquiv.piUnits a.1 w)
        (m.localInfiniteCongruenceSubgroup w)

theorem isOpen_approximationTarget
    (m : Modulus K) (a : IdeleGroup K) :
    ∀ i, IsOpen (approximationTarget m a i)
  | Sum.inl v => by
      change IsOpen
        (unitRatioSet (a.2 v.1)
          (localHigherUnitGroup v.1 (m.finitePart v.1)))
      exact isOpen_unitRatioSet _ _
        (isOpen_localHigherUnitGroup v.1 (m.finitePart v.1))
  | Sum.inr w => by
      change IsOpen
        (unitRatioSet
          (ContinuousMulEquiv.piUnits a.1 w)
          (m.localInfiniteCongruenceSubgroup w))
      apply isOpen_unitRatioSet _ _
      classical
      by_cases hw : w.IsReal
      · by_cases hmem : (⟨w, hw⟩ : RealPlace K) ∈ m.infinitePart
        · rw [Modulus.localInfiniteCongruenceSubgroup,
            dite_eq_left hw, dite_eq_left hmem]
          exact isOpen_infinitePositiveSubgroup w
        · rw [Modulus.localInfiniteCongruenceSubgroup,
            dite_eq_left hw, dite_eq_right hmem]
          exact isOpen_univ
      · rw [Modulus.localInfiniteCongruenceSubgroup, dite_eq_right hw]
        exact isOpen_univ

/-- The given idele itself lies in the product of its approximation
neighborhoods. -/
def approximationTargetPoint
    (m : Modulus K) (a : IdeleGroup K) :
    (i : ApproximationPlace m) → approximationCompletion m i
  | Sum.inl v => (a.2 v.1 : v.1.adicCompletion K)
  | Sum.inr w =>
      (ContinuousMulEquiv.piUnits a.1 w : w.Completion)

theorem approximationTargetPoint_mem
    (m : Modulus K) (a : IdeleGroup K) :
    approximationTargetPoint m a ∈
      Set.univ.pi (approximationTarget m a) := by
  intro i _hi
  cases i with
  | inl v =>
      exact val_mem_unitRatioSet _ _
  | inr w =>
      exact val_mem_unitRatioSet _ _


end RayClass
