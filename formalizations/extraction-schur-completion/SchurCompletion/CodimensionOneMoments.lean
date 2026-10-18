import SchurCompletion.SymmetricHaarBlock
import SchurCompletion.HaarPurity
import SchurCompletion.CyclePositive
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecificLimits.Normed

open scoped BigOperators ComplexOrder Topology Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

/-- Every actual rank-one density has the same literal Haar average. -/
theorem haarOrbitAverage_rank_one (D k : ℕ) (hD : 0 < D)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hr : X.rank = 1) : haarOrbitAverage D k X = symmetricState D k := by
  let Ω := haarOrbitAverage D k X
  have hs : symmetricProjector D k * Ω = Ω := by
    simpa only [hr, rankBudgetProjector_one_eq_symmetricProjector] using
      haarOrbitAverage_common_support D k X
  have hΩ : Ω.IsHermitian := (haarOrbitAverage_density D k X hX).1.isHermitian
  have ht := congrArg Matrix.conjTranspose hs
  have hrΩ : Ω * symmetricProjector D k = Ω := by
    simpa only [Matrix.conjTranspose_mul, (symmetricProjector_hermitian D k).eq,
      hΩ.eq] using ht
  obtain ⟨a, ha⟩ := permutationSpan_symmetric_scalar D k Ω
    (haarOrbitAverage_mem_permutationSpan D k X)
  rw [hrΩ] at ha
  have hn : (Fintype.card (Sym (Fin D) k) : ℂ) ≠ 0 := by
    exact_mod_cast (occupation_card_pos D k hD).ne'
  have ht := congrArg Matrix.trace ha
  rw [(haarOrbitAverage_density D k X hX).2, Matrix.trace_smul,
    symmetricProjector_trace, smul_eq_mul] at ht
  have ha' : a = (Fintype.card (Sym (Fin D) k) : ℂ)⁻¹ := by
    apply (mul_right_cancel₀ hn)
    rw [inv_mul_cancel₀ hn]
    exact ht.symm
  change Ω = _
  rw [ha, ha', symmetricState, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp

def coordinatePureProjection (D : ℕ) (a : Fin D) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.diagonal (Pi.single a 1)

theorem coordinatePureProjection_eq_single (D : ℕ) (a : Fin D) :
    coordinatePureProjection D a = Matrix.single a a 1 := by
  ext i j
  by_cases hi : a = i <;> by_cases hj : a = j <;>
    simp_all [coordinatePureProjection, Matrix.diagonal_apply, Matrix.single,
      Pi.single_apply, eq_comm]

theorem coordinatePureProjection_density (D : ℕ) (a : Fin D) :
    (coordinatePureProjection D a).PosSemidef ∧
      (coordinatePureProjection D a).trace = 1 := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    simp only [Pi.zero_apply, Pi.single_apply]
    split_ifs <;> positivity
  · simp [coordinatePureProjection]

theorem coordinatePureProjection_rank (D : ℕ) (a : Fin D) :
    (coordinatePureProjection D a).rank = 1 := by
  rw [coordinatePureProjection, Matrix.rank_diagonal]
  simp [Pi.single_apply]

theorem symmetricProjector_constant_diagonal (D k : ℕ) (a : Fin D) :
    symmetricProjector D k (fun _ => a) (fun _ => a) = 1 := by
  rw [symmetricProjector_eq_copyPermutationAverage]
  simp [copyPermutationAverage, Matrix.smul_apply, Matrix.sum_apply,
    copyPermutationMatrix_apply, Function.comp_def]

def matrixEntryLinear {ι : Type*} (i j : ι) : Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem haarOrbitAverage_entry (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ)
    (v w : Word D k) :
    haarOrbitAverage D k X v w =
      ∫ U, orbitTensor D k X U v w ∂unitaryHaar D := by
  exact ((matrixEntryLinear v w).toContinuousLinearMap.integral_comp_comm
    (integrable_orbitTensor D k X)).symm

/-- Exact Haar moments of one genuine unitary entry, derived from the
rank-one Haar average, with no moment or design hypothesis. -/
theorem unitary_entry_power_moment (D k : ℕ) (a b : Fin D) :
    (∫ U : OneCopyUnitary D,
      (((U : Matrix (Fin D) (Fin D) ℂ) * coordinatePureProjection D a *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) b b) ^ k ∂unitaryHaar D) =
      ((D+k-1).choose k : ℂ)⁻¹ := by
  have hD : 0 < D := Nat.zero_lt_of_lt a.isLt
  have h := congrArg (fun M : Matrix (Word D k) (Word D k) ℂ =>
      M (fun _ => b) (fun _ => b))
    (haarOrbitAverage_rank_one D k hD (coordinatePureProjection D a)
      (coordinatePureProjection_density D a) (coordinatePureProjection_rank D a))
  rw [haarOrbitAverage_entry] at h
  simpa [orbitTensor, tensorMatrix, symmetricState,
    symmetricProjector_constant_diagonal, Sym.card_sym_eq_choose,
    RCLike.real_smul_eq_coe_mul] using h

theorem coordinateRankProjection_codimension_one (s : ℕ) :
    coordinateRankProjection (s+1) s (Nat.le_succ s) =
      1 - coordinatePureProjection (s+1) (Fin.last s) := by
  ext i j
  change (∑ x : Fin s, (if i = x.castSucc then (1 : ℂ) else 0) *
    star (if j = x.castSucc then (1 : ℂ) else 0)) =
      (1 : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) i j -
        coordinatePureProjection (s+1) (Fin.last s) i j
  simp only [apply_ite star, star_one, star_zero]
  induction i using Fin.lastCases with
  | last =>
    simp [coordinatePureProjection, Matrix.diagonal_apply, Pi.single_apply,
      Matrix.one_apply, eq_comm]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp [coordinatePureProjection, Matrix.diagonal_apply, Pi.single_apply,
        Matrix.one_apply, eq_comm]
    | cast j =>
      simp [coordinatePureProjection, Matrix.diagonal_apply, Pi.single_apply,
        Matrix.one_apply, ite_mul, eq_comm]


def unitaryPureEntry (D : ℕ) (a b : Fin D) (U : OneCopyUnitary D) : ℂ :=
  (((U : Matrix (Fin D) (Fin D) ℂ) * coordinatePureProjection D a *
    (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) b b)

theorem continuous_unitaryPureEntry (D : ℕ) (a b : Fin D) :
    Continuous (unitaryPureEntry D a b) := by
  unfold unitaryPureEntry
  fun_prop

theorem integral_unitaryPureEntry_pow (D k : ℕ) (a b : Fin D) :
    (∫ U, unitaryPureEntry D a b U ^ k ∂unitaryHaar D) =
      ((D+k-1).choose k : ℂ)⁻¹ :=
  unitary_entry_power_moment D k a b

/-- All shifted scalar moments follow from the actual Haar entry moments. -/
theorem integral_shifted_unitaryPureEntry_pow (D k : ℕ) (a b : Fin D) (z : ℂ) :
    (∫ U, (unitaryPureEntry D a b U + z) ^ k ∂unitaryHaar D) =
      ∑ j ∈ Finset.range (k+1),
        ((D+j-1).choose j : ℂ)⁻¹ * z ^ (k-j) * (k.choose j : ℂ) := by
  simp_rw [add_pow]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_const, integral_mul_const, integral_unitaryPureEntry_pow]
  · intro j hj
    exact ((((continuous_unitaryPureEntry D a b).pow j).mul continuous_const).mul
      continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem coordinatePureProjection_trace_mul (D : ℕ) (a : Fin D)
    (A : Matrix (Fin D) (Fin D) ℂ) :
    (coordinatePureProjection D a * A).trace = A a a := by
  rw [Matrix.trace_mul_comm, coordinatePureProjection_eq_single,
    Matrix.trace_mul_single]
  simp

/-- The exact overlap of two genuine codimension-one coordinate subspaces. -/
theorem coordinateRankProjection_codimension_one_overlap (s : ℕ)
    (U : OneCopyUnitary (s+1)) :
    (coordinateRankProjection (s+1) s (Nat.le_succ s) *
      ((U : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) *
        coordinateRankProjection (s+1) s (Nat.le_succ s) *
        (U : Matrix (Fin (s+1)) (Fin (s+1)) ℂ)ᴴ)).trace =
      unitaryPureEntry (s+1) (Fin.last s) (Fin.last s) U + (s : ℂ) - 1 := by
  let A : Matrix (Fin (s+1)) (Fin (s+1)) ℂ := U
  let E := coordinatePureProjection (s+1) (Fin.last s)
  have hU : A * Aᴴ = 1 := U.prop.2
  have hU' : Aᴴ * A = 1 := U.prop.1
  have hT : (A * E * Aᴴ).trace = 1 := by
    rw [Matrix.trace_mul_cycle, hU', Matrix.one_mul]
    exact (coordinatePureProjection_density (s+1) (Fin.last s)).2
  rw [coordinateRankProjection_codimension_one]
  change ((1-E) * (A * (1-E) * Aᴴ)).trace = _
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hU,
    Matrix.trace_sub, hT]
  rw [coordinatePureProjection_trace_mul]
  simp only [Matrix.trace_one, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hE : E.trace = 1 := (coordinatePureProjection_density (s+1) (Fin.last s)).2
  rw [hE]
  dsimp [unitaryPureEntry, A, E]
  ring

/-- Closed finite binomial formula for the actual Haar average's purity in
codimension one. This uses no Schur spectrum or assumed moment law. -/
theorem flatHaarAverage_codimension_one_purity (s k : ℕ) :
    (flatHaarAverage (s+1) s k (Nat.le_succ s) *
      flatHaarAverage (s+1) s k (Nat.le_succ s)).trace =
      ((s : ℂ)⁻¹ ^ 2) ^ k *
        ∑ j ∈ Finset.range (k+1),
          ((s+j).choose j : ℂ)⁻¹ * ((s : ℂ)-1) ^ (k-j) * (k.choose j : ℂ) := by
  rw [flatHaarAverage, haarOrbitAverage_trace_square]
  have he (U : OneCopyUnitary (s+1)) :
      (flatCoordinateDensity (s+1) s (Nat.le_succ s) *
        ((U : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) *
          flatCoordinateDensity (s+1) s (Nat.le_succ s) *
          (U : Matrix (Fin (s+1)) (Fin (s+1)) ℂ)ᴴ)).trace =
        (s : ℂ)⁻¹ ^ 2 *
          (unitaryPureEntry (s+1) (Fin.last s) (Fin.last s) U + ((s : ℂ)-1)) := by
    simp only [flatCoordinateDensity, normalizedProjection, coordinateRankProjection_rank,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv, RCLike.ofReal_natCast]
    rw [coordinateRankProjection_codimension_one_overlap]
    ring
  simp_rw [he, mul_pow]
  rw [integral_const_mul, integral_shifted_unitaryPureEntry_pow]
  congr 2
  funext j
  rw [show s+1+j-1 = s+j by omega]

end
end ExtractionSchur
