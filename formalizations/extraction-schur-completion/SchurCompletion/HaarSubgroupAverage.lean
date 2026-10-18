import SchurCompletion.ColumnProjectionMoments
import SchurCompletion.GramUnitary
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false

def fixFirstMatrix (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  Matrix.of (Fin.cons (Fin.cons 1 (fun _ => 0)) (fun i => Fin.cons 0 (A i)))

theorem fixFirstMatrix_unitary (n : ℕ) (U : OneCopyUnitary n) :
    fixFirstMatrix n (U : Matrix (Fin n) (Fin n) ℂ) ∈
      Matrix.unitaryGroup (Fin (n+1)) ℂ := by
  constructor
  · ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    all_goals
      simp [Matrix.star_eq_conjTranspose, fixFirstMatrix, Matrix.of_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        star_one, star_zero, mul_zero, zero_mul, one_mul, mul_one, Finset.sum_const_zero,
        zero_add, add_zero, Matrix.one_apply, Fin.succ_ne_zero, ne_comm]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.succ_inj, Complex.star_def] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) U.prop.1
  · ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    all_goals
      simp [Matrix.star_eq_conjTranspose, fixFirstMatrix, Matrix.of_apply, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        star_one, star_zero, mul_zero, zero_mul, one_mul, mul_one, Finset.sum_const_zero,
        zero_add, add_zero, Matrix.one_apply, Fin.succ_ne_zero, ne_comm]
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.succ_inj, Complex.star_def] using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) U.prop.2

def fixFirstUnitary (n : ℕ) (U : OneCopyUnitary n) : OneCopyUnitary (n+1) :=
  ⟨fixFirstMatrix n U, fixFirstMatrix_unitary n U⟩

theorem continuous_fixFirstUnitary (n : ℕ) : Continuous (fixFirstUnitary n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp only [fixFirstMatrix, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
  all_goals first | fun_prop | exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))

instance unitaryHaar_isMulRightInvariant (D : ℕ) :
    MeasureTheory.Measure.IsMulRightInvariant (unitaryHaar D) := by
  constructor
  intro g
  let ν := (unitaryHaar D).map (fun U => U*g)
  have hν : ν Set.univ = 1 := by
    simp only [ν, Measure.map_apply (by fun_prop : Measurable (fun U : OneCopyUnitary D => U*g))
      MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have h := Measure.isMulLeftInvariant_eq_smul ν (unitaryHaar D)
  have ht := congrArg (fun μ : Measure (OneCopyUnitary D) => μ Set.univ) h
  have hc : Measure.haarScalarFactor ν (unitaryHaar D) = 1 := by
    simpa [hν] using ht.symm
  rw [hc, one_smul] at h
  exact h

/-- Averaging a continuous observable first over any continuously embedded
unitary family preserves its genuine Haar integral. No conditional Haar law
or subgroup-invariance certificate is supplied by the caller. -/
theorem unitaryHaar_right_double_average (D n : ℕ)
    (φ : OneCopyUnitary n → OneCopyUnitary D) (hφ : Continuous φ)
    (f : OneCopyUnitary D → ℂ) (hf : Continuous f) :
    (∫ U, ∫ V, f (U * φ V) ∂unitaryHaar n ∂unitaryHaar D) =
      ∫ U, f U ∂unitaryHaar D := by
  have hc : Continuous (fun p : OneCopyUnitary D × OneCopyUnitary n =>
      f (p.1 * φ p.2)) := hf.comp (continuous_fst.mul (hφ.comp continuous_snd))
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (unitaryHaar D).prod (unitaryHaar n))
  rw [integral_integral_swap hi]
  simp only [integral_mul_right_eq_self, integral_const, probReal_univ, one_smul]

def columnEnergy {n : ℕ} (b : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (b i)

theorem columnEnergy_nonneg {n : ℕ} (b : Fin n → ℂ) : 0 ≤ columnEnergy b := by
  exact Finset.sum_nonneg (fun i hi => Complex.normSq_nonneg (b i))

theorem exists_unitary_align_column (n : ℕ) (b : Fin (n+1) → ℂ) :
    ∃ W : OneCopyUnitary (n+1),
      ∀ i, ((W : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) *ᵥ b) i =
        if i = 0 then (Real.sqrt (columnEnergy b) : ℂ) else 0 := by
  let X : Matrix (Fin (n+1)) (Fin 1) ℂ := Matrix.of fun i _ =>
    if i = 0 then (Real.sqrt (columnEnergy b) : ℂ) else 0
  let Y : Matrix (Fin (n+1)) (Fin 1) ℂ := Matrix.of fun i _ => b i
  have hsum : (∑ i, star (b i) * b i) = (columnEnergy b : ℂ) := by
    simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum, columnEnergy]
  have hGram : Xᴴ * X = Yᴴ * Y := by
    ext i j
    change (∑ x, star (X x i) * X x j) = ∑ x, star (Y x i) * Y x j
    dsimp only [X, Y, Matrix.of_apply]
    rw [hsum]
    simp only [apply_ite star, map_zero, Complex.star_def, Complex.conj_ofReal, ite_mul, zero_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    norm_cast
    exact Real.mul_self_sqrt (columnEnergy_nonneg b)
  obtain ⟨W,hW⟩ := exists_unitary_mul_of_equal_gram X Y hGram
  refine ⟨W,?_⟩
  intro i
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin 1) ℂ => M i 0) hW
  exact h

end
end ExtractionSchur
