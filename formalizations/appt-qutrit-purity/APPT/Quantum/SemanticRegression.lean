import APPT.Quantum.CornerNecessity
import APPT.Quantum.Attainment

open scoped BigOperators ComplexOrder
open Matrix
namespace APPT.Quantum

section ProductBasis
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- A product-basis pure state, used to distinguish PPT from absolute PPT. -/
def basisPureState (e : a × b) : Matrix (a × b) (a × b) ℂ :=
  Matrix.diagonal (Pi.single e 1)

theorem basisPureState_isDensity (e : a × b) : IsDensity (basisPureState e) := by
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : i = e <;> simp [Pi.single_apply, hi, eq_comm]
  · simp [basisPureState, Matrix.trace_diagonal, Pi.single_apply]

theorem basisPureState_sq (e : a × b) :
    basisPureState e * basisPureState e = basisPureState e := by
  unfold basisPureState
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i = e <;> simp [Pi.single_apply, hi, eq_comm]

theorem basisPureState_partialTranspose (e : a × b) :
    partialTranspose (basisPureState e) = basisPureState e := by
  rcases e with ⟨k,z⟩
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases hij : i=j <;> by_cases hxy : x=y <;>
    simp_all [partialTranspose, basisPureState, Matrix.diagonal_apply, Pi.single_apply]

theorem basisPureState_purity (e : a × b) : purity (basisPureState e) = 1 := by
  unfold purity
  rw [basisPureState_sq, (basisPureState_isDensity e).2]
  rfl

end ProductBasis

/-- Semantic regression for every dimension: the physical APPT condition cannot
be replaced by positivity of just the unrotated partial transpose. This proof
uses corner-unitary necessity and does not assume the maximal-purity theorem. -/
theorem exists_PPT_density_not_APPT (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A ∧ (partialTranspose A).PosSemidef ∧ purity A = 1 ∧
      ¬ AbsolutelyPPT A := by
  let a : Fin 3 → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  let e : Fin 3 × Fin n := (0, a 0)
  refine ⟨basisPureState e, basisPureState_isDensity e, ?_, basisPureState_purity e, ?_⟩
  · rw [basisPureState_partialTranspose]
    exact (basisPureState_isDensity e).1
  · intro hP
    let mu : Fin 3 × Fin n → ℝ := Pi.single e 1
    let x : Fin 9 → Fin 3 × Fin n :=
      ![(0,a 0),(0,a 1),(0,a 2),(1,a 0),(1,a 1),(1,a 2),(2,a 0),(2,a 1),(2,a 2)]
    have ha : Function.Injective a := by
      intro i j hij
      apply Fin.ext
      exact congrArg Fin.val hij
    have hx : Function.Injective x := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [x, a, Fin.ext_iff]
    have hd : AbsolutelyPPT (Matrix.diagonal (fun i => (mu i : ℂ))) := by
      simpa [basisPureState, mu, Pi.single_apply] using hP
    have hc := diagonal_appt_necessary_matrices a ha mu x hx hd
    have hy : mu ∘ x = (![1,0,0,0,0,0,0,0,0] : Fin 9 → ℝ) := by
      funext i
      fin_cases i <;> norm_num [mu, x, e, a, Function.comp_def, Pi.single_apply, Fin.ext_iff]
    have hm := APPT.minorA_nonneg (mu ∘ x) hc.1 0 1
    rw [hy] at hm
    norm_num [APPT.minorA, APPT.matA] at hm

/-- The requested sharp formula is strictly below the pure-state purity. -/
theorem targetPurity_lt_one (n : ℕ) (hn : 3 ≤ n) : targetPurity n < 1 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold targetPurity
  split_ifs
  · have hp : (0 : ℝ) < (3*(n : ℝ)+2)^2 := by positivity
    apply (div_lt_one hp).2
    nlinarith
  · have hp : (0 : ℝ) < 8*(n : ℝ) := by positivity
    apply (div_lt_one hp).2
    linarith

/-- A genuine counterexample to weakening the final theorem's APPT hypothesis
to PPT, uniformly for every n>=3. -/
theorem exists_PPT_density_exceeding_target (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℂ,
      IsDensity A ∧ (partialTranspose A).PosSemidef ∧
      targetPurity n < purity A ∧ ¬ AbsolutelyPPT A := by
  obtain ⟨A,hA,hT,hpur,hnot⟩ := exists_PPT_density_not_APPT n hn
  refine ⟨A,hA,hT,?_,hnot⟩
  rw [hpur]
  exact targetPurity_lt_one n hn

end APPT.Quantum
