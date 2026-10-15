import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Choose

/-! One strictly positive rational input/output weighting separates any finite
family of distinct real matrices. This is an existence proof in exact algebra,
not a randomized numerical claim or an unverified sensor-design solver. -/
open Matrix
noncomputable section
namespace HydrologyTree

/-- An explicit infinite set of positive rational weights in (1,2). -/
def boundedProbeWeight (n : ℕ) : ℝ := 1+((n : ℝ)+2)⁻¹

lemma boundedProbeWeight_bounds (n : ℕ) : 1<boundedProbeWeight n ∧ boundedProbeWeight n<2 := by
  have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
  have hd : 0<(n : ℝ)+2 := by linarith
  have hp := inv_pos.mpr hd
  have hl : ((n : ℝ)+2)⁻¹<1 := (inv_lt_one₀ hd).mpr (by linarith)
  dsimp only [boundedProbeWeight]
  constructor <;> linarith

lemma boundedProbeWeight_injective : Function.Injective boundedProbeWeight := by
  intro n m h
  have h1 : ((n : ℝ)+2)⁻¹=((m : ℝ)+2)⁻¹ := add_left_cancel h
  have h2 := inv_injective h1
  have h3 : (n : ℝ)=(m : ℝ) := add_right_cancel h2
  exact_mod_cast h3

variable {V : Type*} [Fintype V] [DecidableEq V]

def matrixProbeValue (A : Matrix V V ℝ) (b c : V → ℝ) : ℝ :=
  ∑ i,c i*(A*ᵥb) i

/-- Encode every original matrix entry in its own bilinear monomial. -/
def matrixProbePolynomial (A : Matrix V V ℝ) : MvPolynomial (V ⊕ V) ℝ :=
  ∑ i,∑ j,MvPolynomial.C (A i j)*MvPolynomial.X (.inl i)*MvPolynomial.X (.inr j)

lemma matrixProbePolynomial_eval (A : Matrix V V ℝ) (z : V ⊕ V → ℝ) :
    MvPolynomial.eval z (matrixProbePolynomial A)=
      matrixProbeValue A (fun j => z (.inr j)) (fun i => z (.inl i)) := by
  simp only [matrixProbePolynomial,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,
    matrixProbeValue,Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma matrixProbePolynomial_basis (A : Matrix V V ℝ) (i j : V) :
    MvPolynomial.eval (Sum.elim (Pi.single i 1) (Pi.single j 1)) (matrixProbePolynomial A)=A i j := by
  rw [matrixProbePolynomial_eval]
  simp [matrixProbeValue,Matrix.mulVec,dotProduct,Pi.single_apply]

lemma matrixProbePolynomial_injective : Function.Injective (matrixProbePolynomial (V := V)) := by
  intro A B h
  ext i j
  have he := congrArg (MvPolynomial.eval (Sum.elim (Pi.single i 1) (Pi.single j 1))) h
  simpa only [matrixProbePolynomial_basis] using he

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- One pair of explicitly rational, strictly positive coordinate weightings
separates EVERY member of any finite injectively labelled matrix family.
This is adaptive to the candidate family, not one universal fixed probe. -/
theorem exists_positive_rational_matrix_probe (A : K → Matrix V V ℝ)
    (hA : Function.Injective A) :
    ∃ b c : V → ℕ, Function.Injective (fun k =>
      matrixProbeValue (A k) (fun v => boundedProbeWeight (b v)) (fun v => boundedProbeWeight (c v))) := by
  let D (i j : K) : MvPolynomial (V ⊕ V) ℝ :=
    if i=j then 1 else matrixProbePolynomial (A i)-matrixProbePolynomial (A j)
  have hD (i j : K) : D i j ≠ 0 := by
    dsimp only [D]
    split_ifs with hij
    · exact one_ne_zero
    · exact sub_ne_zero.mpr (fun h => hij (hA (matrixProbePolynomial_injective h)))
  let Q : MvPolynomial (V ⊕ V) ℝ := ∏ i,∏ j,D i j
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ =>
    Finset.prod_ne_zero_iff.mpr (fun j _ => hD i j))
  let S : Set ℝ := Set.range boundedProbeWeight
  have hS : S.Infinite := Set.infinite_range_of_injective boundedProbeWeight_injective
  have hex : ∃ z : V ⊕ V → ℝ,(∀ k,z k∈S) ∧ MvPolynomial.eval z Q ≠ 0 := by
    by_contra hn
    apply hQ
    apply MvPolynomial.funext_set (fun _ => S) (fun _ => hS)
    intro z hz
    have he : MvPolynomial.eval z Q=0 := by
      by_contra hne
      exact hn ⟨z,fun k => hz k (Set.mem_univ k),hne⟩
    simpa only [map_zero] using he
  obtain ⟨z,hz,hzQ⟩ := hex
  choose f hf using hz
  refine ⟨(fun v => f (.inr v)),(fun v => f (.inl v)),?_⟩
  intro i j he
  by_contra hij
  have hprod : (∏ i : K,∏ j : K,MvPolynomial.eval z (D i j)) ≠ 0 := by
    simpa only [Q,map_prod] using hzQ
  have hd := (Finset.prod_ne_zero_iff.mp
    ((Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i))) j (Finset.mem_univ j)
  apply hd
  simp only [D,if_neg hij,map_sub,matrixProbePolynomial_eval]
  apply sub_eq_zero.mpr
  simpa only [hf] using he

end HydrologyTree
