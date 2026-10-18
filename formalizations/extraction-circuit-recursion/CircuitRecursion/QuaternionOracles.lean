import CircuitRecursion.HalfAngleEvaluation
import Mathlib.Data.Vector.Basic

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
namespace CircuitRecursion

noncomputable def quaternionCoordinates (U : SU2) : Fin 4 → ℝ :=
  ![(U.val 0 0).re,(U.val 0 0).im,(U.val 0 1).re,(U.val 0 1).im]

theorem quaternionCoordinates_bound (U : SU2) (i : Fin 4) :
    |quaternionCoordinates U i|≤1 := by
  have hm := su2_mass U
  simp only [Complex.normSq_apply] at hm
  rw [abs_le]
  fin_cases i <;> simp [quaternionCoordinates] <;>
    constructor <;> nlinarith [sq_nonneg (U.val 0 0).re,sq_nonneg (U.val 0 0).im,
      sq_nonneg (U.val 0 1).re,sq_nonneg (U.val 0 1).im]

def quaternionRight : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0]]

def quaternionSign : Fin 4 → Fin 4 → ℤ :=
  ![![1,-1,-1,-1],![1,1,1,-1],![1,-1,1,1],![1,1,-1,1]]

def quaternionProduct {R : Type*} [CommRing R] (a b : Fin 4 → R) (i : Fin 4) : R :=
  ∑ j,(quaternionSign i j:R)*a j*b (quaternionRight i j)

theorem quaternionCoordinates_mul (U V : SU2) :
    quaternionCoordinates (U*V)=quaternionProduct (quaternionCoordinates U) (quaternionCoordinates V) := by
  funext i
  fin_cases i <;>
    simp [quaternionCoordinates,quaternionProduct,quaternionSign,quaternionRight,
      Fin.sum_univ_succ,Matrix.mul_apply,Fin.sum_univ_two,su2_lower_left,su2_lower_right,
      Complex.mul_re,Complex.mul_im] <;> ring

theorem quaternionSign_abs (i j : Fin 4) : |(quaternionSign i j:ℝ)|=1 := by
  fin_cases i <;> fin_cases j <;> norm_num [quaternionSign]

theorem unit_product_error (a b x y δ : ℝ) (hδ0 : 0≤δ) (hδ1 : δ≤1)
    (hx : |x|≤1) (hy : |y|≤1) (ha : |a-x|≤δ) (hb : |b-y|≤δ) :
    |a*b-x*y|≤3*δ := by
  have ha2 : |a|≤2 := by
    have ht := abs_add_le (a-x) x
    rw [sub_add_cancel] at ht
    linarith
  have hid : a*b-x*y=a*(b-y)+y*(a-x) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have h₁ := mul_le_mul ha2 hb (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  have h₂ := mul_le_mul hy ha (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  linarith

theorem quaternionProduct_error (a b x y : Fin 4 → ℝ) (δ : ℝ)
    (hδ0 : 0≤δ) (hδ1 : δ≤1) (hx : ∀ j,|x j|≤1) (hy : ∀ j,|y j|≤1)
    (ha : ∀ j,|a j-x j|≤δ) (hb : ∀ j,|b j-y j|≤δ) (i : Fin 4) :
    |quaternionProduct a b i-quaternionProduct x y i|≤12*δ := by
  unfold quaternionProduct
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hs : (∑ j : Fin 4,|(quaternionSign i j:ℝ)*a j*b (quaternionRight i j)-
      (quaternionSign i j:ℝ)*x j*y (quaternionRight i j)|)≤∑ _j : Fin 4,3*δ := by
    apply Finset.sum_le_sum
    intro j hj
    have hid : (quaternionSign i j:ℝ)*a j*b (quaternionRight i j)-
      (quaternionSign i j:ℝ)*x j*y (quaternionRight i j)=
      (quaternionSign i j:ℝ)*(a j*b (quaternionRight i j)-x j*y (quaternionRight i j)) := by ring
    rw [hid,abs_mul,quaternionSign_abs,one_mul]
    exact unit_product_error _ _ _ _ _ hδ0 hδ1 (hx _) (hy _) (ha _) (hb _)
  exact hs.trans_eq (by norm_num; ring)

/-- A query returns a stored four-coordinate packet, rather than four
recursively re-evaluated scalar oracles. Its cost belongs to the explicitly
supplied input oracle; no polynomial running time is built into this type. -/
abbrev QuaternionOracle := ℕ → List.Vector ℚ 4

def QApproximates (f : QuaternionOracle) (U : SU2) : Prop :=
  ∀ p i,|((f p).get i:ℝ)-quaternionCoordinates U i|≤(1/2:ℝ)^p

def quaternionOracleMul (f g : QuaternionOracle) (p : ℕ) : List.Vector ℚ 4 :=
  let a := f (p+4)
  let b := g (p+4)
  List.Vector.ofFn (quaternionProduct a.get b.get)

theorem quaternionProduct_cast (a b : Fin 4 → ℚ) (i : Fin 4) :
    ((quaternionProduct a b i:ℚ):ℝ)=
      quaternionProduct (fun j => (a j:ℝ)) (fun j => (b j:ℝ)) i := by
  simp only [quaternionProduct,Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast]

theorem quaternionOracleMul_correct (f g : QuaternionOracle) (U V : SU2)
    (hf : QApproximates f U) (hg : QApproximates g V) :
    QApproximates (quaternionOracleMul f g) (U*V) := by
  intro p i
  simp only [quaternionOracleMul,List.Vector.get_ofFn,quaternionProduct_cast,
    quaternionCoordinates_mul]
  have h := quaternionProduct_error (fun j => ((f (p+4)).get j:ℝ))
    (fun j => ((g (p+4)).get j:ℝ)) (quaternionCoordinates U) (quaternionCoordinates V)
    ((1/2:ℝ)^(p+4)) (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    (quaternionCoordinates_bound U) (quaternionCoordinates_bound V) (hf (p+4)) (hg (p+4)) i
  apply h.trans
  rw [pow_add]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) p]

def quaternionOracleOne : QuaternionOracle := fun _ => List.Vector.ofFn ![1,0,0,0]

theorem quaternionOracleOne_correct : QApproximates quaternionOracleOne 1 := by
  intro p i
  fin_cases i <;> simp [quaternionOracleOne,quaternionCoordinates] <;> positivity

def quaternionWordOracle {m : ℕ} (entry : Fin m → QuaternionOracle) :
    List (Fin m) → QuaternionOracle
  | [] => quaternionOracleOne
  | i::w => quaternionOracleMul (quaternionWordOracle entry w) (entry i)

theorem quaternionWordOracle_correct {m : ℕ} (entry : Fin m → QuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,QApproximates (entry i) (G i)) (w : List (Fin m)) :
    QApproximates (quaternionWordOracle entry w) (instructionWordValue G w) := by
  induction w with
  | nil => exact quaternionOracleOne_correct
  | cons i w ih => exact quaternionOracleMul_correct _ _ _ _ ih (he i)

def wordOracleQueries {m : ℕ} : List (Fin m) → ℕ → List (Fin m×ℕ)
  | [],_ => []
  | i::w,p => wordOracleQueries w (p+4)++[(i,p+4)]

theorem wordOracleQueries_count {m : ℕ} (w : List (Fin m)) (p : ℕ) :
    (wordOracleQueries w p).length=w.length := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih => simp [wordOracleQueries,ih]

theorem wordOracleQueries_precision {m : ℕ} (w : List (Fin m)) (p : ℕ)
    (x : Fin m×ℕ) (hx : x∈wordOracleQueries w p) : x.2≤p+4*w.length := by
  induction w generalizing p with
  | nil => simp [wordOracleQueries] at hx
  | cons i w ih =>
    rcases List.mem_append.mp hx with h|h
    · have ht := ih (p+4) h
      simp only [List.length_cons]
      omega
    · simp only [List.mem_singleton] at h
      subst x
      simp only [List.length_cons]
      omega

end CircuitRecursion
