import HydrologyTree.PathPolynomial
import HydrologyTree.RateChart

/-! Nested endpoint-path rate coordinates and their explicit permutation to
all physical inward, outward and leak coordinates. No parameter is discarded. -/
open Module Polynomial
noncomputable section
namespace HydrologyTree

@[reducible] def PathRates : ℕ → Type
  | 0 => ℝ
  | n+1 => PathRates n × (ℝ × ℝ)

instance pathRatesNormed : (n : ℕ) → NormedAddCommGroup (PathRates n)
  | 0 => inferInstanceAs (NormedAddCommGroup ℝ)
  | n+1 => by
    letI := pathRatesNormed n
    exact inferInstanceAs (NormedAddCommGroup (PathRates n × (ℝ × ℝ)))

instance pathRatesSpace : (n : ℕ) → NormedSpace ℝ (PathRates n)
  | 0 => inferInstanceAs (NormedSpace ℝ ℝ)
  | n+1 => by
    letI := pathRatesSpace n
    exact inferInstanceAs (NormedSpace ℝ (PathRates n × (ℝ × ℝ)))

instance pathRatesFinite : (n : ℕ) → FiniteDimensional ℝ (PathRates n)
  | 0 => inferInstanceAs (FiniteDimensional ℝ ℝ)
  | n+1 => by
    letI := pathRatesFinite n
    exact inferInstanceAs (FiniteDimensional ℝ (PathRates n × (ℝ × ℝ)))

/-- Add one new root with leak ell and outgoing rate f to the previous child rates. -/
def prependRateEquiv (n : ℕ) : (TreeRates n × (ℝ × ℝ)) ≃ₗ[ℝ] TreeRates (n+1) where
  toFun z := (Fin.cons z.2.1 z.1.1, Fin.cons z.2.2 z.1.2)
  invFun x := ((Fin.tail x.1, Fin.tail x.2),(x.1 0,x.2 0))
  left_inv z := rfl
  right_inv x := by
    apply Prod.ext
    · funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_add' z w := by
    apply Prod.ext
    · funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' a z := by
    apply Prod.ext
    · funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] lemma prependRateEquiv_apply (n : ℕ) (z : TreeRates n × (ℝ × ℝ)) :
    prependRateEquiv n z = (Fin.cons z.2.1 z.1.1, Fin.cons z.2.2 z.1.2) := rfl

def singletonRateEquiv : ℝ ≃ₗ[ℝ] TreeRates 0 where
  toFun a := (fun _ => a, Fin.elim0)
  invFun x := x.1 0
  left_inv a := rfl
  right_inv x := by
    apply Prod.ext
    · funext i; have hi : i = 0 := Fin.ext (by omega); subst i; rfl
    · funext i; exact Fin.elim0 i
  map_add' a b := by
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i
  map_smul' a b := by
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i

/-- Explicit linear permutation from the nested rate order to original arrays. -/
def pathRateEquiv : (n : ℕ) → PathRates n ≃ₗ[ℝ] TreeRates n
  | 0 => singletonRateEquiv
  | n+1 => ((pathRateEquiv n).prodCongr (LinearEquiv.refl ℝ (ℝ × ℝ))).trans (prependRateEquiv n)

@[simp] lemma pathRateEquiv_succ (n : ℕ) (z : PathRates (n+1)) :
    pathRateEquiv (n+1) z = prependRateEquiv n (pathRateEquiv n z.1,z.2) := rfl

/-- The actual root leak as a continuous linear function of all path rates. -/
def pathLeak (n : ℕ) : PathRates n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (((LinearMap.proj 0).comp
    (LinearMap.fst ℝ (VertexValues n) (EdgeValues n))).comp (pathRateEquiv n).toLinearMap)

@[simp] lemma pathLeak_apply (n : ℕ) (z : PathRates n) :
    pathLeak n z = (pathRateEquiv n z).1 0 := rfl

@[simp] lemma pathLeak_succ (n : ℕ) (z : PathRates (n+1)) : pathLeak (n+1) z = z.2.1 := rfl

/-- The exact monomial, including all zero-rate boundaries. -/
def pathWeight : (n : ℕ) → PathRates n → ℝ
  | 0, _ => 1
  | n+1, z => (pathLeak n z.1)^(n+1) * z.2.2^n * pathWeight n z.1

def pathRateMonomial (n : ℕ) (x : TreeRates n) : ℝ :=
  ∏ i : Fin n, x.1 i.succ ^ (n-i.val) * x.2 i ^ (n-i.val-1)

lemma pathRateMonomial_prepend (n : ℕ) (y : TreeRates n) (ell f : ℝ) :
    pathRateMonomial (n+1) (prependRateEquiv n (y,(ell,f))) =
      y.1 0^(n+1) * f^n * pathRateMonomial n y := by
  rw [pathRateMonomial, Fin.prod_univ_succ]
  simp only [prependRateEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_add_right,
    Nat.add_sub_cancel]
  rfl

theorem pathWeight_eq_rate_monomial (n : ℕ) (z : PathRates n) :
    pathWeight n z = pathRateMonomial n (pathRateEquiv n z) := by
  induction n with
  | zero => simp [pathWeight, pathRateMonomial]
  | succ n ih =>
    rw [pathWeight, pathRateEquiv_succ, pathRateMonomial_prepend, ih, pathLeak_apply]

/-- The sign depends only on size and the explicit coefficient ordering. -/
def pathOrientation : ℕ → ℝ
  | 0 => 1
  | n+1 => (-1 : ℝ)^(n+1) * pathOrientation n

lemma pathOrientation_sq (n : ℕ) : pathOrientation n ^ 2 = 1 := by
  induction n with
  | zero => norm_num [pathOrientation]
  | succ n ih =>
    rw [pathOrientation, mul_pow, ih, mul_one, ← pow_mul, Nat.mul_comm (n+1) 2, pow_mul]
    norm_num

end HydrologyTree
