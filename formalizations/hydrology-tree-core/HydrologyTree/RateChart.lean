import HydrologyTree.Triangular
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block

/-! Actual conservative tree rate coordinates, with arbitrary finite size.
Vertices are topologically numbered from the designated leak/root 0.
The parameter at 0 is the leak; at every other vertex it is the transfer rate
toward its parent. No positivity or nonzero-rate premise is used below. -/
open Module Matrix
noncomputable section
namespace HydrologyTree

/-- A finite rooted tree in a topological vertex numbering. Every nonroot
vertex i+1 has exactly one parent, with smaller vertex number. -/
structure OrderedTree (n : ℕ) where
  parent : Fin n → Fin (n+1)
  parent_le : ∀ i, (parent i).val ≤ i.val

abbrev VertexValues (n : ℕ) := Fin (n+1) → ℝ
abbrev EdgeValues (n : ℕ) := Fin n → ℝ
abbrev TreeRates (n : ℕ) := VertexValues n × EdgeValues n

lemma parent_ne_child {n : ℕ} (t : OrderedTree n) (i : Fin n) :
    t.parent i ≠ i.succ := by
  intro h
  have hle := t.parent_le i
  have := congrArg Fin.val h
  simp only [Fin.val_succ] at this
  omega

/-- Parent-incidence matrix of the actual labelled tree. -/
def parentIncidence {n : ℕ} (t : OrderedTree n) : Matrix (Fin (n+1)) (Fin n) ℝ :=
  Matrix.of fun v e => if t.parent e = v then 1 else 0

/-- Derivative of c_e=a_e f_e with respect to the inward/diagonal parameters. -/
def childWeighted {n : ℕ} (f : EdgeValues n) : Matrix (Fin n) (Fin (n+1)) ℝ :=
  Matrix.of fun e v => if e.succ = v then f e else 0

def parentCLM {n : ℕ} (t : OrderedTree n) : EdgeValues n →L[ℝ] VertexValues n :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (parentIncidence t))

@[simp] lemma parentCLM_apply {n : ℕ} (t : OrderedTree n) (f : EdgeValues n)
    (v : Fin (n+1)) :
    parentCLM t f v = ∑ e, if t.parent e = v then f e else 0 := by
  simp [parentCLM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    parentIncidence, ite_mul]

/-- Physical rate chart: d_v is the sum of all rates leaving v, and c_e is
exactly the product of the two opposed rates on edge e. -/
def rateChart {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : TreeRates n :=
  (x.1 + parentCLM t x.2, fun e => x.1 e.succ * x.2 e)

def rateChartDerivative {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    TreeRates n →L[ℝ] TreeRates n :=
  ((ContinuousLinearMap.fst ℝ (VertexValues n) (EdgeValues n)) +
    (parentCLM t).comp (ContinuousLinearMap.snd ℝ (VertexValues n) (EdgeValues n))).prod
    (ContinuousLinearMap.pi fun e : Fin n =>
      x.1 e.succ • ((ContinuousLinearMap.proj e).comp
        (ContinuousLinearMap.snd ℝ (VertexValues n) (EdgeValues n))) +
      x.2 e • ((ContinuousLinearMap.proj e.succ).comp
        (ContinuousLinearMap.fst ℝ (VertexValues n) (EdgeValues n))))

/-- The rate-coordinate Jacobian is derived from the actual polynomial map. -/
theorem hasFDerivAt_rateChart {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    HasFDerivAt (rateChart t) (rateChartDerivative t x) x := by
  apply HasFDerivAt.prodMk
  · exact (ContinuousLinearMap.fst ℝ (VertexValues n) (EdgeValues n)).hasFDerivAt.add
      ((parentCLM t).hasFDerivAt.comp x
        (ContinuousLinearMap.snd ℝ (VertexValues n) (EdgeValues n)).hasFDerivAt)
  · apply hasFDerivAt_pi.mpr
    intro e
    exact ((ContinuousLinearMap.proj e.succ).comp
      (ContinuousLinearMap.fst ℝ (VertexValues n) (EdgeValues n))).hasFDerivAt.mul
      ((ContinuousLinearMap.proj e).comp
        (ContinuousLinearMap.snd ℝ (VertexValues n) (EdgeValues n))).hasFDerivAt

lemma toMatrix_rateChartDerivative {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    LinearMap.toMatrix ((Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n)))
      ((Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n)))
      (rateChartDerivative t x).toLinearMap =
      Matrix.fromBlocks 1 (parentIncidence t) (childWeighted x.2)
        (Matrix.diagonal fun e : Fin n => x.1 e.succ) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.toMatrix_apply, rateChartDerivative, childWeighted,
      parentIncidence, Matrix.one_apply, Matrix.diagonal_apply,
      Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rename_i v j
  symm
  rw [Finset.sum_eq_single j]
  · simp
  · intro e _ he
    simp [Ne.symm he]
  · simp

lemma childWeighted_mul_parent {n : ℕ} (t : OrderedTree n) (f : EdgeValues n)
    (i j : Fin n) :
    (childWeighted f * parentIncidence t) i j = if t.parent j = i.succ then f i else 0 := by
  simp [Matrix.mul_apply, childWeighted, parentIncidence, ite_mul, eq_comm]

lemma rateSchur_upperTriangular {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (Matrix.diagonal (fun e : Fin n => x.1 e.succ) -
      childWeighted x.2 * parentIncidence t).IsUpperTriangular := by
  intro i j hij
  have hne : t.parent j ≠ i.succ := by
    intro h
    have hle := t.parent_le j
    have hh := congrArg Fin.val h
    simp only [Fin.val_succ] at hh
    have hijv : j.val < i.val := hij
    omega
  have hneq : i ≠ j := ne_of_gt (show j < i from hij)
  simp [Matrix.sub_apply, Matrix.diagonal_apply, childWeighted_mul_parent,
    hne, hneq]

lemma rateSchur_diagonal {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (i : Fin n) :
    (Matrix.diagonal (fun e : Fin n => x.1 e.succ) -
      childWeighted x.2 * parentIncidence t) i i = x.1 i.succ := by
  simp [childWeighted_mul_parent, parent_ne_child]

/-- The exact physical-rate Jacobian, for every tree size and all real rates.
In particular, zero edges are not excluded by an inverse-rate calculation. -/
theorem det_rateChartDerivative {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    (LinearMap.toMatrix ((Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n)))
      ((Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n)))
      (rateChartDerivative t x).toLinearMap).det = ∏ i : Fin n, x.1 i.succ := by
  rw [toMatrix_rateChartDerivative, Matrix.det_fromBlocks_one₁₁,
    Matrix.det_of_upperTriangular (rateSchur_upperTriangular t x)]
  apply Finset.prod_congr rfl
  intro i _
  exact rateSchur_diagonal t x i

/-- The true Frechet Jacobian, not a separately prescribed formal matrix. -/
def physicalRateJacobian {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : ℝ :=
  (LinearMap.toMatrix ((Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n)))
    ((Pi.basisFun ℝ (Fin (n+1))).prod (Pi.basisFun ℝ (Fin n)))
    (fderiv ℝ (rateChart t) x).toLinearMap).det

theorem physicalRateJacobian_eq {n : ℕ} (t : OrderedTree n) (x : TreeRates n) :
    physicalRateJacobian t x = ∏ i : Fin n, x.1 i.succ := by
  rw [physicalRateJacobian, (hasFDerivAt_rateChart t x).fderiv,
    det_rateChartDerivative]

end HydrologyTree
