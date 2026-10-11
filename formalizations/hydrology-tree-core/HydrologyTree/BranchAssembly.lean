import HydrologyTree.RootAttachment

/-! Actual matrix assembly for an arbitrary finite list of child branches. -/
open Matrix Polynomial
noncomputable section
namespace HydrologyTree

structure MatrixBranch where
  size : ℕ
  matrix : Matrix (Fin (size+1)) (Fin (size+1)) ℝ
  root : Fin (size+1)
  inward : ℝ
  outward : ℝ

def branchP (b : MatrixBranch) : ℝ[X] := b.matrix.charpoly
def branchF (b : MatrixBranch) : ℝ[X] := diagonalCofactor b.matrix b.root
def branchR (b : MatrixBranch) : ℝ[X] := C (b.inward * b.outward) * branchF b

def BranchNodes : List MatrixBranch → Type
  | [] => Unit
  | b :: bs => BranchNodes bs ⊕ Fin (b.size+1)

instance branchNodesFintype : (bs : List MatrixBranch) → Fintype (BranchNodes bs)
  | [] => inferInstanceAs (Fintype Unit)
  | b :: bs => by
    letI := branchNodesFintype bs
    exact inferInstanceAs (Fintype (BranchNodes bs ⊕ Fin (b.size+1)))

instance branchNodesDecidableEq : (bs : List MatrixBranch) → DecidableEq (BranchNodes bs)
  | [] => inferInstanceAs (DecidableEq Unit)
  | b :: bs => by
    letI := branchNodesDecidableEq bs
    exact inferInstanceAs (DecidableEq (BranchNodes bs ⊕ Fin (b.size+1)))

def branchRoot : (bs : List MatrixBranch) → BranchNodes bs
  | [] => ()
  | _ :: bs => Sum.inl (branchRoot bs)

/-- The root diagonal is minus d; every child block retains its original diagonal. -/
def assembledMatrix (d : ℝ) : (bs : List MatrixBranch) →
    Matrix (BranchNodes bs) (BranchNodes bs) ℝ
  | [] => Matrix.of fun _ _ => -d
  | b :: bs => edgeJoin (assembledMatrix d bs) b.matrix (branchRoot bs) b.root b.inward b.outward

def branchProduct (bs : List MatrixBranch) : ℝ[X] := (bs.map branchP).prod

/-- Sum of each branch numerator multiplied by the other denominators. -/
def branchNumerator : List MatrixBranch → ℝ[X]
  | [] => 0
  | b :: bs => branchNumerator bs * branchP b + branchR b * branchProduct bs

@[simp] lemma branchProduct_nil : branchProduct [] = 1 := rfl
@[simp] lemma branchProduct_cons (b : MatrixBranch) (bs : List MatrixBranch) :
    branchProduct (b :: bs) = branchP b * branchProduct bs := by simp [branchProduct]

theorem assembled_cofactor (d : ℝ) (bs : List MatrixBranch) :
    diagonalCofactor (assembledMatrix d bs) (branchRoot bs) = branchProduct bs := by
  induction bs with
  | nil =>
    change ((Matrix.of fun (_ _ : Unit) => -d).charmatrix).adjugate () () = 1
    rw [Matrix.adjugate_subsingleton]
    rfl
  | cons b bs ih =>
    change diagonalCofactor
      (edgeJoin (assembledMatrix d bs) b.matrix (branchRoot bs) b.root b.inward b.outward)
      (Sum.inl (branchRoot bs)) = branchProduct (b::bs)
    rw [diagonalCofactor_edgeJoin_left, ih, branchProduct_cons]
    exact mul_comm _ _

/-- Arbitrary-branch characteristic recursion without spectral restrictions. -/
theorem assembled_characteristic (d : ℝ) (bs : List MatrixBranch) :
    (assembledMatrix d bs).charpoly =
      (X+C d) * branchProduct bs - branchNumerator bs := by
  induction bs with
  | nil =>
    change ((Matrix.of fun (_ _ : Unit) => -d).charmatrix).det = (X+C d)*1-0
    rw [Matrix.det_unique]
    simp [Matrix.charmatrix_apply_eq]
  | cons b bs ih =>
    change (edgeJoin (assembledMatrix d bs) b.matrix (branchRoot bs) b.root
      b.inward b.outward).charpoly = _
    rw [charpoly_edgeJoin, ih, assembled_cofactor, branchProduct_cons, branchNumerator]
    dsimp only [branchP, branchR, branchF]
    ring

end HydrologyTree
