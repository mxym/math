import Nonnegative

namespace Chollet

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation by a diagonal sign matrix. -/
def signedSwitch (A : Matrix n n ℝ) (s : n → ℝ) : Matrix n n ℝ :=
  fun i j => s i * A i j * s j

omit [Fintype n] [DecidableEq n] in
private theorem switch_sq (A : Matrix n n ℝ) (s : n → ℝ)
    (hs : ∀ i, (s i)^2 = 1) (i j : n) :
    (signedSwitch A s i j)^2 = (A i j)^2 := by
  dsimp [signedSwitch]
  calc
    (s i * A i j * s j)^2 = (s i)^2 * (A i j)^2 * (s j)^2 := by ring
    _ = (A i j)^2 := by rw [hs i, hs j]; ring

omit [Fintype n] [DecidableEq n] in
private theorem switch_diag (A : Matrix n n ℝ) (s : n → ℝ)
    (hs : ∀ i, (s i)^2 = 1) (i : n) :
    signedSwitch A s i i = A i i := by
  dsimp [signedSwitch]
  calc
    s i * A i i * s i = (s i)^2 * A i i := by ring
    _ = A i i := by rw [hs i]; ring

private theorem switch_permanent (A : Matrix n n ℝ) (s : n → ℝ)
    (hs : ∀ i, (s i)^2 = 1) :
    Matrix.permanent (signedSwitch A s) = Matrix.permanent A := by
  classical
  have hsp : (∏ i, s i)^2 = 1 := by
    rw [← Finset.prod_pow]
    simp only [hs]
    simp
  simp only [Matrix.permanent]
  apply Finset.sum_congr rfl
  intro σ _
  have hp : (∏ i, s (σ i)) = ∏ i, s i :=
    Equiv.prod_comp σ s
  calc
    (∏ i, signedSwitch A s (σ i) i)
        = (∏ i, s (σ i)) * (∏ i, A (σ i) i) * (∏ i, s i) := by
            simp only [signedSwitch, Finset.prod_mul_distrib, mul_assoc]
    _ = (∏ i, A (σ i) i) * ((∏ i, s i)^2) := by rw [hp]; ring
    _ = (∏ i, A (σ i) i) := by rw [hsp]; ring

/-- The strong permanent inequality is invariant under diagonal sign switching;
this contains the entire combinatorial core for bipartite-support matrices. -/
theorem sign_switch_permanent_hadamard_bound (A : Matrix n n ℝ) (s : n → ℝ)
    (hs : ∀ i, (s i)^2 = 1)
    (h_nonneg : ∀ i j, 0 ≤ signedSwitch A s i j)
    (h_minor : ∀ i j, (A i j)^2 ≤ A i i * A j j) :
    (Matrix.permanent (fun i j => A i j * A i j)) ≤
      (Matrix.permanent A) * (∏ i, A i i) := by
  let B := signedSwitch A s
  have hbminor : ∀ i j, (B i j)^2 ≤ B i i * B j j := by
    intro i j
    rw [show B i i = A i i from switch_diag A s hs i]
    rw [show B j j = A j j from switch_diag A s hs j]
    rw [show (B i j)^2 = (A i j)^2 from switch_sq A s hs i j]
    exact h_minor i j
  have hbase := nonnegative_permanent_hadamard_bound B h_nonneg hbminor
  have hsqmat :
      (fun i j => B i j * B i j) = (fun i j => A i j * A i j) := by
    funext i j
    nlinarith [switch_sq A s hs i j]
  have hper : Matrix.permanent B = Matrix.permanent A :=
    switch_permanent A s hs
  have hdiag : (∏ i, B i i) = ∏ i, A i i := by
    apply Finset.prod_congr rfl
    intro i _
    exact switch_diag A s hs i
  rw [hsqmat,hper,hdiag] at hbase
  exact hbase

end Chollet
