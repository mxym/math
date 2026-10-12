import CholletCycleExpansion
import Mathlib.LinearAlgebra.Matrix.Trace

/-! A row-sum contraction and the cycle-trace estimate for the actual
matrix powers used in the all-graph upper bound. No spectral theorem or
abstract trace-bound hypothesis is assumed. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

def frobeniusSquare (A : Matrix V V ℝ) : ℝ := ∑ i, ∑ j, (A i j)^2

lemma frobeniusSquare_nonneg (A : Matrix V V ℝ) : 0 ≤ frobeniusSquare A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma weighted_square_sum (c v : V → ℝ) (hc : ∀ j, 0 ≤ c j) :
    (∑ j, c j*v j)^2 ≤ (∑ j,c j)*(∑ j,c j*(v j)^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun j _ => hc j) (fun j _ => mul_nonneg (hc j) (sq_nonneg _))
  intro j _
  nlinarith [sq_nonneg (c j*v j)]

theorem row_sum_square_contraction (C : Matrix V V ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hc : ∀ i j, 0 ≤ C i j)
    (hrow : ∀ i, (∑ j,C i j) ≤ r)
    (hcol : ∀ j, (∑ i,C i j) ≤ r) (v : V → ℝ) :
    (∑ i, (∑ j,C i j*v j)^2) ≤ r^2*(∑ j,(v j)^2) := by
  calc
    _ ≤ ∑ i,r*(∑ j,C i j*(v j)^2) := Finset.sum_le_sum fun i _ =>
      (weighted_square_sum (C i) v (hc i)).trans
        (mul_le_mul_of_nonneg_right (hrow i)
          (Finset.sum_nonneg fun j _ => mul_nonneg (hc i j) (sq_nonneg _)))
    _ = r*(∑ j,(∑ i,C i j)*(v j)^2) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ r*(∑ j,r*(v j)^2) := by
      apply mul_le_mul_of_nonneg_left _ hr
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem frobeniusSquare_mul_le (C B : Matrix V V ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hc : ∀ i j,0 ≤ C i j)
    (hrow : ∀ i,(∑ j,C i j) ≤ r)
    (hcol : ∀ j,(∑ i,C i j) ≤ r) :
    frobeniusSquare (C*B) ≤ r^2*frobeniusSquare B := by
  unfold frobeniusSquare
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply]
  calc
    _ ≤ ∑ j,r^2*(∑ i,(B i j)^2) := Finset.sum_le_sum fun j _ =>
      row_sum_square_contraction C r hr hc hrow hcol (fun i => B i j)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

theorem frobeniusSquare_pow_le (C : Matrix V V ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hc : ∀ i j,0 ≤ C i j)
    (hrow : ∀ i,(∑ j,C i j) ≤ r)
    (hcol : ∀ j,(∑ i,C i j) ≤ r) (n : ℕ) :
    frobeniusSquare (C^(n+1)) ≤ (r^2)^n*frobeniusSquare C := by
  induction n with
  | zero => simp
  | succ n ih =>
    change frobeniusSquare (C^((n+1)+1)) ≤ (r^2)^(n+1)*frobeniusSquare C
    rw [pow_succ']
    calc
      _ ≤ r^2*frobeniusSquare (C^(n+1)) :=
        frobeniusSquare_mul_le C (C^(n+1)) r hr hc hrow hcol
      _ ≤ r^2*((r^2)^n*frobeniusSquare C) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg r)
      _ = _ := by rw [pow_succ]; ring

theorem trace_mul_square_le (A B : Matrix V V ℝ) :
    (A*B).trace^2 ≤ frobeniusSquare A*frobeniusSquare B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (V×V))
    (fun p => A p.1 p.2) (fun p => B p.2 p.1)
  simp only [Fintype.sum_prod_type] at h
  have hB : (∑ i, ∑ j, (B j i)^2) = frobeniusSquare B := by
    unfold frobeniusSquare
    exact Finset.sum_comm
  change (∑ i, ∑ j, A i j*B j i)^2 ≤
    frobeniusSquare A*(∑ i,∑ j,(B j i)^2) at h
  rw [hB] at h
  simpa only [Matrix.trace,Matrix.diag,Matrix.mul_apply] using h

theorem trace_square_eq_frobeniusSquare (C : Matrix V V ℝ)
    (hs : ∀ i j,C i j=C j i) : (C^2).trace = frobeniusSquare C := by
  simp only [pow_two,Matrix.trace,Matrix.diag,Matrix.mul_apply,frobeniusSquare]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hs i j]

/-- For every n≥0 this is the genuine estimate
tr(C^(n+2)) ≤ r^n tr(C^2) for symmetric nonnegative row-substochastic C. -/
theorem trace_pow_le_row_sum (C : Matrix V V ℝ) (r : ℝ)
    (hr : 0 ≤ r) (hc : ∀ i j,0 ≤ C i j)
    (hs : ∀ i j,C i j=C j i)
    (hrow : ∀ i,(∑ j,C i j) ≤ r) (n : ℕ) :
    (C^(n+2)).trace ≤ r^n*(C^2).trace := by
  have hcol (j : V) : (∑ i,C i j) ≤ r := by simpa only [hs] using hrow j
  have hF := frobeniusSquare_nonneg C
  have hpow := frobeniusSquare_pow_le C r hr hc hrow hcol n
  have htr := trace_mul_square_le C (C^(n+1))
  have he : (r^2)^n = (r^n)^2 := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  rw [← pow_succ'] at htr
  change (C^(n+2)).trace^2 ≤ _ at htr
  rw [he] at hpow
  have hbound := mul_le_mul_of_nonneg_left hpow hF
  rw [trace_square_eq_frobeniusSquare C hs]
  have hnonneg : 0 ≤ r^n*frobeniusSquare C := mul_nonneg (pow_nonneg hr n) hF
  nlinarith [sq_nonneg ((C^(n+2)).trace-r^n*frobeniusSquare C)]

end
end Chollet
