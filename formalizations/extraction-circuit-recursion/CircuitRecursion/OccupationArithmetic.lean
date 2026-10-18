import CircuitRecursion.FinitePrecision

open scoped BigOperators
open CircuitCompletion
namespace CircuitRecursion

/-- Occupied branching coefficients have a discrete, known denominator. -/
theorem occupationMass_pos_iff {k : ℕ} (ν : Sym (Fin 4) (k+1)) (i : Fin 4) :
    0<occupationMass ν i ↔ i∈ν := by
  unfold occupationMass
  rw [div_pos_iff_of_pos_right (by positivity),Nat.cast_pos]
  exact Multiset.count_pos

theorem occupationMass_ge_inverse {k : ℕ} (ν : Sym (Fin 4) (k+1))
    (i : Fin 4) (hi : i∈ν) :
    1/(k+1:ℝ)≤occupationMass ν i := by
  have hc : (1:ℝ)≤(ν.val.count i:ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Multiset.count_pos.mpr hi))
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr hc

/-- Every partial accumulated mass is one integer ratio, with no real zero
test needed when the occupation counts themselves are explicitly given. -/
theorem occupationMass_partial_count {k : ℕ} (ν : Sym (Fin 4) (k+1))
    (S : Finset (Fin 4)) :
    (∑ i∈S,occupationMass ν i)=((∑ i∈S,ν.val.count i:ℕ):ℝ)/(k+1) := by
  simp only [occupationMass,← Finset.sum_div,Nat.cast_sum]

theorem occupationMass_partial_le_one {k : ℕ} (ν : Sym (Fin 4) (k+1))
    (S : Finset (Fin 4)) : (∑ i∈S,occupationMass ν i)≤1 := by
  rw [← occupationMass_sum ν]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (by intro i hi hS; exact occupationMass_nonneg ν i)

theorem occupationMass_partial_ge_inverse {k : ℕ} (ν : Sym (Fin 4) (k+1))
    (S : Finset (Fin 4)) (i : Fin 4) (hiS : i∈S) (hi : i∈ν) :
    1/(k+1:ℝ)≤∑ j∈S,occupationMass ν j := by
  exact (occupationMass_ge_inverse ν i hi).trans
    (Finset.single_le_sum (fun j hj => occupationMass_nonneg ν j) hiS)

/-- The common occupation denominator cancels in the actual merging angle.
This is a matrix-coefficient identity, not a claim about evaluation cost. -/
theorem rational_mergeAngle_trig (A B j : ℕ) (hj : 0<j) (hAB : 0<A+B) :
    Real.cos (mergeAngle ((A:ℝ)/j) ((B:ℝ)/j))=Real.sqrt ((A:ℝ)/(A+B)) ∧
    Real.sin (mergeAngle ((A:ℝ)/j) ((B:ℝ)/j))=Real.sqrt ((B:ℝ)/(A+B)) := by
  have hj' : (j:ℝ)≠0 := by exact_mod_cast hj.ne'
  have hAB' : (0:ℝ)<(A:ℝ)+B := by exact_mod_cast hAB
  have hsum : (A:ℝ)/j+(B:ℝ)/j=((A:ℝ)+B)/j := by ring
  have hsumpos : 0<(A:ℝ)/j+(B:ℝ)/j := by rw [hsum]; positivity
  have hc : Real.sqrt ((A:ℝ)/j)/Real.sqrt ((A:ℝ)/j+(B:ℝ)/j)=
      Real.sqrt ((A:ℝ)/(A+B)) := by
    rw [← Real.sqrt_div (by positivity),hsum]
    congr 1
    field_simp
  have hs : Real.sqrt ((B:ℝ)/j)/Real.sqrt ((A:ℝ)/j+(B:ℝ)/j)=
      Real.sqrt ((B:ℝ)/(A+B)) := by
    rw [← Real.sqrt_div (by positivity),hsum]
    congr 1
    field_simp
  have hcs : Real.sqrt ((A:ℝ)/(A+B))*Real.sqrt ((A:ℝ)/(A+B))+
      Real.sqrt ((B:ℝ)/(A+B))*Real.sqrt ((B:ℝ)/(A+B))=1 := by
    rw [← pow_two,← pow_two,Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity)]
    rw [← add_div]
    exact div_self hAB'.ne'
  simpa only [mergeAngle,if_neg hsumpos.ne',hc,hs] using
    circleAngle_trig (Real.sqrt ((A:ℝ)/(A+B))) (Real.sqrt ((B:ℝ)/(A+B))) hcs

theorem occupation_partial_mergeAngle_trig {k : ℕ} (ν : Sym (Fin 4) (k+1))
    (S : Finset (Fin 4)) (i p : Fin 4) (hpS : p∈S) (hp : p∈ν) :
    Real.cos (mergeAngle (∑ l∈S,occupationMass ν l) (occupationMass ν i))=
      Real.sqrt (((∑ l∈S,ν.val.count l:ℕ):ℝ)/
        ((∑ l∈S,ν.val.count l:ℕ)+ν.val.count i)) ∧
    Real.sin (mergeAngle (∑ l∈S,occupationMass ν l) (occupationMass ν i))=
      Real.sqrt ((ν.val.count i:ℝ)/
        ((∑ l∈S,ν.val.count l:ℕ)+ν.val.count i)) := by
  rw [occupationMass_partial_count]
  unfold occupationMass
  have hsum : 0<∑ l∈S,ν.val.count l :=
    lt_of_lt_of_le (Multiset.count_pos.mpr hp)
      (Finset.single_le_sum (fun l hl => Nat.zero_le (ν.val.count l)) hpS)
  have h := rational_mergeAngle_trig (∑ l∈S,ν.val.count l) (ν.val.count i)
    (k+1) (by omega) (by omega)
  simpa only [Nat.cast_add,Nat.cast_one] using h

end CircuitRecursion
