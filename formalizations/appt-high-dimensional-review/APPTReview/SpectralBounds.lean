import APPTReview.SortedWitness

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The rank-two all-ones test, now for the canonically ordered actual spectrum. -/
theorem appt_sorted_rankTwo_linear {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hA : A.IsHermitian) (h : APPT.Quantum.AbsolutelyPPT A)
    (hD : 4 ≤ Fintype.card (Fin m × Fin n)) :
    hA.eigenvalues₀ (rankTwoLabels hD (1,0)) ≤
      hA.eigenvalues₀ (rankTwoLabels hD (0,0)) +
      hA.eigenvalues₀ (rankTwoLabels hD (0,1)) +
      hA.eigenvalues₀ (rankTwoLabels hD (1,1)) := by
  have hM := appt_sorted_rankTwo_witness hm hmn hA h
  have hq := hM.dotProduct_mulVec_nonneg (fun _ : Fin 2 => (1 : ℝ))
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two, witnessMatrix] at hq
  linarith

/-- Ordered scalar mass accounting; the bottom three cannot have a larger
average than the complete tail. No positivity or spectral hypothesis is hidden. -/
theorem ordered_head_from_triple {d : ℕ} (f : Fin (d+4) → ℝ)
    (hf : Antitone f)
    (hhead : f 0 ≤ ∑ j : Fin 3, f (Fin.natAdd d j).succ) :
    ((d : ℝ)+6)*f 0 ≤ 3*∑ i, f i := by
  let B : ℝ := ∑ j : Fin 3, f (Fin.natAdd d j).succ
  let M : ℝ := ∑ i : Fin d, f (i.castAdd 3).succ
  have hb : B ≤ 3*f (Fin.natAdd d (0 : Fin 3)).succ := by
    calc
      _ ≤ ∑ _j : Fin 3, f (Fin.natAdd d (0 : Fin 3)).succ := by
        apply Finset.sum_le_sum
        intro j _
        exact hf (by change d+1 ≤ d+j.val+1; omega)
      _ = _ := by simp
  have hm (i : Fin d) : B ≤ 3*f (i.castAdd 3).succ := by
    have ht : f (Fin.natAdd d (0 : Fin 3)).succ ≤ f (i.castAdd 3).succ :=
      hf (by change i.val+1 ≤ d+1; omega)
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hm i)
  have hm' : (d : ℝ)*B ≤ 3*M := by
    simpa [M, Finset.mul_sum] using hsum
  have hsplit : (∑ i, f i) = f 0+M+B := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_add]
    simp only [M, B]
    ring
  have ht : ((d : ℝ)+3)*f 0 ≤ ((d : ℝ)+3)*B :=
    mul_le_mul_of_nonneg_left hhead (by positivity)
  rw [hsplit]
  nlinarith

/-- The trace-one condition for the actual canonically ordered real eigenvalues. -/
theorem ordered_eigenvalues_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (htr : A.trace = 1) :
    (∑ i, hA.eigenvalues₀ i) = 1 := by
  have ht : (∑ i, hA.eigenvalues i) = 1 := by
    have hh := congrArg Complex.re hA.trace_eq_sum_eigenvalues
    rw [htr] at hh
    simpa only [Complex.one_re, Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using hh.symm
  have hs := (spectralLabel ι).sum_comp hA.eigenvalues
  simpa using hs.trans ht

/-- Largest-eigenvalue bound from ordering and the physical rank-two test.
This scalar lemma keeps dimension casts out of the quantum theorem. -/
theorem head_bound_of_rankTwo {D : ℕ} (hD : 4 ≤ D) (f : Fin D → ℝ)
    (hf : Antitone f) (hs : (∑ i, f i) = 1)
    (hc : f (rankTwoLabels hD (1,0)) ≤
      f (rankTwoLabels hD (0,0)) + f (rankTwoLabels hD (0,1)) +
      f (rankTwoLabels hD (1,1))) :
    f (rankTwoLabels hD (1,0)) ≤ 3/((D : ℝ)+2) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d+4 := ⟨D-4, by omega⟩
  have h0 : rankTwoLabels hD (1,0) = (0 : Fin (d+4)) := rfl
  have h1 : rankTwoLabels hD (0,0) = (Fin.natAdd d (2 : Fin 3)).succ := by
    apply Fin.ext
    simp only [rankTwoLabels]
    simp
  have h2 : rankTwoLabels hD (0,1) = (Fin.natAdd d (1 : Fin 3)).succ := by
    apply Fin.ext
    simp only [rankTwoLabels]
    simp
  have h3 : rankTwoLabels hD (1,1) = (Fin.natAdd d (0 : Fin 3)).succ := by
    apply Fin.ext
    simp only [rankTwoLabels]
    simp
  rw [h0,h1,h2,h3] at hc
  have hh : f 0 ≤ ∑ j : Fin 3, f (Fin.natAdd d j).succ := by
    rw [Fin.sum_univ_three]
    linarith
  have hb := ordered_head_from_triple f hf hh
  rw [hs] at hb
  have hp : (0 : ℝ) < (d+4 : ℕ)+2 := by positivity
  apply (le_div_iff₀ hp).2
  norm_num [rankTwoLabels] at *
  nlinarith

/-- For every rectangular dimension with 2 ≤ m ≤ n, a genuine APPT density
matrix has largest eigenvalue at most 3/(mn+2). -/
theorem appt_largest_eigenvalue_bound {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ}
    (hρ : APPT.Quantum.IsDensity A) (h : APPT.Quantum.AbsolutelyPPT A)
    (hD : 4 ≤ Fintype.card (Fin m × Fin n)) :
    hρ.1.isHermitian.eigenvalues₀ (rankTwoLabels hD (1,0)) ≤
      3/((m : ℝ)*n+2) := by
  have hb := head_bound_of_rankTwo hD hρ.1.isHermitian.eigenvalues₀
    hρ.1.isHermitian.eigenvalues₀_antitone (ordered_eigenvalues_sum hρ.1.isHermitian hρ.2)
    (appt_sorted_rankTwo_linear hm hmn hρ.1.isHermitian h hD)
  simpa using hb

end APPTReview
