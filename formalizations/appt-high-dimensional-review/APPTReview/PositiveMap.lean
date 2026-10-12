import APPTReview.BlockContraction

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- Each summand is a sum of congruences of P and its positive complement. -/
def pairPositive (P : Matrix (a × b) (a × b) ℂ) (t u : a) :=
  if t=u then 0 else
    localCongruence P (localPair t u 1) + localCongruence (1-P) (localPair t u (-1))

theorem pairPositive_posSemidef {P : Matrix (a × b) (a × b) ℂ}
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) (t u : a) :
    (pairPositive P t u).PosSemidef := by
  unfold pairPositive
  split_ifs
  · exact Matrix.PosSemidef.zero
  · exact (localCongruence_posSemidef hP _).add (localCongruence_posSemidef hI _)

theorem pairPositive_apply (P : Matrix (a × b) (a × b) ℂ) (t u i j : a) (x y : b) :
    pairPositive P t u (i,x) (j,y) =
      (if t=i ∧ i=j ∧ u≠i then (1 : Matrix b b ℂ) x y else 0) +
      (if u=i ∧ i=j ∧ t≠i then (1 : Matrix b b ℂ) x y else 0) +
      (if t=i ∧ u=j ∧ i≠j then 2*P (j,x) (i,y) else 0) +
      (if u=i ∧ t=j ∧ i≠j then 2*P (j,x) (i,y) else 0) := by
  by_cases htu : t=u
  · subst u
    by_cases hi : t=i <;> by_cases hj : i=j <;>
      simp_all [pairPositive]
  · simp only [pairPositive, if_neg htu, Matrix.add_apply, localPair_apply]
    by_cases hi : i=t <;> by_cases hj : j=t <;>
      by_cases hij : i=j <;> by_cases hiu : i=u <;> by_cases hju : j=u <;> by_cases hxy : x=y <;>
      simp_all [Matrix.sub_apply, Matrix.one_apply, eq_comm, two_mul]

theorem sum_except_constant (i : a) (c : ℂ) :
    (∑ u : a, if i=u then 0 else c) = ((Fintype.card a : ℂ)-1)*c := by
  calc
    _ = (∑ _u : a, c) - ∑ u : a, if i=u then c else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _
      split_ifs <;> simp
    _ = _ := by simp; ring

/-- Exact positive-map identity for arbitrary finite first-factor dimension. -/
theorem contraction_partialTranspose_identity (P : Matrix (a × b) (a × b) ℂ) :
    (2 : ℝ) • APPT.Quantum.partialTranspose P +
      ((Fintype.card a : ℝ)-1) • (1 : Matrix (a × b) (a × b) ℂ) =
    (2 : ℝ) • (∑ t : a, localCongruence P (localDiagonal t)) +
      (1/2 : ℝ) • (∑ t : a, ∑ u : a, pairPositive P t u) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, localDiagonal_apply,
    pairPositive_apply, Complex.real_smul, smul_eq_mul]
  by_cases hij : i=j
  · subst j
    simp [APPT.Quantum.partialTranspose, Matrix.one_apply, Finset.sum_add_distrib,
      Finset.sum_ite_irrel, ite_and, eq_comm]
    rw [sum_except_constant]
    by_cases hxy : x=y <;> simp [hxy]
    <;> push_cast <;> ring
  · simp [APPT.Quantum.partialTranspose, Matrix.one_apply, Finset.sum_add_distrib,
      hij, ite_and, eq_comm]
    <;> ring

/-- Finite sums preserve positivity, with all summands explicitly checked. -/
theorem psd_finset_sum {ι κ : Type*} [Fintype κ] (s : Finset ι)
    (F : ι → Matrix κ κ ℂ) (hF : ∀ i ∈ s, (F i).PosSemidef) :
    (∑ i ∈ s, F i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix κ κ ℂ).PosSemidef)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

/-- Every positive contraction has partial transpose bounded below by -(m-1)/2.
This is an actual matrix positivity theorem in arbitrary bipartite dimensions. -/
theorem contraction_partialTranspose_lower (P : Matrix (a × b) (a × b) ℂ)
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) :
    ((2 : ℝ) • APPT.Quantum.partialTranspose P +
      ((Fintype.card a : ℝ)-1) • (1 : Matrix (a × b) (a × b) ℂ)).PosSemidef := by
  rw [contraction_partialTranspose_identity]
  have hd := psd_finset_sum Finset.univ (fun t : a => localCongruence P (localDiagonal t))
    (fun t _ => localCongruence_posSemidef hP _)
  have hp := psd_finset_sum Finset.univ (fun t : a => ∑ u : a, pairPositive P t u)
    (fun t _ => psd_finset_sum Finset.univ (fun u : a => pairPositive P t u)
      (fun u _ => pairPositive_posSemidef hP hI t u))
  exact (hd.smul (by norm_num : (0 : ℝ) ≤ 2)).add
    (hp.smul (by norm_num : (0 : ℝ) ≤ 1/2))

/-- Dimension-uniform physical APPT sufficiency, not an assumed spectral criterion. -/
theorem absolutelyPPT_dimension_contraction (P : Matrix (a × b) (a × b) ℂ)
    (hP : P.PosSemidef) (hI : (1-P).PosSemidef) :
    APPT.Quantum.AbsolutelyPPT
      (((Fintype.card a : ℝ)-1) • (1 : Matrix (a × b) (a × b) ℂ) + (2 : ℝ) • P) := by
  intro U
  let Q := (U : Matrix (a × b) (a × b) ℂ) * P * (U : Matrix (a × b) (a × b) ℂ)ᴴ
  have hQ : Q.PosSemidef := hP.mul_mul_conjTranspose_same _
  have hQI : (1-Q).PosSemidef := by
    have hh := hI.mul_mul_conjTranspose_same (U : Matrix (a × b) (a × b) ℂ)
    simpa [Q, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.star_eq_conjTranspose,
      Unitary.coe_mul_star_self] using hh
  have hh := contraction_partialTranspose_lower Q hQ hQI
  simpa [Q, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.star_eq_conjTranspose, Unitary.coe_mul_star_self, add_comm] using hh

end APPTReview
