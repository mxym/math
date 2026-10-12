import HydrologyTree.StieltjesResidues

/-! Exact polynomial reconstruction of a reciprocal response. Quotient/remainder
and all residues are reconstructed from the actual polynomials and all their
simple roots; no unproved partial fraction decomposition is assumed. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma monic_consecutive_division (P F : ℝ[X]) (hP : P.Monic) (hF : F.Monic)
    (hdeg : P.natDegree=F.natDegree+1) :
    P /ₘ F = X + C ((P /ₘ F).coeff 0) := by
  have hle : F.degree ≤ P.degree := by
    rw [Polynomial.degree_eq_natDegree hF.ne_zero,Polynomial.degree_eq_natDegree hP.ne_zero,hdeg]
    exact_mod_cast Nat.le_succ F.natDegree
  have hq : (P /ₘ F).Monic := by
    change (P /ₘ F).leadingCoeff=1
    rw [Polynomial.leadingCoeff_divByMonic_of_monic hF hle]
    exact hP
  apply hq.eq_X_add_C
  rw [Polynomial.natDegree_divByMonic P hF,hdeg]
  omega

lemma stieltjesDenominator_derivative_pole {n : ℕ} (b : Fin n → ℝ) (i : Fin n) :
    (stieltjesDenominator b).derivative.eval (-b i) =
      ∏ j ∈ Finset.univ.erase i, (b j-b i) := by
  rw [stieltjesDenominator_derivative,stieltjesNumerator_eval_pole,one_mul]

lemma stieltjesDenominator_simple {n : ℕ} (b : Fin n → ℝ) (hb : Function.Injective b) (i : Fin n) :
    (stieltjesDenominator b).derivative.eval (-b i) ≠ 0 := by
  rw [stieltjesDenominator_derivative_pole]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj he
  exact (Finset.mem_erase.mp hj).1 (hb (sub_eq_zero.mp he))

/-- A complete algebraic reciprocal partial fraction identity. The denominator
is monic and has exactly n prescribed distinct real zeros; P has degree n+1.
Neither signs of residues nor positivity are premises of this algebraic lemma. -/
theorem polynomial_reciprocal_interpolation {n : ℕ} (P : ℝ[X]) (b g : Fin n → ℝ)
    (hP : P.Monic) (hd : P.natDegree=n+1) (hb : Function.Injective b)
    (hg : ∀ i, g i = -P.eval (-b i)/(stieltjesDenominator b).derivative.eval (-b i)) :
    P = (X+C ((P /ₘ stieltjesDenominator b).coeff 0))*stieltjesDenominator b -
      stieltjesNumerator b g := by
  let F := stieltjesDenominator b
  have hF : F.Monic := stieltjesDenominator_monic b
  have hFd : F.natDegree=n := by simpa only [Fintype.card_fin] using stieltjesDenominator_degree_card b
  have hQ := monic_consecutive_division P F hP hF (by rw [hd,hFd])
  have hrem : P %ₘ F = -stieltjesNumerator b g := by
    by_cases hn : n=0
    · letI : IsEmpty (Fin n) := ⟨fun i => by have h := i.isLt; omega⟩
      have hF1 : F=1 := by simp [F,stieltjesDenominator]
      simp [hF1,stieltjesNumerator]
    · have hF1 : F ≠ 1 := by intro h; rw [h,Polynomial.natDegree_one] at hFd; exact hn hFd.symm
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (neg_injective.comp hb)
      · intro i
        change (P %ₘ F).eval (-b i) = (-stieltjesNumerator b g).eval (-b i)
        have hv : (P %ₘ F).eval (-b i) = P.eval (-b i) := by
          have h := congrArg (fun Q : ℝ[X] => Q.eval (-b i)) (Polynomial.modByMonic_add_div P F)
          simpa only [Polynomial.eval_add,Polynomial.eval_mul,F,stieltjesDenominator_eval_pole,
            zero_mul,add_zero] using h
        rw [hv,Polynomial.eval_neg,stieltjesNumerator_eval_pole,hg]
        rw [← stieltjesDenominator_derivative_pole]
        rw [div_mul_cancel₀ _ (stieltjesDenominator_simple b hb i),neg_neg]
      · have hR : (P %ₘ F).natDegree < n := by
          simpa only [hFd] using Polynomial.natDegree_modByMonic_lt P hF hF1
        have hS : (stieltjesNumerator b g).natDegree < n := by
          rcases n with _ | k
          · exact False.elim (hn rfl)
          · exact lt_of_le_of_lt (stieltjesNumerator_natDegree_le b g) (Nat.lt_succ_self k)
        simpa only [Fintype.card_fin,Polynomial.natDegree_neg] using max_lt hR hS
  have h := Polynomial.modByMonic_add_div P F
  rw [hrem,hQ] at h
  calc
    P = -stieltjesNumerator b g + F*(X+C ((P /ₘ F).coeff 0)) := h.symm
    _ = _ := by change -stieltjesNumerator b g + F*(X+C ((P /ₘ F).coeff 0)) =
                      (X+C ((P /ₘ F).coeff 0))*F-stieltjesNumerator b g
                ring

end HydrologyTree
