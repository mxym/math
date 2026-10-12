import APPTReview.SchmidtModel
import APPTReview.SOS

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a : Type*} [Fintype a] [LinearOrder a]

def schmidtMass (s : a → ℝ) : ℝ := ∑ p : a × a, schmidtNegative s p

theorem schmidtMass_nonneg (s : a → ℝ) (hs : ∀ i,0≤s i) : 0≤schmidtMass s :=
  Finset.sum_nonneg (fun p _ => schmidtNegative_nonneg s hs p)

/-- Sum of all negative pure eigenvalues, not a bound obtained from sampled vectors. -/
theorem schmidtMass_identity (s : a → ℝ) :
    2*schmidtMass s=(∑ i,s i)^2-∑ i,(s i)^2 := by
  have hp (p : a × a) : s p.1*s p.2=
      (if p.1=p.2 then (s p.1)^2 else 0)+schmidtNegative s p+schmidtNegative s p.swap := by
    rcases p with ⟨i,j⟩
    rcases lt_trichotomy i j with h | h | h
    · simp [schmidtNegative,h,ne_of_lt h,not_lt_of_gt h,mul_comm]
    · subst j
      simp [schmidtNegative,pow_two]
    · simp [schmidtNegative,h,ne_of_gt h,not_lt_of_gt h,mul_comm]
  have he := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun p _ => hp p)
  have hprod : (∑ p : a × a,s p.1*s p.2)=(∑ i,s i)^2 := by
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,← Finset.sum_mul,pow_two]
  have hdiag : (∑ p : a × a,if p.1=p.2 then (s p.1)^2 else 0)=∑ i,(s i)^2 := by
    simp [Fintype.sum_prod_type]
  have hswap : (∑ p : a × a,schmidtNegative s p.swap)=schmidtMass s :=
    (Equiv.prodComm a a).sum_comp (schmidtNegative s)
  simp only [Finset.sum_add_distrib] at he
  rw [hprod,hdiag,hswap] at he
  unfold schmidtMass at *
  linarith

/-- The scalar positivity margin without selecting or sorting the largest Schmidt pair. -/
theorem schmidt_joint_background_nonneg (s : a → ℝ)
    (hc : 4≤Fintype.card a) (hsq : (∑ i,(s i)^2)=1) :
    0≤(2*(Fintype.card a:ℝ)-5)-2*schmidtMass s := by
  rw [schmidtMass_identity,hsq]
  have hh := tail_cauchy s
  rw [hsq] at hh
  have hcr : (4:ℝ)≤Fintype.card a := by exact_mod_cast hc
  linarith


end APPTReview
