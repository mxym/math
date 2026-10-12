import APPTReview.SchmidtPartialTranspose
import APPTReview.Hadamard

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview
variable {a : Type*} [Fintype a] [LinearOrder a]

def schmidtSigned (s : a → ℝ) (p : a × a) : ℝ :=
  if p.1=p.2 then (s p.1)^2 else if p.1<p.2 then s p.1*s p.2 else -(s p.1*s p.2)

/-- All positive and negative pure partial-transpose eigenvalues, simultaneously. -/
theorem hadamard_schmidt_exchange (s : a → ℝ) :
    hadamard (a:=a)*schmidtExchange s=
      Matrix.diagonal (fun p => (schmidtSigned s p:ℂ))*hadamard := by
  classical
  ext ⟨i,j⟩ ⟨k,l⟩
  rw [hadamard_mul_apply,Matrix.diagonal_mul]
  by_cases hij : i=j
  · subst j
    simp [schmidtExchange,schmidtSigned,hadamard]
    split_ifs <;> push_cast <;> ring
  · have hji : j≠i := Ne.symm hij
    by_cases h1 : (i,j)=(k,l)
    · have hk : k=i := (congrArg Prod.fst h1).symm
      have hl : l=j := (congrArg Prod.snd h1).symm
      subst k
      subst l
      by_cases hlt : i<j <;>
        simp [schmidtExchange,schmidtSigned,hadamard,hij,hji,hlt]
        <;> push_cast <;> ring
    · by_cases h2 : (j,i)=(k,l)
      · have hk : k=j := (congrArg Prod.fst h2).symm
        have hl : l=i := (congrArg Prod.snd h2).symm
        subst k
        subst l
        by_cases hlt : i<j <;>
          simp [schmidtExchange,schmidtSigned,hadamard,hij,hji,hlt]
          <;> push_cast <;> ring
      · simp [schmidtExchange,schmidtSigned,hadamard,hij,hji,h1,h2]

/-- Exact diagonalization of the weighted exchange by the already checked Hadamard unitary. -/
theorem schmidtExchange_diagonalization (s : a → ℝ) :
    schmidtExchange s=hadamard (a:=a)*Matrix.diagonal (fun p => (schmidtSigned s p:ℂ))*hadamardᴴ := by
  have hh := congrArg (fun M : Matrix (a × a) (a × a) ℂ => hadamard*M)
    (hadamard_schmidt_exchange s)
  simpa only [← Matrix.mul_assoc,hadamard_sq,Matrix.one_mul,hadamard_conjTranspose] using hh

/-- The explicit ordered-pair sum of negative pure-state eigenvalue magnitudes. -/
def schmidtNegative (s : a → ℝ) (p : a × a) : ℝ :=
  if p.2<p.1 then s p.1*s p.2 else 0

theorem schmidtNegative_nonneg (s : a → ℝ) (hs : ∀ i,0≤s i) (p : a × a) :
    0≤schmidtNegative s p := by
  unfold schmidtNegative
  split_ifs
  · exact mul_nonneg (hs _) (hs _)
  · exact le_refl _

theorem schmidtSigned_add_negative_nonneg (s : a → ℝ) (hs : ∀ i,0≤s i) (p : a × a) :
    0≤schmidtSigned s p+schmidtNegative s p := by
  unfold schmidtSigned schmidtNegative
  have hp := hs p.1
  have hq := hs p.2
  by_cases he : p.1=p.2
  · simp only [he,ite_true,lt_self_iff_false,ite_false,add_zero]
    exact sq_nonneg _
  · by_cases hl : p.1<p.2
    · simp [he,hl,not_lt_of_gt hl]
      exact mul_nonneg hp hq
    · have hrev : p.2<p.1 := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
      simp [he,hl,hrev]

end APPTReview
