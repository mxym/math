import HydrologyTree.DiagonalGauge
import HydrologyTree.ArrowCharacteristic

/-! Explicit diagonal assembly of arbitrary real child similarities. Negative
scale factors are permitted; every required nonzero denominator is stated. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {C : Type*} [Fintype C] [LinearOrder C] {V : C → Type*}
  [∀ c,Fintype (V c)] [∀ c,DecidableEq (V c)]

def arrowGaugeWeight (f b : C → ℝ) (h : ∀ c,V c → ℝ) : Unit ⊕ (Σ c,V c) → ℝ
  | .inl _ => 1
  | .inr ⟨c,i⟩ => (b c/f c)*h c i

lemma arrowGaugeWeight_nonzero (f b : C → ℝ) (h : ∀ c,V c → ℝ)
    (hf : ∀ c,f c ≠ 0) (hb : ∀ c,b c ≠ 0) (hh : ∀ c i,h c i ≠ 0) :
    ∀ v, arrowGaugeWeight f b h v ≠ 0 := by
  rintro (u | ⟨c,i⟩)
  · exact one_ne_zero
  · exact mul_ne_zero (div_ne_zero (hb c) (hf c)) (hh c i)

/-- Assemble similarities at child matrices into the actual full arrow matrix.
Matching edge PRODUCTS is enough: individual directions may initially have
arbitrary signs. The constructed gauge is normalized to one at the parent root. -/
theorem arrow_diagonal_gauge (d : ℝ) (A B : ∀ c,Matrix (V c) (V c) ℝ)
    (r : ∀ c,V c) (alpha beta a f : C → ℝ) (h : ∀ c,V c → ℝ)
    (hf : ∀ c,f c ≠ 0) (hb : ∀ c,beta c ≠ 0) (hh : ∀ c i,h c i ≠ 0)
    (hroot : ∀ c,h c (r c)=1)
    (hchild : ∀ c,A c=diagonalGauge (h c) (B c))
    (hprod : ∀ c,alpha c*beta c=a c*f c) :
    arrowMatrix d A r alpha beta=
      diagonalGauge (arrowGaugeWeight f beta h) (arrowMatrix d B r a f) := by
  ext u v
  rcases u with u | ⟨c,u⟩ <;> rcases v with v | ⟨k,v⟩
  · simp [diagonalGauge_apply,arrowMatrix,arrowGaugeWeight]
  · rw [diagonalGauge_apply]
    change (if v=r k then alpha k else 0)=
      1*(if v=r k then a k else 0)*((beta k/f k)*h k v)⁻¹
    by_cases hv : v=r k
    · subst v
      simp only [if_pos rfl,hroot,one_mul,mul_one]
      calc
        alpha k = a k*f k/beta k := (eq_div_iff (hb k)).mpr (hprod k)
        _ = a k*(beta k/f k)⁻¹ := by simp only [div_eq_mul_inv,_root_.mul_inv_rev,_root_.inv_inv]; ring
    · simp [hv]
  · rw [diagonalGauge_apply]
    change (if u=r c then beta c else 0)=
      ((beta c/f c)*h c u)*(if u=r c then f c else 0)*1⁻¹
    by_cases hu : u=r c
    · subst u
      simp [hroot,hf c]
    · simp [hu]
  · rw [diagonalGauge_apply]
    simp only [arrowMatrix,Matrix.fromBlocks_apply₂₂,arrowGaugeWeight]
    by_cases hck : c=k
    · subst k
      rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq,hchild c,diagonalGauge_apply]
      field_simp [hf c,hb c,hh c v]
      <;> ring
    · rw [Matrix.blockDiagonal'_apply_ne A u v hck,Matrix.blockDiagonal'_apply_ne B u v hck]
      simp

end HydrologyTree
