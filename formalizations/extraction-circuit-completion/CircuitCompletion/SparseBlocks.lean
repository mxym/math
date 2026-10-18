import CircuitCompletion.CompiledGivens

open scoped BigOperators
open Matrix
namespace CircuitCompletion

theorem mergeRotation_zero_right (a : ℝ) (ha : 0≤a) : mergeRotation a 0 ha (by rfl)=1 := by
  by_cases h : a=0
  · subst a;simp [mergeRotation]
  · have hp : 0<a := lt_of_le_of_ne ha (Ne.symm h)
    have hs : Real.sqrt a≠0 := (Real.sqrt_pos.mpr hp).ne'
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mergeRotation,h,Real.sqrt_zero,hs,rotationUnitary,rotationMatrix]

theorem embedPlane_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι (Fin 2) ℂ) (hE : Eᴴ*E=1) : embedPlane E hE 1=1 := by
  apply Subtype.ext
  change E*1*Eᴴ+(1-E*Eᴴ)=1
  rw [Matrix.mul_one]
  abel

theorem mergeAt_zero_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) (a : ℝ) (ha : 0≤a) : mergeAt p q hpq a 0 ha (by rfl)=1 := by
  rw [mergeAt,mergeRotation_zero_right,embedPlane_one]

theorem mergeAt_fixes_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (v : ι → ℂ) (hp : v p=0) (hq : v q=0) :
    (mergeAt p q hpq a b ha hb : Matrix ι ι ℂ)*ᵥv=v := by
  rw [mergeAt,embedPlane_apply,pairPlane_adjoint_mulVec,hp,hq]
  have hz : (![0,0] : Fin 2 → ℂ)=0 := by ext i;fin_cases i <;> rfl
  simp [hz]

theorem isometry_embedPlane_intertwine {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (E : Matrix ι κ ℂ) (hE : Eᴴ*E=1)
    (F : Matrix κ (Fin 2) ℂ) (hF : Fᴴ*F=1) (G : Matrix.unitaryGroup (Fin 2) ℂ) :
    (embedPlane (E*F) (by
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Eᴴ,hE,Matrix.one_mul,hF]) G : Matrix ι ι ℂ)*E=
        E*(embedPlane F hF G : Matrix κ κ ℂ) := by
  change ((E*F)*(G : Matrix (Fin 2) (Fin 2) ℂ)*(E*F)ᴴ+
    (1-(E*F)*(E*F)ᴴ))*E=E*(F*(G : Matrix (Fin 2) (Fin 2) ℂ)*Fᴴ+(1-F*Fᴴ))
  simp only [Matrix.conjTranspose_mul,Matrix.add_mul,Matrix.sub_mul,Matrix.one_mul,
    Matrix.mul_add,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_assoc]
  simp only [hE,Matrix.mul_one]

theorem coordinateIsometry_pairPlane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Fin 4 ↪ ι) (p q : Fin 4) (hpq : p≠q) :
    Extraction.coordinateIsometry e*pairPlane p q hpq=
      pairPlane (e p) (e q) (by exact fun h => hpq (e.injective h)) := by
  ext w j
  fin_cases j
  · fin_cases p <;>
      simp [pairPlane,Extraction.coordinateIsometry,coordinatePair_zero,coordinatePair_one,
        Matrix.mul_apply,Fin.sum_univ_succ] <;> rfl
  · fin_cases q <;>
      simp [pairPlane,Extraction.coordinateIsometry,coordinatePair_zero,coordinatePair_one,
        Matrix.mul_apply,Fin.sum_univ_succ] <;> rfl

end CircuitCompletion
