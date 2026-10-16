import CircuitCompletion.Givens

open scoped BigOperators ComplexOrder
open Matrix
namespace CircuitCompletion

noncomputable def coordinatePair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) : Fin 2 ↪ ι :=
  ⟨![p,q],by intro i j h;fin_cases i <;> fin_cases j <;> simp_all⟩

theorem coordinatePair_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) : coordinatePair p q hpq 0=p := rfl

theorem coordinatePair_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) : coordinatePair p q hpq 1=q := rfl

noncomputable def pairPlane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) : Matrix ι (Fin 2) ℂ :=
  Extraction.coordinateIsometry (coordinatePair p q hpq)

theorem pairPlane_isometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) : (pairPlane p q hpq)ᴴ*pairPlane p q hpq=1 :=
  Extraction.coordinateIsometry_isometry _

theorem pairPlane_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) (v : Fin 2 → ℂ) :
    pairPlane p q hpq*ᵥv=Pi.single p (v 0)+Pi.single q (v 1) := by
  ext i
  simp [pairPlane,Extraction.coordinateIsometry,coordinatePair_zero,coordinatePair_one,Matrix.mulVec,
    dotProduct,Fin.sum_univ_two,Pi.single_apply,eq_comm]

theorem pairPlane_adjoint_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) (v : ι → ℂ) :
    (pairPlane p q hpq)ᴴ*ᵥv=![v p,v q] := by
  ext i
  fin_cases i <;>
    simp [pairPlane,Extraction.coordinateIsometry,coordinatePair_zero,coordinatePair_one,Matrix.mulVec,
      dotProduct,Matrix.conjTranspose_apply,eq_comm]

theorem embedPlane_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Matrix ι (Fin 2) ℂ) (hE : Eᴴ*E=1) (G : Matrix.unitaryGroup (Fin 2) ℂ)
    (v : ι → ℂ) :
    (embedPlane E hE G : Matrix ι ι ℂ)*ᵥv=
      E*ᵥ((G : Matrix (Fin 2) (Fin 2) ℂ)*ᵥ(Eᴴ*ᵥv))+(v-E*ᵥ(Eᴴ*ᵥv)) := by
  change (E*(G : Matrix (Fin 2) (Fin 2) ℂ)*Eᴴ+(1-E*Eᴴ))*ᵥv=_
  simp only [Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,← Matrix.mulVec_mulVec]

noncomputable def mergeAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Matrix.unitaryGroup ι ℂ :=
  embedPlane (pairPlane p q hpq) (pairPlane_isometry p q hpq) (mergeRotation a b ha hb)

/-- This explicit two-level matrix changes exactly the two selected
coordinates, with its action proved on an arbitrary ambient vector. -/
theorem mergeAt_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι) (hpq : p≠q) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (v : ι → ℂ) (hp : v p=(Real.sqrt a:ℂ)) (hq : v q=(Real.sqrt b:ℂ)) :
    (mergeAt p q hpq a b ha hb : Matrix ι ι ℂ)*ᵥv=
      Pi.single p (Real.sqrt (a+b):ℂ)+
        (v-(Pi.single p (Real.sqrt a:ℂ)+Pi.single q (Real.sqrt b:ℂ))) := by
  rw [mergeAt,embedPlane_apply,pairPlane_adjoint_mulVec,hp,hq,mergeRotation_action,
    pairPlane_mulVec,pairPlane_mulVec]
  simp

/-- Three actual Givens operations compress four nonnegative amplitudes. -/
noncomputable def compressFour (a : Fin 4 → ℝ) (ha : ∀ i,0 ≤ a i) :
    Matrix.unitaryGroup (Fin 4) ℂ :=
  mergeAt (0:Fin 4) 3 (by decide) (a 0+a 1+a 2) (a 3)
    (add_nonneg (add_nonneg (ha 0) (ha 1)) (ha 2)) (ha 3)*
  mergeAt (0:Fin 4) 2 (by decide) (a 0+a 1) (a 2) (add_nonneg (ha 0) (ha 1)) (ha 2)*
  mergeAt (0:Fin 4) 1 (by decide) (a 0) (a 1) (ha 0) (ha 1)

theorem compressFour_action (a : Fin 4 → ℝ) (ha : ∀ i,0 ≤ a i) :
    (compressFour a ha : Matrix (Fin 4) (Fin 4) ℂ)*ᵥ(fun i => (Real.sqrt (a i):ℂ))=
      Pi.single 0 (Real.sqrt (∑ i,a i):ℂ) := by
  let v : Fin 4 → ℂ := fun i => (Real.sqrt (a i):ℂ)
  let v₁ : Fin 4 → ℂ := ![(Real.sqrt (a 0+a 1):ℂ),0,(Real.sqrt (a 2):ℂ),(Real.sqrt (a 3):ℂ)]
  let v₂ : Fin 4 → ℂ := ![(Real.sqrt (a 0+a 1+a 2):ℂ),0,0,(Real.sqrt (a 3):ℂ)]
  have h₁ : (mergeAt (0:Fin 4) 1 (by decide) (a 0) (a 1) (ha 0) (ha 1) : Matrix (Fin 4) (Fin 4) ℂ)*ᵥv=v₁ := by
    rw [mergeAt_action _ _ _ _ _ _ _ v rfl rfl]
    ext i;fin_cases i <;> simp [v,v₁,Pi.single_apply,Matrix.vecHead,Matrix.vecTail]
  have h₂ : (mergeAt (0:Fin 4) 2 (by decide) (a 0+a 1) (a 2)
      (add_nonneg (ha 0) (ha 1)) (ha 2) : Matrix (Fin 4) (Fin 4) ℂ)*ᵥv₁=v₂ := by
    rw [mergeAt_action _ _ _ _ _ _ _ v₁ rfl rfl]
    ext i;fin_cases i <;> simp [v₁,v₂,Pi.single_apply,Matrix.vecHead,Matrix.vecTail]
  have h₃ : (mergeAt (0:Fin 4) 3 (by decide) (a 0+a 1+a 2) (a 3)
      (add_nonneg (add_nonneg (ha 0) (ha 1)) (ha 2)) (ha 3) : Matrix (Fin 4) (Fin 4) ℂ)*ᵥv₂=
        Pi.single 0 (Real.sqrt (∑ i,a i):ℂ) := by
    rw [mergeAt_action _ _ _ _ _ _ _ v₂ rfl rfl]
    ext i;fin_cases i <;> simp [v₂,Pi.single_apply,Matrix.vecHead,Matrix.vecTail,Fin.sum_univ_succ,add_assoc]
  change (compressFour a ha : Matrix (Fin 4) (Fin 4) ℂ)*ᵥv=_
  simp only [compressFour,Matrix.UnitaryGroup.mul_val,← Matrix.mulVec_mulVec]
  rw [h₁,h₂,h₃]

end CircuitCompletion
