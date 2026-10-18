import CircuitRecursion.InputDensity

open scoped Matrix.Norms.L2Operator
open Matrix CircuitCompletion
namespace CircuitRecursion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def unitaryDistance (A B : Matrix.unitaryGroup ι ℂ) : ℝ :=
  ‖(A : Matrix ι ι ℂ)-(B : Matrix ι ι ℂ)‖

theorem unitaryDistance_nonneg (A B : Matrix.unitaryGroup ι ℂ) : 0≤unitaryDistance A B :=
  norm_nonneg _

theorem unitaryDistance_symm (A B : Matrix.unitaryGroup ι ℂ) :
    unitaryDistance A B=unitaryDistance B A := norm_sub_rev _ _

theorem unitaryDistance_triangle (A B C : Matrix.unitaryGroup ι ℂ) :
    unitaryDistance A C≤unitaryDistance A B+unitaryDistance B C := by
  simpa only [unitaryDistance,dist_eq_norm] using
    dist_triangle (A : Matrix ι ι ℂ) (B : Matrix ι ι ℂ) (C : Matrix ι ι ℂ)

theorem unitaryDistance_mul_right (A B C : Matrix.unitaryGroup ι ℂ) :
    unitaryDistance (A*C) (B*C)=unitaryDistance A B := by
  simp only [unitaryDistance,Matrix.UnitaryGroup.mul_val,← Matrix.sub_mul,
    CStarRing.norm_mul_coe_unitary]

theorem unitaryDistance_mul_left (A B C : Matrix.unitaryGroup ι ℂ) :
    unitaryDistance (C*A) (C*B)=unitaryDistance A B := by
  simp only [unitaryDistance,Matrix.UnitaryGroup.mul_val,← Matrix.mul_sub,
    CStarRing.norm_coe_unitary_mul]

theorem unitaryDistance_star (A B : Matrix.unitaryGroup ι ℂ) :
    unitaryDistance (star A) (star B)=unitaryDistance A B := by
  simpa only [unitaryDistance,star_sub,Unitary.coe_star,Matrix.star_eq_conjTranspose] using
    norm_star ((A : Matrix ι ι ℂ)-(B : Matrix ι ι ℂ))

/-- Conjugation errors vanish linearly with the distance of the conjugated
unitary from identity. This cancellation is proved from matrix algebra. -/
theorem unitaryDistance_conjugation (A B X : Matrix.unitaryGroup ι ℂ) :
    unitaryDistance (A*X*star A) (B*X*star B)≤
      2*unitaryDistance A B*unitaryDistance X 1 := by
  have hA : (A : Matrix ι ι ℂ)*(star A : Matrix ι ι ℂ)=1 :=
    Unitary.coe_mul_star_self A
  have hB : (B : Matrix ι ι ℂ)*(star B : Matrix ι ι ℂ)=1 :=
    Unitary.coe_mul_star_self B
  have hshift (U : Matrix.unitaryGroup ι ℂ)
      (hU : (U : Matrix ι ι ℂ)*(star U : Matrix ι ι ℂ)=1) :
      (U : Matrix ι ι ℂ)*(X : Matrix ι ι ℂ)*(star U : Matrix ι ι ℂ)=
        (U : Matrix ι ι ℂ)*((X : Matrix ι ι ℂ)-1)*(star U : Matrix ι ι ℂ)+1 := by
    simp only [Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul,hU,sub_add_cancel]
  have he : (A : Matrix ι ι ℂ)*(X : Matrix ι ι ℂ)*(star A : Matrix ι ι ℂ)-
      (B : Matrix ι ι ℂ)*(X : Matrix ι ι ℂ)*(star B : Matrix ι ι ℂ)=
      ((A : Matrix ι ι ℂ)-(B : Matrix ι ι ℂ))*((X : Matrix ι ι ℂ)-1)*(star A : Matrix ι ι ℂ)+
        (B : Matrix ι ι ℂ)*(((X : Matrix ι ι ℂ)-1)*
          ((star A : Matrix ι ι ℂ)-(star B : Matrix ι ι ℂ))) := by
    rw [hshift A hA,hshift B hB]
    noncomm_ring
  change ‖(A : Matrix ι ι ℂ)*(X : Matrix ι ι ℂ)*(star A : Matrix ι ι ℂ)-
    (B : Matrix ι ι ℂ)*(X : Matrix ι ι ℂ)*(star B : Matrix ι ι ℂ)‖≤_
  rw [he]
  calc
    _ ≤ ‖((A : Matrix ι ι ℂ)-(B : Matrix ι ι ℂ))*((X : Matrix ι ι ℂ)-1)*(star A : Matrix ι ι ℂ)‖+
        ‖(B : Matrix ι ι ℂ)*(((X : Matrix ι ι ℂ)-1)*
          ((star A : Matrix ι ι ℂ)-(star B : Matrix ι ι ℂ)))‖ := norm_add_le _ _
    _ = ‖((A : Matrix ι ι ℂ)-(B : Matrix ι ι ℂ))*((X : Matrix ι ι ℂ)-1)‖+
        ‖((X : Matrix ι ι ℂ)-1)*((star A : Matrix ι ι ℂ)-(star B : Matrix ι ι ℂ))‖ := by
      exact congrArg₂ (fun x y : ℝ => x+y)
        (CStarRing.norm_mul_coe_unitary
          (((A : Matrix ι ι ℂ)-(B : Matrix ι ι ℂ))*((X : Matrix ι ι ℂ)-1)) (star A))
        (CStarRing.norm_coe_unitary_mul B
          (((X : Matrix ι ι ℂ)-1)*((star A : Matrix ι ι ℂ)-(star B : Matrix ι ι ℂ))))
    _ ≤ unitaryDistance A B*unitaryDistance X 1+
        unitaryDistance X 1*unitaryDistance (star A) (star B) :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by rw [unitaryDistance_star]; ring

def unitaryCommutator (A B : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup ι ℂ :=
  A*B*star A*star B

theorem unitaryCommutator_first_error (A A' B : Matrix.unitaryGroup ι ℂ) :
    unitaryDistance (unitaryCommutator A B) (unitaryCommutator A' B)≤
      2*unitaryDistance A A'*unitaryDistance B 1 := by
  rw [unitaryCommutator,unitaryCommutator,unitaryDistance_mul_right]
  exact unitaryDistance_conjugation A A' B

theorem unitaryCommutator_second_error (A B B' : Matrix.unitaryGroup ι ℂ) :
    unitaryDistance (unitaryCommutator A B) (unitaryCommutator A B')≤
      2*unitaryDistance B B'*unitaryDistance A 1 := by
  have he : unitaryDistance (unitaryCommutator A B) (unitaryCommutator A B')=
      unitaryDistance (B*star A*star B) (B'*star A*star B') := by
    simp only [unitaryCommutator,mul_assoc]
    exact unitaryDistance_mul_left _ _ _
  rw [he]
  have ht := unitaryDistance_conjugation B B' (star A)
  have hs : unitaryDistance (star A) 1=unitaryDistance A 1 := by
    simpa only [star_one] using unitaryDistance_star A 1
  rwa [hs] at ht

/-- Actual balanced-commutator perturbation bound used in the SK recursion.
No net, calibration, decomposition or synthesis theorem is supplied as a premise. -/
theorem unitaryCommutator_error (A B A' B' : Matrix.unitaryGroup ι ℂ)
    (δ ε : ℝ) (hδ : 0≤δ) (hε : 0≤ε)
    (hA : unitaryDistance A 1≤δ) (hB : unitaryDistance B 1≤δ)
    (hAA' : unitaryDistance A A'≤ε) (hBB' : unitaryDistance B B'≤ε) :
    unitaryDistance (unitaryCommutator A B) (unitaryCommutator A' B')≤4*δ*ε+2*ε^2 := by
  have hA' : unitaryDistance A' 1≤δ+ε := by
    have ht := unitaryDistance_triangle A' A 1
    rw [unitaryDistance_symm A' A] at ht
    linarith
  calc
    _ ≤ unitaryDistance (unitaryCommutator A B) (unitaryCommutator A' B)+
        unitaryDistance (unitaryCommutator A' B) (unitaryCommutator A' B') :=
      unitaryDistance_triangle _ _ _
    _ ≤ 2*unitaryDistance A A'*unitaryDistance B 1+
        2*unitaryDistance B B'*unitaryDistance A' 1 :=
      add_le_add (unitaryCommutator_first_error A A' B) (unitaryCommutator_second_error A' B B')
    _ ≤ 2*ε*δ+2*ε*(δ+ε) := by
      gcongr <;> exact unitaryDistance_nonneg _ _
    _ = _ := by ring

end CircuitRecursion
