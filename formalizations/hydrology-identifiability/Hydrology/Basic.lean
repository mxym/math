import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace HydrologyIdentifiability

noncomputable section

/-- Positive parameters of a two-storage linear rainfall-runoff model.

The equations are
  x₁' = p - (a+b)x₁ + c x₂,
  x₂' = b x₁ - c x₂,
  Q = a x₁.
-/
structure Params where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c

/-- The two coefficients visible in the eliminated scalar output equation. -/
def totalRate (θ : Params) : ℝ := θ.a + θ.b + θ.c
def productRate (θ : Params) : ℝ := θ.a * θ.c

/-- A pointwise output jet and its rainfall jet. -/
structure Jet where
  q : ℝ
  q₁ : ℝ
  q₂ : ℝ
  p : ℝ
  p₁ : ℝ

/-- The two-storage equations and the output relation at a point. -/
structure StateJet (θ : Params) (J : Jet) where
  x₁ : ℝ
  x₂ : ℝ
  x₁₁ : ℝ
  x₂₁ : ℝ
  x₁₂ : ℝ
  q_eq : J.q = θ.a * x₁
  x1_eq : x₁₁ = J.p - (θ.a + θ.b) * x₁ + θ.c * x₂
  x2_eq : x₂₁ = θ.b * x₁ - θ.c * x₂
  x1₂_eq : x₁₂ = J.p₁ - (θ.a + θ.b) * x₁₁ + θ.c * x₂₁
  q1_eq : J.q₁ = θ.a * x₁₁
  q2_eq : J.q₂ = θ.a * x₁₂

/-- Exact elimination of the two storage variables at the level of 2-jets.

This is the local algebraic identity induced by differentiating the model once.
The `StateJet` fields make every regularity assumption explicit; no numerical or
ODE solver is part of the theorem.
-/
theorem output_elimination (θ : Params) (J : Jet) (h : StateJet θ J) :
    J.q₂ + totalRate θ * J.q₁ + productRate θ * J.q =
      θ.a * J.p₁ + productRate θ * J.p := by
  rcases h with ⟨x₁, x₂, x₁₁, x₂₁, x₁₂, hq, hx1, hx2, hx12, hq1, hq2⟩
  dsimp [totalRate, productRate]
  rw [hq, hq1, hq2]
  rw [hx12, hx1, hx2]
  ring

/-- Equilibrium state for constant positive rainfall. -/
def equilibrium (θ : Params) (p : ℝ) : ℝ × ℝ :=
  (p / θ.a, θ.b * p / (θ.a * θ.c))

/-- The algebraic conditions for a constant (stationary) state and discharge.
Constant functions with these values solve the model ODE exactly, so this is a
finite certificate for an all-time output trajectory, rather than a sampled
numerical fit. -/
def StationaryOutput (θ : Params) (p x₁ x₂ q : ℝ) : Prop :=
  q = θ.a * x₁ ∧
  p - (θ.a + θ.b) * x₁ + θ.c * x₂ = 0 ∧
  θ.b * x₁ - θ.c * x₂ = 0

theorem stationary_equilibrium (θ : Params) (p : ℝ) :
    StationaryOutput θ p (equilibrium θ p).1 (equilibrium θ p).2 p := by
  dsimp [StationaryOutput, equilibrium]
  constructor
  · field_simp [ne_of_gt θ.ha]
  constructor <;> field_simp [ne_of_gt θ.ha, ne_of_gt θ.hc] <;> ring

/-- The equilibrium output equals the rainfall. -/
theorem equilibrium_output (θ : Params) (p : ℝ) :
    θ.a * (equilibrium θ p).1 = p := by
  dsimp [equilibrium]
  field_simp [ne_of_gt θ.ha]

/-- Two distinct positive parameter triples have the same eliminated coefficients. -/
def thetaA : Params :=
  { a := 2, b := 2, c := 2, ha := by norm_num, hb := by norm_num, hc := by norm_num }
def thetaB : Params :=
  { a := 1, b := 1, c := 4, ha := by norm_num, hb := by norm_num, hc := by norm_num }

theorem thetaA_thetaB_distinct : thetaA.a ≠ thetaB.a := by norm_num [thetaA, thetaB]
theorem thetaA_thetaB_same_total : totalRate thetaA = totalRate thetaB := by norm_num [totalRate, thetaA, thetaB]
theorem thetaA_thetaB_same_product : productRate thetaA = productRate thetaB := by norm_num [productRate, thetaA, thetaB]

/-- Every positive rate triple lies on an explicit one-parameter fibre of the
same eliminated coefficients.  The second and third rates are recovered from
the chosen first rate and the invariants `S,P`. -/
theorem parameter_fibre_identity (θ : Params) :
    θ.b = totalRate θ - θ.a - productRate θ / θ.a ∧
    θ.c = productRate θ / θ.a := by
  have ha0 : θ.a ≠ 0 := ne_of_gt θ.ha
  constructor
  · dsimp [totalRate, productRate]
    field_simp [ha0]
    ring
  · dsimp [productRate]
    field_simp [ha0]

/-- Conversely, any positive choice of `a` for which the reconstructed `b,c`
are positive gives a positive parameter triple with prescribed invariants. -/
def fibreParams (S P a : ℝ) (ha : 0 < a) (hb : 0 < S - a - P / a)
    (hc : 0 < P / a) : Params :=
  { a := a, b := S - a - P / a, c := P / a, ha := ha, hb := hb, hc := hc }

theorem fibreParams_totalRate (S P a : ℝ) (ha : 0 < a)
    (hb : 0 < S - a - P / a) (hc : 0 < P / a) :
    totalRate (fibreParams S P a ha hb hc) = S := by
  dsimp [totalRate, fibreParams]
  ring

theorem fibreParams_productRate (S P a : ℝ) (ha : 0 < a)
    (hb : 0 < S - a - P / a) (hc : 0 < P / a) :
    productRate (fibreParams S P a ha hb hc) = P := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  dsimp [productRate, fibreParams]
  field_simp [ha0]

/-- Exact physical equifinality under constant rainfall: both systems have the
same equilibrium discharge, although their parameters and storage partition differ. -/
theorem thetaA_thetaB_equifinal (p : ℝ) :
    thetaA.a * (equilibrium thetaA p).1 =
      thetaB.a * (equilibrium thetaB p).1 := by
  rw [equilibrium_output, equilibrium_output]

theorem thetaA_thetaB_stationary_unit :
    StationaryOutput thetaA 1 (1 / 2) (1 / 2) 1 ∧
    StationaryOutput thetaB 1 1 (1 / 4) 1 := by
  constructor <;> norm_num [StationaryOutput, thetaA, thetaB]

theorem thetaA_thetaB_storage_partition_diff (p : ℝ) (hp : p ≠ 0) :
    (equilibrium thetaA p).1 ≠ (equilibrium thetaB p).1 := by
  dsimp [equilibrium, thetaA, thetaB]
  intro h
  apply hp
  linarith

end
end HydrologyIdentifiability
