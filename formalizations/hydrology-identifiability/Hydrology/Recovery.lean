import Hydrology.Basic

namespace HydrologyIdentifiability

/-- Zero-initial-state output jets for constant rainfall. -/
structure ZeroInitialJets (θ : Params) (p : ℝ) where
  q₁ : ℝ
  q₂ : ℝ
  q₃ : ℝ
  hq₁ : q₁ = θ.a * p
  hq₂ : q₂ = - θ.a * (θ.a + θ.b) * p
  hq₃ : q₃ = θ.a * ((θ.a + θ.b)^2 + θ.b * θ.c) * p

/-- Jets from two constant-rainfall experiments that start from the same
unknown storage state.  Subtracting the two hydrographs cancels that state;
the displayed hypotheses are exactly the resulting difference identities. -/
structure PairedDifferenceJets (θ : Params) (pHi pLo : ℝ) where
  u1 : ℝ
  v1 : ℝ
  u2 : ℝ
  v2 : ℝ
  u3 : ℝ
  v3 : ℝ
  hq₁ : u1 - v1 = θ.a * (pHi - pLo)
  hq₂ : u2 - v2 = -θ.a * (θ.a + θ.b) * (pHi - pLo)
  hq₃ : u3 - v3 = θ.a * ((θ.a + θ.b)^2 + θ.b * θ.c) * (pHi - pLo)

/-- Recovery of the three positive rates from the first three output derivatives.
The theorem is purely exact algebra, so it is independent of discretization and
floating-point conditioning. -/
theorem recover_parameters
    (θ : Params) (p : ℝ) (hp : 0 < p) (J : ZeroInitialJets θ p) :
    θ.a = J.q₁ / p ∧
    θ.b = (-J.q₂ / J.q₁) - (J.q₁ / p) ∧
    θ.c = (J.q₃ / J.q₁ - (-J.q₂ / J.q₁)^2) /
      ((-J.q₂ / J.q₁) - (J.q₁ / p)) := by
  have ha0 : θ.a ≠ 0 := ne_of_gt θ.ha
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hq10 : J.q₁ ≠ 0 := by rw [J.hq₁]; positivity
  have hb0 : θ.b ≠ 0 := ne_of_gt θ.hb
  have hB : (-J.q₂ / J.q₁) = θ.a + θ.b := by
    rw [J.hq₂, J.hq₁]
    field_simp
  have hA : J.q₁ / p = θ.a := by
    rw [J.hq₁]
    field_simp
  have hC : J.q₃ / J.q₁ - (-J.q₂ / J.q₁)^2 = θ.b * θ.c := by
    rw [J.hq₃, J.hq₁, J.hq₂]
    field_simp [ha0, hp0]
    ring
  constructor
  · exact hA.symm
  constructor
  · rw [hB, hA]
    ring
  · rw [hC, hB, hA]
    field_simp [hb0]
    ring

/-- Two ordered rainfall experiments identify the same three rates even when
the common initial storage is unknown.  Only the difference hydrograph is used;
its initial state is zero by cancellation. -/
theorem recover_from_two_common_state_experiments
    (θ : Params) (pHi pLo : ℝ) (hRain : pLo < pHi)
    (J : PairedDifferenceJets θ pHi pLo) :
    θ.a = (J.u1 - J.v1) / (pHi - pLo) ∧
    θ.b = (-(J.u2 - J.v2) / (J.u1 - J.v1)) -
      ((J.u1 - J.v1) / (pHi - pLo)) ∧
    θ.c = ((J.u3 - J.v3) / (J.u1 - J.v1) -
      (-(J.u2 - J.v2) / (J.u1 - J.v1))^2) /
      ((-(J.u2 - J.v2) / (J.u1 - J.v1)) -
        ((J.u1 - J.v1) / (pHi - pLo))) := by
  let D : ZeroInitialJets θ (pHi - pLo) :=
    { q₁ := J.u1 - J.v1
      q₂ := J.u2 - J.v2
      q₃ := J.u3 - J.v3
      hq₁ := J.hq₁
      hq₂ := J.hq₂
      hq₃ := J.hq₃ }
  have hD := recover_parameters θ (pHi - pLo) (by linarith) D
  simpa [D] using hD

/-- A concrete exact recovery instance, useful as an executable regression test. -/
def sampleJets : ZeroInitialJets thetaA 3 :=
  { q₁ := 6, q₂ := -24, q₃ := 120
    hq₁ := by norm_num [thetaA]
    hq₂ := by norm_num [thetaA]
    hq₃ := by norm_num [thetaA] }

theorem sample_recovery :
    thetaA.a = sampleJets.q₁ / 3 ∧
    thetaA.b = (-sampleJets.q₂ / sampleJets.q₁) - (sampleJets.q₁ / 3) ∧
    thetaA.c = (sampleJets.q₃ / sampleJets.q₁ - (-sampleJets.q₂ / sampleJets.q₁)^2) /
      ((-sampleJets.q₂ / sampleJets.q₁) - (sampleJets.q₁ / 3)) := by
  have h := recover_parameters thetaA 3 (by norm_num) sampleJets
  exact h

end HydrologyIdentifiability
