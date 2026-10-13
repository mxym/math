import APPTReview.OuterValues

namespace APPTReview

/-- Exact continuous-envelope gap for the spike branch of the outer cut. -/
theorem outerSpike_deficit_identity (m D : ℝ) (hm : m^2-1≠0) (hd : D+m≠0) :
    m^2/(m^2-1)-D*((D+m*(m+2))/(D+m)^2)=
      (D^2-(m^4-m^2-2*m)*D+m^4)/((m^2-1)*(D+m)^2) := by
  generalize hz : D+m=z at *
  field_simp
  rw [← hz]
  ring

/-- A uniform real comparison absorbs the integer-rounding loss. In particular
no parity or finite table is needed to prove the sufficient rectangular cutoff. -/
theorem outerSpike_lt_rounded_model (m D H s : ℝ)
    (hm : 3 ≤ m) (hD : m^2 ≤ D) (hcut : m^4-m^2-2*m ≤ D)
    (hH : 0 < H) (hHD : m*H=(m^2-1)*D) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    D*((D+m*(m+2))/(D+m)^2) <
      m^2/(m^2-1)-(m^2/(m^2-1))*s^2/(H+s)^2 := by
  let u := m^2-1
  let C := m^2/u
  have hmP : 0 < m := by linarith
  have hu : 0 < u := by dsimp [u]; nlinarith
  have hDP : 0 < D := by nlinarith
  have hDM : 0 < D+m := by positivity
  have hC : 0 < C := div_pos (sq_pos_of_pos hmP) hu
  have hS : 0 < H+s := by positivity
  have hshort : D+m < m*H := by
    have htwo : 2 < u := by dsimp [u]; nlinarith
    have hx := mul_lt_mul_of_pos_right htwo hDP
    change m*H=u*D at hHD
    nlinarith
  have hsquare : (D+m)^2 < (m*H)^2 := by nlinarith
  have hround : C*s^2/(H+s)^2 ≤ C/H^2 := by
    have hss : s^2 ≤ 1 := by nlinarith
    calc
      _ ≤ C/(H+s)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_left hC.le (sq_pos_of_pos hH) (by nlinarith)
  have hstrict : C/H^2 < m^4/(u*(D+m)^2) := by
    dsimp [C]
    rw [div_div]
    apply (div_lt_div_iff₀ (mul_pos hu (sq_pos_of_pos hH))
      (mul_pos hu (sq_pos_of_pos hDM))).2
    have he := mul_lt_mul_of_pos_left hsquare (mul_pos hu (sq_pos_of_pos hmP))
    nlinarith
  have hsp : m^4/(u*(D+m)^2) ≤ C-D*((D+m*(m+2))/(D+m)^2) := by
    rw [show C=m^2/(m^2-1) by rfl,outerSpike_deficit_identity m D (ne_of_gt hu) (ne_of_gt hDM)]
    apply div_le_div_of_nonneg_right _ (mul_nonneg hu.le (sq_nonneg _))
    have he := mul_nonneg hDP.le (sub_nonneg.mpr hcut)
    nlinarith
  have hlt := hround.trans_lt (hstrict.trans_le hsp)
  change D*((D+m*(m+2))/(D+m)^2) < C-C*s^2/(H+s)^2
  linarith

/-- The specified integer dimension cutoff makes the physical plateau branch
strictly dominate the other branch of the unrestricted outer-polytope bound. -/
theorem outerSpike_lt_roundedPlateau {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n)
    (hcut : m^3-m-2 ≤ n) : outerSpikePurity m n < roundedPlateauPurity m n := by
  let t := ((m-1)*n+1)/2
  let D : ℝ := (m:ℝ)*n
  let H : ℝ := ((m:ℝ)^2-1)*n
  let s : ℝ := 2*(t:ℝ)-((m:ℝ)-1)*n
  let C : ℝ := (m:ℝ)^2/((m:ℝ)^2-1)
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  have hmP : (0:ℝ) < m := by linarith
  have hnP : (0:ℝ) < n := by linarith
  have hu : (0:ℝ) < (m:ℝ)^2-1 := by nlinarith
  have hDP : 0 < D := mul_pos hmP hnP
  have hD : (m:ℝ)^2 ≤ D := by dsimp [D]; nlinarith
  have hnat : m+2 ≤ m^3 := by
    have h1 := Nat.mul_le_mul_left m hm
    have h2 := Nat.mul_le_mul_left (m*m) hm
    nlinarith
  have hcast : ((m^3-m-2:ℕ):ℝ)=(m:ℝ)^3-m-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m^3-m),Nat.cast_sub (by omega : m ≤ m^3),
      Nat.cast_pow,Nat.cast_ofNat]
  have hncut : (m:ℝ)^3-m-2 ≤ (n:ℝ) := by rw [← hcast]; exact_mod_cast hcut
  have hDcut : (m:ℝ)^4-(m:ℝ)^2-2*m ≤ D := by
    have he := mul_le_mul_of_nonneg_left hncut hmP.le
    dsimp [D]
    nlinarith
  have hroundN : (m-1)*n ≤ 2*t ∧ 2*t ≤ (m-1)*n+1 := by dsimp [t]; omega
  have hcast2 : (((m-1)*n:ℕ):ℝ)=((m:ℝ)-1)*n := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one]
  have hr0 : ((m:ℝ)-1)*n ≤ 2*(t:ℝ) := by rw [← hcast2]; exact_mod_cast hroundN.1
  have hr1 : 2*(t:ℝ) ≤ ((m:ℝ)-1)*n+1 := by rw [← hcast2]; exact_mod_cast hroundN.2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hHP : 0 < H := mul_pos hu hnP
  have hHD : (m:ℝ)*H=((m:ℝ)^2-1)*D := by dsimp [H,D];ring
  have hZ : H+s=plateauDenominator m n t := by dsimp [H,s,plateauDenominator];ring
  have hZP : 0 < plateauDenominator m n t := plateauDenominator_pos (by omega) (by omega) t
  have hmodel := outerSpike_lt_rounded_model (m:ℝ) D H s hmR hD hDcut hHP hHD hs hs1
  have hid := plateau_rounding_identity (m:ℝ) (n:ℝ) (t:ℝ) (ne_of_gt hu) (ne_of_gt hZP)
  have hpure : C-plateauScaledPurity m n t=C*s^2/(H+s)^2 := by
    rw [hZ]
    simpa only [C,s,plateauScaledPurity,plateauDenominator] using hid
  have hscaled : D*roundedPlateauPurity m n=plateauScaledPurity m n t := by
    unfold roundedPlateauPurity
    change D*(plateauScaledPurity m n t/D)=_
    field_simp
  have hout : D*outerSpikePurity m n=D*((D+(m:ℝ)*((m:ℝ)+2))/(D+m)^2) := rfl
  apply (mul_lt_mul_iff_right₀ hDP).mp
  rw [hout,hscaled]
  change D*((D+(m:ℝ)*((m:ℝ)+2))/(D+m)^2) < C-C*s^2/(H+s)^2 at hmodel
  linarith

end APPTReview
