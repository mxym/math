import APPTReview.IntegerPlateau
import APPTReview.OuterEndpoint

namespace APPTReview

noncomputable def outerSpikePurity (m n : ℕ) : ℝ :=
  ((m:ℝ)*n+(m:ℝ)*((m:ℝ)+2))/((m:ℝ)*n+m)^2

noncomputable def roundedPlateauPurity (m n : ℕ) : ℝ :=
  plateauScaledPurity m n (((m-1)*n+1)/2)/((m:ℝ)*n)

/-- The early-prefix full-support endpoint is largest at prefix length one. -/
theorem cutEdge_early_full_bound (L i m : ℝ) (hL : 0 < L) (hi : 1 ≤ i) (hm : 0 ≤ m) :
    cutEdgePurity L i i m ≤ (L+3*m+m^2)/(L+2*m)^2 := by
  have hiP : 0 < i := by linarith
  have ht : 0 < L+2*m := by linarith
  have hd : i*L+(i+i)*m=i*(L+2*m) := by ring
  have hnum : (i^2*(L+m)+2*i*i*m+i*m^2)/i^2 ≤ L+3*m+m^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hiP)).2
    have hp := mul_nonneg (mul_nonneg hiP.le (show 0 ≤ i-1 by linarith)) (sq_nonneg m)
    nlinarith
  unfold cutEdgePurity
  rw [hd,mul_pow,← div_div]
  exact div_le_div_of_nonneg_right hnum (sq_nonneg _)

/-- The late-prefix family lies below the uniform-prefix endpoint. -/
theorem cutEdge_late_bound (L i s : ℝ) (hL : 0 < L) (hi : 0 ≤ i)
    (hiL : i < L) (hs : 0 ≤ s) : cutEdgePurity L (L-i) i s ≤ 1/L := by
  have hh : 0 < L-i := by linarith
  have hd : 0 < (L-i)*L+((L-i)+i)*s := by positivity
  rw [cutEdgePurity_quadratic L (L-i) i s (ne_of_gt hL) (ne_of_gt hd)]
  have he : L-(L-i)-i=0 := by ring
  rw [he]
  simp only [mul_zero,zero_div,zero_mul,add_zero]
  exact sub_le_self _ (mul_nonneg (div_nonneg hh.le hL.le) (div_nonneg hs hd.le))

/-- Full-support middle vertices have precisely the projection-plateau objective. -/
theorem cutEdge_middle_identity (D m i : ℝ) (hm : m≠0) (hZ : D*(m-1)+2*i≠0) :
    cutEdgePurity (D-m) (m*(m-1)/2) i m=
      (D*(m-1)^2+4*m*i)/(D*(m-1)+2*i)^2 := by
  have hd : (m*(m-1)/2)*(D-m)+(m*(m-1)/2+i)*m=
      (m/2)*(D*(m-1)+2*i) := by ring
  have hn : (m*(m-1)/2)^2*((D-m)+m)+2*i*(m*(m-1)/2)*m+i*m^2=
      (m^2/4)*(D*(m-1)^2+4*m*i) := by ring
  unfold cutEdgePurity
  rw [hd,hn,mul_pow]
  generalize he : D*(m-1)+2*i=z at *
  field_simp
  ring

theorem cutEdge_middle_le_rounded {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (k : ℕ) :
    cutEdgePurity ((m:ℝ)*n-m) ((m:ℝ)*((m:ℝ)-1)/2) (k:ℝ) m ≤ roundedPlateauPurity m n := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hnP : (0:ℝ) < n := by exact_mod_cast hn
  have hmP : (0:ℝ) < m := by linarith
  have hD : (0:ℝ) < (m:ℝ)*n := mul_pos hmP hnP
  have hZ : (m:ℝ)*n*((m:ℝ)-1)+2*(k:ℝ)≠0 := by
    have hs : (0:ℝ) < (m:ℝ)-1 := by linarith
    positivity
  rw [cutEdge_middle_identity _ _ _ (ne_of_gt hmP) hZ]
  have he : ((m:ℝ)*n*((m:ℝ)-1)^2+4*m*k)/((m:ℝ)*n*((m:ℝ)-1)+2*k)^2=
      plateauScaledPurity m n k/((m:ℝ)*n) := by
    unfold plateauScaledPurity plateauDenominator
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right (plateauScaledPurity_ceiling_unique hm hn k).1 hD.le

/-- The surviving uniform-prefix vertices are bounded by the spike branch. -/
theorem outerSpike_dominates_uniform {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    1/((m:ℝ)*n-m) ≤ outerSpikePurity m n := by
  let D : ℝ := (m:ℝ)*n
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  have hmP : (0:ℝ) < m := by linarith
  have hD : (m:ℝ)^2 ≤ D := by dsimp [D]; nlinarith
  have hL : 0 < D-m := by nlinarith
  have hplus : 0 < D+m := by nlinarith
  have h1 := mul_nonneg (show (0:ℝ) ≤ (m:ℝ)-1 by linarith) (sub_nonneg.mpr hD)
  have h2 : 0 ≤ (m:ℝ)*((m:ℝ)-3)*((m:ℝ)+1) := by positivity
  have hp : 0 ≤ ((m:ℝ)-1)*D-(m:ℝ)*((m:ℝ)+3) := by nlinarith
  have hmul := mul_nonneg hmP.le hp
  change 1/(D-m) ≤ (D+(m:ℝ)*((m:ℝ)+2))/(D+m)^2
  apply (div_le_div_iff₀ hL (sq_pos_of_pos hplus)).2
  nlinarith

end APPTReview
