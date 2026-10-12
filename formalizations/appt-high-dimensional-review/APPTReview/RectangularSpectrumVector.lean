import APPTReview.RectangularEqualityScalar

open scoped BigOperators
namespace APPTReview

/-- The claimed maximizing spectrum, with its actual integer multiplicities. -/
noncomputable def roundedPlateauSpectrum {D : ℕ} (m n : ℕ) : Fin D → ℝ :=
  fun x => if x.val < ((m-1)*n+1)/2 then
    ((m:ℝ)+1)/plateauDenominator m n (((m-1)*n+1)/2)
  else ((m:ℝ)-1)/plateauDenominator m n (((m-1)*n+1)/2)

theorem rounded_plateau_rank_bounds {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    0 < ((m-1)*n+1)/2 ∧ ((m-1)*n+1)/2 < m*n := by
  have hp : n ≤ (m-1)*n := by simpa using Nat.mul_le_mul_right n (show 1 ≤ m-1 by omega)
  have he : (m-1)*n+n=m*n := by
    have hs : m-1+1=m := by omega
    nlinarith
  constructor <;> omega

/-- Coordinates of a full-support crossing with a middle prefix. -/
theorem plateauCrossing_entry (m D i a : ℝ) (hm : 1 < m) (hD : 0 < D) (hi : 0 < i) :
    ((m/D)*(a/i)+(m*(m-1)/2/i)*(1/D))/(m*(m-1)/2/i+m/D)=
      (2*a+m-1)/(D*(m-1)+2*i) := by
  have hmP : 0 < m := by linarith
  have hZ : 0 < D*(m-1)+2*i := by positivity
  have hd : m*(m-1)/2/i+m/D=m*(D*(m-1)+2*i)/(2*i*D) := by
    field_simp <;> ring
  rw [hd]
  generalize hz : D*(m-1)+2*i=z at *
  field_simp
  ring

theorem uniformPrefix_last {D : ℕ} (l : Fin D) (hl : l.val+1=D) (x : Fin D) :
    uniformPrefix l x=1/(D:ℝ) := by
  have hx : x ≤ l := by change x.val ≤ l.val; have ht:=x.isLt; omega
  simp only [uniformPrefix,if_pos hx,hl]

/-- The unique full-support crossing is the actual two-valued spectrum. -/
theorem full_middle_crossing_spectrum {D m n : ℕ} (hm : 2 ≤ m) (hD : D=m*n)
    (k l : Fin D) (hk : k.val+1=((m-1)*n+1)/2) (hl : l.val+1=D) :
    cutPair (((m:ℝ)*((m:ℝ)-1)/2)/((k.val+1:ℕ):ℝ)) ((m:ℝ)/(D:ℝ))
      (uniformPrefix k) (uniformPrefix l)=roundedPlateauSpectrum (D:=D) m n := by
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hDP : (0:ℝ) < D := by exact_mod_cast (Fin.pos k)
  have hIP : (0:ℝ) < ((k.val+1:ℕ):ℝ) := by positivity
  have hDR : (D:ℝ)=(m:ℝ)*n := by exact_mod_cast hD
  funext x
  have hxiff : x ≤ k ↔ x.val < ((m-1)*n+1)/2 := by
    change x.val ≤ k.val ↔ _
    omega
  unfold cutPair
  rw [uniformPrefix_last l hl x]
  by_cases hx : x ≤ k
  · simp only [uniformPrefix,if_pos hx,roundedPlateauSpectrum,if_pos (hxiff.mp hx)]
    have he := plateauCrossing_entry (m:ℝ) (D:ℝ) ((k.val+1:ℕ):ℝ) 1 (by linarith) hDP hIP
    convert he using 1 <;> (try simp only [mul_zero,zero_add]) <;>
      rw [hDR,hk] <;> simp only [plateauDenominator] <;> congr 1 <;> ring
  · simp only [uniformPrefix,if_neg hx,roundedPlateauSpectrum,if_neg (not_congr hxiff |>.mp hx)]
    have he := plateauCrossing_entry (m:ℝ) (D:ℝ) ((k.val+1:ℕ):ℝ) 0 (by linarith) hDP hIP
    simp only [zero_div,mul_zero,zero_add] at he
    convert he using 1 <;> (try simp only [mul_zero,zero_add]) <;>
      rw [hDR,hk] <;> simp only [plateauDenominator] <;> congr 1 <;> ring

end APPTReview
