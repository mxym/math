import APPTReview.SchmidtJointWitness

open scoped BigOperators
namespace APPTReview
variable {a : Type*} [Fintype a] [LinearOrder a]

/-- Integer-parameter background permitting a spike and a broad plateau jointly. -/
def effectiveBackground (m h : ℝ) : ℝ := (h+1)*m+2*h^2+h

/-- A finite Young/Cauchy certificate; no large-dimension or compactness premise. -/
theorem effective_joint_pair (s : a → ℝ) (h : ℝ) (hh : 0≤h)
    (i j : a) (hij : i≠j) :
    0≤effectiveBackground (Fintype.card a) h*(∑ k,(s k)^2)
      -2*h*schmidtMass s-2*(Fintype.card a:ℝ)*h*s i*s j := by
  classical
  let τ := {k : a // k≠i ∧ k≠j}
  let Q : ℝ := ∑ k : τ,(s k)^2
  let T : ℝ := ∑ k : τ,s k
  let m : ℝ := Fintype.card a
  have hQ : 0≤Q := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hm : 0≤m := Nat.cast_nonneg _
  have hcardN : Fintype.card τ≤Fintype.card a :=
    Fintype.card_le_of_injective (fun k : τ => (k:a)) Subtype.val_injective
  have hcard : (Fintype.card τ:ℝ)≤m := by change (Fintype.card τ:ℝ)≤(Fintype.card a:ℝ); exact_mod_cast hcardN
  have htail : T^2≤m*Q :=
    (tail_cauchy (fun k : τ => s k)).trans (mul_le_mul_of_nonneg_right hcard hQ)
  have hsum := sum_remove_two s i j hij
  have hsq := sum_remove_two (fun k => (s k)^2) i j hij
  have hmass := schmidtMass_identity s
  have he : effectiveBackground m h*(∑ k,(s k)^2)-2*h*schmidtMass s-2*m*h*s i*s j=
      (h*(s i+s j)-T)^2+(h+1)*(m*Q-T^2)+m*((s i)^2+(s j)^2)
        +h*(m+h+1)*(s i-s j)^2+2*h*(h+1)*Q := by
    rw [show 2*h*schmidtMass s=h*(2*schmidtMass s) by ring,hmass,hsum,hsq]
    dsimp only [effectiveBackground,Q,T,τ]
    ring
  change 0≤effectiveBackground m h*(∑ k,(s k)^2)-2*h*schmidtMass s-2*m*h*s i*s j
  rw [he]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (sq_nonneg _)
    (mul_nonneg (by linarith) (sub_nonneg.mpr htail)))
    (mul_nonneg hm (add_nonneg (sq_nonneg _) (sq_nonneg _))))
    (mul_nonneg (by positivity) (sq_nonneg _))) (by positivity)

theorem effective_joint_background (s : a → ℝ) (h : ℝ) (hh : 0≤h) :
    0≤effectiveBackground (Fintype.card a) h*(∑ k,(s k)^2)-2*h*schmidtMass s := by
  have hc := tail_cauchy s
  have hm := schmidtMass_identity s
  have hQ : 0≤∑ k,(s k)^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hM : 0≤(Fintype.card a:ℝ) := Nat.cast_nonneg _
  have h1 := mul_nonneg hh (sub_nonneg.mpr hc)
  have h2 : 0≤((Fintype.card a:ℝ)+2*h^2+2*h)*(∑ k,(s k)^2) := by positivity
  unfold effectiveBackground
  nlinarith

theorem effective_joint_signed (s : a → ℝ) (h : ℝ) (hh : 0≤h)
    (hs : ∀ i,0≤s i) (p : a × a) :
    0≤(effectiveBackground (Fintype.card a) h*(∑ k,(s k)^2)-2*h*schmidtMass s)
      +2*(Fintype.card a:ℝ)*h*schmidtSigned s p := by
  have hbg := effective_joint_background s h hh
  unfold schmidtSigned
  split_ifs with he hl
  · exact add_nonneg hbg (mul_nonneg (by positivity) (sq_nonneg _))
  · exact add_nonneg hbg (mul_nonneg (by positivity) (mul_nonneg (hs _) (hs _)))
  · have hp := effective_joint_pair s h hh p.1 p.2 he
    nlinarith

end APPTReview
