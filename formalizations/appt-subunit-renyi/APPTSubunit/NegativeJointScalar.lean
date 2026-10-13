import APPTReview.SchmidtJointScalar

open scoped BigOperators
namespace APPTSubunit
open APPTReview
variable {a : Type*} [Fintype a] [LinearOrder a]

def negativeBackground (m h : ℝ) : ℝ := (h+1)*m
def negativeSpikeSize (m h : ℝ) : ℝ := negativeBackground m h-h^2

/-- A finite SOS controls a downward spike and a positive contraction jointly.
The selected Schmidt coordinate is arbitrary and the vector need not be unit. -/
theorem negative_joint_coordinate (s : a → ℝ) (h : ℝ) (hh : 0≤h) (i : a) :
    0≤negativeBackground (Fintype.card a) h*(∑ k,(s k)^2)
      -2*h*schmidtMass s-negativeSpikeSize (Fintype.card a) h*(s i)^2 := by
  classical
  let τ := {k : a // k≠i}
  let Q : ℝ := ∑ k : τ,(s k)^2
  let T : ℝ := ∑ k : τ,s k
  let m : ℝ := Fintype.card a
  have hQ : 0≤Q := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hcard : (Fintype.card τ:ℝ)+1=m := by
    have he : Fintype.card τ+1=Fintype.card a := by
      have he : Fintype.card τ=Fintype.card a-1 := by simp [τ]
      have hn : 0<Fintype.card a := Fintype.card_pos_iff.mpr ⟨i⟩
      omega
    dsimp only [m]
    exact_mod_cast he
  have htail : T^2≤(m-1)*Q := by
    have hc := tail_cauchy (fun k : τ => s k)
    rw [show (Fintype.card τ:ℝ)=m-1 by linarith] at hc
    exact hc
  have hsum (f : a → ℝ) : (∑ k,f k)=f i+∑ k : τ,f k := by
    have he := Finset.sum_erase_add (Finset.univ : Finset a) f (Finset.mem_univ i)
    have ht : (∑ k∈(Finset.univ : Finset a).erase i,f k)=∑ k : τ,f k :=
      Finset.sum_subtype _ (by intro k; simp) f
    linarith
  have hmass := schmidtMass_identity s
  have he : negativeBackground m h*(∑ k,(s k)^2)-2*h*schmidtMass s
      -negativeSpikeSize m h*(s i)^2 =
      (h*s i-T)^2+(h+1)*((m-1)*Q-T^2)+(2*h+1)*Q := by
    rw [show 2*h*schmidtMass s=h*(2*schmidtMass s) by ring,hmass,hsum s,
      hsum (fun k => (s k)^2)]
    dsimp only [negativeBackground,negativeSpikeSize,Q,T]
    ring
  change 0≤negativeBackground m h*(∑ k,(s k)^2)-2*h*schmidtMass s
      -negativeSpikeSize m h*(s i)^2
  rw [he]
  exact add_nonneg (add_nonneg (sq_nonneg _)
    (mul_nonneg (by linarith) (sub_nonneg.mpr htail))) (by positivity)

theorem negative_joint_background (s : a → ℝ) (h : ℝ) (hh : 0≤h) :
    0≤negativeBackground (Fintype.card a) h*(∑ k,(s k)^2)-2*h*schmidtMass s := by
  have hc := tail_cauchy s
  have hm := schmidtMass_identity s
  have hQ : 0≤∑ k,(s k)^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h1 := mul_nonneg hh (sub_nonneg.mpr hc)
  have h2 : 0≤((Fintype.card a:ℝ)+h)*(∑ k,(s k)^2) := by positivity
  unfold negativeBackground
  nlinarith

/-- The upper, rather than lower, signed-Schmidt floor is the physical input
for subtracting a pure state. Both positive off-diagonal entries and diagonals
are treated, and negative entries have the favorable sign. -/
theorem negative_joint_signed (s : a → ℝ) (h : ℝ) (hh : 0≤h)
    (hd : 0≤negativeSpikeSize (Fintype.card a) h) (hs : ∀ i,0≤s i) (p : a × a) :
    0≤negativeBackground (Fintype.card a) h*(∑ k,(s k)^2)-2*h*schmidtMass s
      -negativeSpikeSize (Fintype.card a) h*schmidtSigned s p := by
  have hbg := negative_joint_background s h hh
  have hi := negative_joint_coordinate s h hh p.1
  have hj := negative_joint_coordinate s h hh p.2
  unfold schmidtSigned
  split_ifs with he hl
  · exact hi
  · have hsq := mul_nonneg hd (sq_nonneg (s p.1-s p.2))
    nlinarith
  · have hp := mul_nonneg hd (mul_nonneg (hs p.1) (hs p.2))
    nlinarith

end APPTSubunit
