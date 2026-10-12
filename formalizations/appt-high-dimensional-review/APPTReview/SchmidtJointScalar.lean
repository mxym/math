import APPTReview.SchmidtMass

open scoped BigOperators
namespace APPTReview
variable {a : Type*} [Fintype a] [LinearOrder a]

/-- Remove any two distinct Schmidt coordinates, without a sorting assumption. -/
theorem sum_remove_two (f : a → ℝ) (i j : a) (hij : i≠j) :
    (∑ k, f k)=f i+f j+∑ k : {k : a // k≠i ∧ k≠j}, f k := by
  classical
  let t := (Finset.univ : Finset a).erase i |>.erase j
  have hji : j∈(Finset.univ : Finset a).erase i := by simp [hij,Ne.symm hij]
  have h1 := Finset.sum_erase_add (Finset.univ : Finset a) f (Finset.mem_univ i)
  have h2 := Finset.sum_erase_add ((Finset.univ : Finset a).erase i) f hji
  have ht : (∑ k∈t, f k)=∑ k : {k : a // k≠i ∧ k≠j}, f k := by
    exact Finset.sum_subtype t (by intro k; simp [t,and_comm]) f
  dsimp only [t] at ht
  linarith

/-- The Schmidt sum-of-squares bound holds for every distinct pair simultaneously. -/
theorem schmidt_joint_pair_nonneg (s : a → ℝ) (hc : 4≤Fintype.card a)
    (i j : a) (hij : i≠j) :
    0≤(2*(Fintype.card a:ℝ)-5)*(∑ k,(s k)^2)-2*schmidtMass s
      -4*((Fintype.card a:ℝ)-4)*s i*s j := by
  classical
  let t := (Finset.univ : Finset a).erase i |>.erase j
  have hji : j∈(Finset.univ : Finset a).erase i := by simp [hij,Ne.symm hij]
  have ht : Fintype.card {k : a // k≠i ∧ k≠j}+2=Fintype.card a := by
    have he : Fintype.card {k : a // k≠i ∧ k≠j}=t.card := by
      let e : {k : a // k≠i ∧ k≠j} ≃ ↥t :=
        { toFun := fun k => ⟨k.val, by simpa [t,and_comm] using k.property⟩
          invFun := fun k => ⟨k.val, ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp k.property).2).1, (Finset.mem_erase.mp k.property).1⟩⟩
          left_inv := by intro k; rfl
          right_inv := by intro k; rfl }
      simpa using Fintype.card_congr e
    rw [he]
    simp only [t,Finset.card_erase_of_mem hji,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ]
    omega
  have htR : (Fintype.card {k : a // k≠i ∧ k≠j}:ℝ)+2=(Fintype.card a:ℝ) := by exact_mod_cast ht
  have hb := multilevel_sos_nonneg (ι:={k : a // k≠i ∧ k≠j}) (by omega) (s i) (s j) (fun k => s k)
  have hsum := sum_remove_two s i j hij
  have hsq := sum_remove_two (fun k => (s k)^2) i j hij
  have hmass := schmidtMass_identity s
  rw [hmass,hsum,hsq,← htR]
  convert hb using 1 <;> ring

/-- The isotropic background is nonnegative, even for an unnormalized test vector. -/
theorem schmidt_joint_background (s : a → ℝ) (hc : 4≤Fintype.card a) :
    0≤(2*(Fintype.card a:ℝ)-5)*(∑ k,(s k)^2)-2*schmidtMass s := by
  have ht := tail_cauchy s
  have hmass := schmidtMass_identity s
  have hcR : (4:ℝ)≤Fintype.card a := by exact_mod_cast hc
  have hsq : 0≤∑ k,(s k)^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hprod := mul_nonneg (show (0:ℝ)≤Fintype.card a-4 by linarith) hsq
  nlinarith

/-- Every signed Schmidt diagonal entry satisfies the same joint floor. -/
theorem schmidt_joint_signed_nonneg (s : a → ℝ) (hc : 4≤Fintype.card a)
    (hs : ∀ i,0≤s i) (p : a × a) :
    0≤((2*(Fintype.card a:ℝ)-5)*(∑ k,(s k)^2)-2*schmidtMass s)
      +4*((Fintype.card a:ℝ)-4)*schmidtSigned s p := by
  have hbg := schmidt_joint_background s hc
  have hcR : (4:ℝ)≤Fintype.card a := by exact_mod_cast hc
  unfold schmidtSigned
  split_ifs with he hl
  · exact add_nonneg hbg (mul_nonneg (by linarith) (sq_nonneg _))
  · exact add_nonneg hbg (mul_nonneg (by linarith) (mul_nonneg (hs _) (hs _)))
  · have hh := schmidt_joint_pair_nonneg s hc p.1 p.2 he
    nlinarith

end APPTReview
