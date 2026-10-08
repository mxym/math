import FiniteMarginals

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I K J : Type*} [Fintype I] [Fintype K] [DecidableEq K]

def fiber (f : I → K) (k : K) : Finset I := Finset.univ.filter (fun i => f i = k)

def fiberSize (f : I → K) (k : K) : ℝ := (fiber f k).card

def pushLaw (f : I → K) (v : I → ℝ) (k : K) : ℝ := ∑ i ∈ fiber f k, v i

def liftLaw (f : I → K) (p : K → ℝ) (i : I) : ℝ := p (f i) / fiberSize f (f i)

theorem fiberSize_pos (f : I → K) (hf : Function.Surjective f) (k : K) :
    0 < fiberSize f k := by
  obtain ⟨i, hi⟩ := hf k
  have hh : (fiber f k).Nonempty := ⟨i, by simp [fiber, hi]⟩
  dsimp [fiberSize]
  exact_mod_cast Finset.card_pos.mpr hh

theorem sum_pushLaw (f : I → K) (v : I → ℝ) :
    (∑ k, pushLaw f v k) = ∑ i, v i :=
  Finset.sum_fiberwise Finset.univ f v

theorem pushLaw_liftLaw (f : I → K) (hf : Function.Surjective f) (p : K → ℝ) :
    pushLaw f (liftLaw f p) = p := by
  funext k
  dsimp [pushLaw]
  calc
    (∑ i ∈ fiber f k, liftLaw f p i) = ∑ _i ∈ fiber f k, p k / fiberSize f k := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [liftLaw, (Finset.mem_filter.mp hi).2]
    _ = p k := by
      rw [Finset.sum_const, nsmul_eq_mul]
      change fiberSize f k * (p k / fiberSize f k) = p k
      field_simp [(fiberSize_pos f hf k).ne']

theorem sum_liftLaw (f : I → K) (hf : Function.Surjective f) (p : K → ℝ) :
    (∑ i, liftLaw f p i) = ∑ k, p k := by
  rw [← sum_pushLaw f, pushLaw_liftLaw f hf]

theorem pushLaw_probability (f : I → K) (v : I → ℝ) (hv : Probability v) :
    Probability (pushLaw f v) :=
  ⟨fun k => Finset.sum_nonneg (fun i _ => hv.1 i), (sum_pushLaw f v).trans hv.2⟩

theorem liftLaw_probability (f : I → K) (hf : Function.Surjective f)
    (p : K → ℝ) (hp : Probability p) : Probability (liftLaw f p) :=
  ⟨fun i => div_nonneg (hp.1 _) (fiberSize_pos f hf _).le,
    (sum_liftLaw f hf p).trans hp.2⟩

theorem liftLaw_pushLaw (f : I → K) (v : I → ℝ)
    (hconstant : ∀ i j, f i = f j → v i = v j) : liftLaw f (pushLaw f v) = v := by
  funext i
  have hs : pushLaw f v (f i) = fiberSize f (f i) * v i := by
    dsimp [pushLaw, fiberSize]
    calc
      (∑ j ∈ fiber f (f i), v j) = ∑ _j ∈ fiber f (f i), v i := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hconstant j i (Finset.mem_filter.mp hj).2
      _ = _ := by simp
  have hh : (fiber f (f i)).Nonempty := ⟨i, by simp [fiber]⟩
  have hn : fiberSize f (f i) ≠ 0 := by
    dsimp [fiberSize]
    exact_mod_cast (Finset.card_pos.mpr hh).ne'
  simp [liftLaw, hs, hn]

theorem fiber_moment (f : I → K) (M : K → ℝ) (v : I → ℝ) :
    (∑ i, M (f i) * v i) = ∑ k, M k * pushLaw f v k := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun i => M (f i) * v i)]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [pushLaw]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

theorem lift_match (f : I → K) (hf : Function.Surjective f) (M : J → K → ℝ)
    (p q : K → ℝ) :
    Match (fun j i => M j (f i)) (liftLaw f p) (liftLaw f q) ↔ Match M p q := by
  have he (v : K → ℝ) (j : J) :
      (∑ i, M j (f i) * liftLaw f v i) = ∑ k, M j k * v k := by
    rw [fiber_moment f (M j), pushLaw_liftLaw f hf]
  constructor <;> intro h j
  · rw [← he p j, ← he q j]
    exact h j
  · rw [he p j, he q j]
    exact h j

end
end OrbitalMarginals
