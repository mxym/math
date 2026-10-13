import APPTReview.SparseMatrixBound

open scoped BigOperators
open Matrix
namespace APPTReview

/-- Removing a nonnegative part of the vector loses at most the displayed row mass.
There is no asymptotic or symmetry premise in this finite estimate. -/
theorem rayleigh_remove_bound {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (c : ℝ) (hc : 0≤c)
    (hA : ∀ i j,0≤A i j) (hAc : ∀ i j,A i j≤c)
    (s u v : ι → ℝ) (hu : ∀ i,0≤u i) (hv : ∀ i,0≤v i)
    (hsplit : ∀ i,s i=u i+v i) :
    realRayleigh A s ≤ realRayleigh A v+2*c*(∑ i,u i)*(∑ i,s i) := by
  have hs (i) : 0≤s i := by rw [hsplit]; exact add_nonneg (hu _) (hv _)
  have hp (z : ι × ι) : A z.1 z.2*(s z.1*s z.2) ≤
      A z.1 z.2*(v z.1*v z.2)+c*(u z.1*s z.2+s z.1*u z.2) := by
    have h1 := mul_le_mul_of_nonneg_right (hAc z.1 z.2)
      (add_nonneg (mul_nonneg (hu z.1) (hs z.2)) (mul_nonneg (hs z.1) (hu z.2)))
    have h2 := mul_nonneg (hA z.1 z.2) (mul_nonneg (hu z.1) (hu z.2))
    rw [hsplit z.1,hsplit z.2] at *
    nlinarith
  have hh := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) => hp z)
  change realRayleigh A s ≤ _ at hh
  have he : (∑ z : ι × ι, (A z.1 z.2*(v z.1*v z.2)+
      c*(u z.1*s z.2+s z.1*u z.2)))=
      realRayleigh A v+2*c*(∑ i,u i)*(∑ i,s i) := by
    simp only [Finset.sum_add_distrib,realRayleigh,Fintype.sum_prod_type,
      ← Finset.mul_sum,← Finset.sum_mul]
    ring
  rwa [he] at hh

/-- A single edge decouples from a matrix whose entries are uniformly small.
The exact error is 4*c*sqrt(card); the norm budget is not counted twice. -/
theorem rayleigh_single_spike_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (c C a : ℝ) (hc : 0≤c) (ha : 0≤a)
    (hA : ∀ i j,0≤A i j) (hAc : ∀ i j,A i j≤c)
    (hcap : ∀ x : ι → ℝ,realRayleigh A x≤C*∑ i,(x i)^2)
    (s : ι → ℝ) (hs : ∀ i,0≤s i) (hn : (∑ i,(s i)^2)=1)
    (i j : ι) (hij : i≠j) :
    realRayleigh A s+2*a*s i*s j ≤ max C a+4*c*Real.sqrt (Fintype.card ι) := by
  let u : ι → ℝ := fun k => if k=i then s i else if k=j then s j else 0
  let v : ι → ℝ := fun k => if k=i ∨ k=j then 0 else s k
  have hu (k) : 0≤u k := by dsimp [u]; split_ifs; exact hs i; exact hs j; exact le_rfl
  have hv (k) : 0≤v k := by dsimp [v]; split_ifs; exact le_rfl; exact hs k
  have hsplit (k) : s k=u k+v k := by
    by_cases hi : k=i <;> by_cases hj : k=j <;> simp_all only [u,v,ite_true,ite_false,or_true,true_or,or_false,false_or,add_zero,zero_add,zero_pow,ne_eq,not_false_eq_true]
  have huSplit (k) : u k=(if k=i then s i else 0)+(if k=j then s j else 0) := by
    by_cases hi : k=i
    · subst k; simp [u,hij]
    · simp [u,hi]
  have hsumu : (∑ k,u k)=s i+s j := by simp_rw [huSplit]; simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hsq (k) : (s k)^2=(u k)^2+(v k)^2 := by
    by_cases hi : k=i
    · subst k; simp [u,v,hij]
    · by_cases hj : k=j
      · subst k; simp [u,v,Ne.symm hij]
      · simp [u,v,hi,hj]
  have husq : (∑ k,(u k)^2)=(s i)^2+(s j)^2 := by
    have he (k) : (u k)^2=(if k=i then (s i)^2 else 0)+(if k=j then (s j)^2 else 0) := by
      by_cases hi : k=i
      · subst k; simp [u,hij]
      · by_cases hj : k=j
        · subst k; simp [u,Ne.symm hij]
        · simp [u,hi,hj]
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have htotal : (s i)^2+(s j)^2+(∑ k,(v k)^2)=1 := by
    have hh := Finset.sum_congr rfl (fun k (_ : k∈Finset.univ) => hsq k)
    rw [hn,Finset.sum_add_distrib,husq] at hh
    linarith
  have hsi := unit_amplitude_le_one s hs hn i
  have hsj := unit_amplitude_le_one s hs hn j
  have hsump : 0≤∑ k,s k := Finset.sum_nonneg (fun k _ => hs k)
  have hS : (∑ k,s k)≤Real.sqrt (Fintype.card ι) := by
    have hh := tail_cauchy s
    rw [hn,mul_one] at hh
    have hrt := Real.sq_sqrt (show (0:ℝ)≤Fintype.card ι by positivity)
    have hr := Real.sqrt_nonneg (Fintype.card ι:ℝ)
    nlinarith
  have herr : 2*c*(s i+s j)*(∑ k,s k)≤4*c*Real.sqrt (Fintype.card ι) := by
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show s i+s j≤2 by linarith) (show 0≤2*c by positivity)) hsump
    have h2 := mul_le_mul_of_nonneg_left hS (show 0≤4*c by positivity)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right (le_max_left C a)
    (Finset.sum_nonneg (fun k (_ : k∈Finset.univ) => sq_nonneg (v k)))
  have h2 := mul_le_mul_of_nonneg_right (le_max_right C a)
    (add_nonneg (sq_nonneg (s i)) (sq_nonneg (s j)))
  have h3 := mul_nonneg ha (sq_nonneg (s i-s j))
  have hbound := rayleigh_remove_bound A c hc hA hAc s u v hu hv hsplit
  rw [hsumu] at hbound
  have hh := hcap v
  have hbudget := congrArg (fun x : ℝ => max C a*x) htotal
  nlinarith only [h1,h2,h3,hbound,hh,herr,hbudget]

end APPTReview
