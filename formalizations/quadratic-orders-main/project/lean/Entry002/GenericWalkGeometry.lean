import Entry002.GenericSignedArithmetic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Tactic

/-! Arbitrary full-lattice walk difference geometry, with the actual planar metric.
The finite rectangle Sperner proof and complex path covering proof below are
adapted verbatim from the pinned OpenAI upstream-028 WalkGeometry.lean,
lines 7--368. Only their namespace and imports change. -/

namespace Entry002
namespace WalkGeometry

section
open scoped BigOperators

def colorEdge (a b : Fin 3) : ℤ :=
  if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0

def Tricolored (a b c : Fin 3) : Prop := a ≠ b ∧ b ≠ c ∧ a ≠ c

theorem colorEdge_add {a b c : Fin 3} (h : ¬ Tricolored a b c) :
    colorEdge a b + colorEdge b c = colorEdge a c := by
  unfold Tricolored at h
  revert a b c
  decide

theorem colorEdge_zero_left (a b : Fin 3) (ha : a ≠ 0) (hb : b ≠ 0) :
    colorEdge a b = 0 := by simp [colorEdge,ha,hb]

theorem colorEdge_zero_one (a b : Fin 3) (ha : a ≠ 1) (hb : b ≠ 1) :
    colorEdge a b = 0 := by simp [colorEdge,ha,hb]

theorem colorEdge_binary (a b : Fin 3) (ha : a ≠ 2) (hb : b ≠ 2) :
    colorEdge a b = (b.val : ℤ) - a.val := by
  revert a b
  decide

theorem discrete_rectangle_sperner (c : ℕ → ℕ → Fin 3) (m n : ℕ)
    (hbottom : ∀ i ≤ m, c i 0 = 0)
    (htop : ∀ i ≤ m, c i n ≠ 0)
    (hleft : ∀ j ≤ n, c 0 j ≠ 2)
    (hright : ∀ j ≤ n, c m j ≠ 1) :
    ∃ i < m, ∃ j < n,
      Tricolored (c i j) (c (i+1) j) (c (i+1) (j+1)) ∨
      Tricolored (c i j) (c i (j+1)) (c (i+1) (j+1)) := by
  by_contra h
  have hcell (i j : ℕ) (hi : i < m) (hj : j < n) :
      colorEdge (c i j) (c (i+1) j) - colorEdge (c i (j+1)) (c (i+1) (j+1)) =
      colorEdge (c i j) (c i (j+1)) - colorEdge (c (i+1) j) (c (i+1) (j+1)) := by
    have h1 : ¬ Tricolored (c i j) (c (i+1) j) (c (i+1) (j+1)) :=
      fun hh => h ⟨i,hi,j,hj,Or.inl hh⟩
    have h2 : ¬ Tricolored (c i j) (c i (j+1)) (c (i+1) (j+1)) :=
      fun hh => h ⟨i,hi,j,hj,Or.inr hh⟩
    have he1 := colorEdge_add h1
    have he2 := colorEdge_add h2
    omega
  have hsum := Finset.sum_congr (s₁ := Finset.range n) rfl (fun j hj =>
    Finset.sum_congr (s₁ := Finset.range m) rfl (fun i hi =>
      hcell i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)))
  have hl : (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m,
      (colorEdge (c i j) (c (i+1) j) - colorEdge (c i (j+1)) (c (i+1) (j+1)))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.sum_range_sub']
    rw [hbottom i (Nat.le_of_lt (Finset.mem_range.mp hi)),
      hbottom (i+1) (Finset.mem_range.mp hi)]
    rw [colorEdge_zero_left _ _ (htop i (Nat.le_of_lt (Finset.mem_range.mp hi)))
      (htop (i+1) (Finset.mem_range.mp hi))]
    rfl
  have hr : (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m,
      (colorEdge (c i j) (c i (j+1)) - colorEdge (c (i+1) j) (c (i+1) (j+1)))) = 1 := by
    have he (j : ℕ) (hj : j ∈ Finset.range n) :
        (∑ i ∈ Finset.range m, (colorEdge (c i j) (c i (j+1)) -
          colorEdge (c (i+1) j) (c (i+1) (j+1)))) = ((c 0 (j+1)).val : ℤ) - (c 0 j).val := by
      rw [Finset.sum_range_sub']
      rw [colorEdge_zero_one _ _ (hright j (Nat.le_of_lt (Finset.mem_range.mp hj)))
        (hright (j+1) (Finset.mem_range.mp hj)),sub_zero,
        colorEdge_binary _ _ (hleft j (Nat.le_of_lt (Finset.mem_range.mp hj)))
          (hleft (j+1) (Finset.mem_range.mp hj))]
    rw [Finset.sum_congr rfl he,Finset.sum_range_sub (fun j => ((c 0 j).val : ℤ))]
    have hend : c 0 n = 1 := by
      have h0 := htop 0 (Nat.zero_le m)
      have h2 := hleft n le_rfl
      have hone : ∀ x : Fin 3, x ≠ 0 → x ≠ 2 → x = 1 := by decide
      exact hone _ h0 h2
    rw [hend,hbottom 0 (Nat.zero_le m)]
    norm_num
  rw [hl,hr] at hsum
  omega

noncomputable def pointColor (z : ℂ) : Fin 3 := if z.im < 0 then 0 else if z.re < 0 then 1 else 2

theorem pointColor_zero {z : ℂ} (h : pointColor z = 0) : z.im < 0 := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact hi
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 0) h)
  · exact False.elim ((by decide : (2 : Fin 3) ≠ 0) h)

theorem pointColor_one {z : ℂ} (h : pointColor z = 1) : z.re < 0 ∧ 0 ≤ z.im := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 1) h)
  · exact ⟨hr,le_of_not_gt hi⟩
  · exact False.elim ((by decide : (2 : Fin 3) ≠ 1) h)

theorem pointColor_two {z : ℂ} (h : pointColor z = 2) : 0 ≤ z.re ∧ 0 ≤ z.im := by
  unfold pointColor at h
  split_ifs at h with hi hr
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 2) h)
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 2) h)
  · exact ⟨le_of_not_gt hr,le_of_not_gt hi⟩

theorem tricolored_covers {a b c : Fin 3} (h : Tricolored a b c) (q : Fin 3) :
    q = a ∨ q = b ∨ q = c := by
  unfold Tricolored at h
  revert a b c q
  decide

theorem tricolored_norm_bound {x y z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hxy : dist x y ≤ r) (hxz : dist x z ≤ r)
    (hc : Tricolored (pointColor x) (pointColor y) (pointColor z)) : ‖x‖ ≤ 2*r := by
  have he (q : Fin 3) : ∃ w : ℂ, pointColor w = q ∧ dist x w ≤ r := by
    rcases tricolored_covers hc q with h | h | h
    · exact ⟨x,h.symm,by simpa using hr⟩
    · exact ⟨y,h.symm,hxy⟩
    · exact ⟨z,h.symm,hxz⟩
  obtain ⟨w0,h0,hd0⟩ := he 0
  obtain ⟨w1,h1,hd1⟩ := he 1
  obtain ⟨w2,h2,hd2⟩ := he 2
  have hc0 := pointColor_zero h0
  have hc1 := pointColor_one h1
  have hc2 := pointColor_two h2
  have hRe (w : ℂ) (hd : dist x w ≤ r) : -r ≤ x.re-w.re ∧ x.re-w.re ≤ r := by
    apply abs_le.mp
    have hh : |x.re-w.re| ≤ dist x w := by simpa only [Complex.sub_re,dist_eq_norm] using Complex.abs_re_le_norm (x-w)
    exact hh.trans hd
  have hIm (w : ℂ) (hd : dist x w ≤ r) : -r ≤ x.im-w.im ∧ x.im-w.im ≤ r := by
    apply abs_le.mp
    have hh : |x.im-w.im| ≤ dist x w := by simpa only [Complex.sub_im,dist_eq_norm] using Complex.abs_im_le_norm (x-w)
    exact hh.trans hd
  have hR1 := hRe w1 hd1
  have hR2 := hRe w2 hd2
  have hI0 := hIm w0 hd0
  have hI1 := hIm w1 hd1
  have hrx : |x.re| ≤ r := abs_le.mpr ⟨by linarith,by linarith⟩
  have hix : |x.im| ≤ r := abs_le.mpr ⟨by linarith,by linarith⟩
  have h := Complex.norm_le_abs_re_add_abs_im x
  linarith

theorem discrete_rectangle_approx_zero (f : ℕ → ℕ → ℂ) (m n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hhor : ∀ i < m, ∀ j ≤ n, dist (f i j) (f (i+1) j) ≤ D)
    (hver : ∀ i ≤ m, ∀ j < n, dist (f i j) (f i (j+1)) ≤ D)
    (hbottom : ∀ i ≤ m, (f i 0).im < 0)
    (htop : ∀ i ≤ m, 0 ≤ (f i n).im)
    (hleft : ∀ j ≤ n, (f 0 j).re < 0)
    (hright : ∀ j ≤ n, 0 ≤ (f m j).re) :
    ∃ i ≤ m, ∃ j ≤ n, ‖f i j‖ ≤ 4*D := by
  have hb : ∀ i ≤ m, pointColor (f i 0) = 0 := by
    intro i hi
    simp [pointColor,hbottom i hi]
  have ht : ∀ i ≤ m, pointColor (f i n) ≠ 0 := by
    intro i hi hh
    exact (not_lt_of_ge (htop i hi)) (pointColor_zero hh)
  have hl : ∀ j ≤ n, pointColor (f 0 j) ≠ 2 := by
    intro j hj hh
    exact (not_le_of_gt (hleft j hj)) (pointColor_two hh).1
  have hr : ∀ j ≤ n, pointColor (f m j) ≠ 1 := by
    intro j hj hh
    exact (not_lt_of_ge (hright j hj)) (pointColor_one hh).1
  obtain ⟨i,hi,j,hj,hc⟩ := discrete_rectangle_sperner (fun i j => pointColor (f i j)) m n hb ht hl hr
  refine ⟨i,hi.le,j,hj.le,?_⟩
  have hdiag : dist (f i j) (f (i+1) (j+1)) ≤ 2*D := by
    have h := dist_triangle (f i j) (f (i+1) j) (f (i+1) (j+1))
    have h1 := hhor i hi j hj.le
    have h2 := hver (i+1) hi j hj
    linarith
  rcases hc with hc | hc
  · have hh := tricolored_norm_bound (show 0 ≤ 2*D by positivity)
      ((hhor i hi j hj.le).trans (by linarith : D ≤ 2*D)) hdiag hc
    linarith
  · have hh := tricolored_norm_bound (show 0 ≤ 2*D by positivity)
      ((hver i hi.le j hj).trans (by linarith : D ≤ 2*D)) hdiag hc
    linarith

noncomputable def repeatPath (v : ℕ → ℂ) (n : ℕ) (a : ℂ) (t : ℕ) : ℂ :=
  v (t % n) + ((t / n : ℕ) : ℂ) * a

@[simp] theorem repeatPath_zero (v : ℕ → ℂ) (n : ℕ) (a : ℂ) :
    repeatPath v n a 0 = v 0 := by simp [repeatPath]

@[simp] theorem repeatPath_multiple (v : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (a : ℂ) (k : ℕ) :
    repeatPath v n a (k*n) = v 0 + (k : ℂ)*a := by simp [repeatPath,hn.ne']

theorem repeatPath_step (v : ℕ → ℂ) {n : ℕ} (hn : 0 < n) (a : ℂ)
    (hv0 : v 0 = 0) (hvn : v n = a) {D : ℝ}
    (hstep : ∀ i < n, dist (v i) (v (i+1)) ≤ D) (t : ℕ) :
    dist (repeatPath v n a t) (repeatPath v n a (t+1)) ≤ D := by
  have hr := Nat.mod_lt t hn
  have hdiv := Nat.mod_add_div t n
  by_cases hh : t % n + 1 = n
  · have ht : t+1 = (t/n+1)*n := by nlinarith
    rw [ht,repeatPath_multiple v hn]
    have he : repeatPath v n a t = v (t%n) + ((t/n:ℕ):ℂ)*a := rfl
    rw [he,hv0,zero_add,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (((t/n:ℕ):ℂ)*a) a]
    rw [dist_add_right]
    simpa [hh,hvn] using hstep (t%n) hr
  · have hr' : t%n+1 < n := by omega
    have ht : t+1 = t%n+1+(t/n)*n := by nlinarith
    have hmod : (t+1)%n = t%n+1 := by rw [ht,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr']
    have hquo : (t+1)/n = t/n := by rw [ht,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt hr',zero_add]
    simp only [repeatPath,hmod,hquo,dist_add_right]
    exact hstep (t%n) hr

theorem discrete_rectangle_approx_zero_rev (f : ℕ → ℕ → ℂ) (m n : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hhor : ∀ i < m, ∀ j ≤ n, dist (f i j) (f (i+1) j) ≤ D)
    (hver : ∀ i ≤ m, ∀ j < n, dist (f i j) (f i (j+1)) ≤ D)
    (hbottom : ∀ i ≤ m, 0 < (f i 0).im)
    (htop : ∀ i ≤ m, (f i n).im ≤ 0)
    (hleft : ∀ j ≤ n, (f 0 j).re < 0)
    (hright : ∀ j ≤ n, 0 ≤ (f m j).re) :
    ∃ i ≤ m, ∃ j ≤ n, ‖f i j‖ ≤ 4*D := by
  have hh : ∀ i < m, ∀ j ≤ n, dist (star (f i j)) (star (f (i+1) j)) ≤ D := by
    intro i hi j hj
    simpa only [dist_star_star] using hhor i hi j hj
  have hv : ∀ i ≤ m, ∀ j < n, dist (star (f i j)) (star (f i (j+1))) ≤ D := by
    intro i hi j hj
    simpa only [dist_star_star] using hver i hi j hj
  have hb : ∀ i ≤ m, (star (f i 0)).im < 0 := by
    intro i hi
    simpa only [Complex.star_def,Complex.conj_im,neg_lt_zero] using hbottom i hi
  have ht : ∀ i ≤ m, 0 ≤ (star (f i n)).im := by
    intro i hi
    simpa only [Complex.star_def,Complex.conj_im,neg_nonneg] using htop i hi
  obtain ⟨i,hi,j,hj,hz⟩ := discrete_rectangle_approx_zero (fun i j => star (f i j)) m n
    hD hh hv hb ht (by simpa only [Complex.star_def,Complex.conj_re] using hleft)
      (by simpa only [Complex.star_def,Complex.conj_re] using hright)
  exact ⟨i,hi,j,hj,by simpa only [norm_star] using hz⟩

theorem path_difference_cover (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : 0 < a.re) (hai : a.im = 0) (hb : 0 < b.im) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  let H : ℝ := (∑ i ∈ Finset.range n, ‖v i‖) + (∑ j ∈ Finset.range m, ‖u j‖) + ‖w‖
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hvb (i : ℕ) : ‖v (i%n)‖ ≤ ∑ k ∈ Finset.range n, ‖v k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (v k)) (Finset.mem_range.mpr (Nat.mod_lt i hn))
  have hub (j : ℕ) : ‖u (j%m)‖ ≤ ∑ k ∈ Finset.range m, ‖u k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (u k)) (Finset.mem_range.mpr (Nat.mod_lt j hm))
  have herr (i j : ℕ) : ‖v (i%n)-u (j%m)-w‖ ≤ H := by
    have h1 := norm_sub_le (v (i%n)) (u (j%m))
    have h2 := norm_sub_le (v (i%n)-u (j%m)) w
    dsimp [H]
    linarith [hvb i,hub j]
  have hrerr (i j : ℕ) : -H ≤ (v (i%n)-u (j%m)-w).re ∧
      (v (i%n)-u (j%m)-w).re ≤ H :=
    abs_le.mp ((Complex.abs_re_le_norm _).trans (herr i j))
  have hierr (i j : ℕ) : -H ≤ (v (i%n)-u (j%m)-w).im ∧
      (v (i%n)-u (j%m)-w).im ≤ H :=
    abs_le.mp ((Complex.abs_im_le_norm _).trans (herr i j))
  obtain ⟨N,hN⟩ := exists_nat_gt (H/b.im)
  have hN' : H < (N:ℝ)*b.im := (div_lt_iff₀ hb).mp hN
  obtain ⟨M,hM⟩ := exists_nat_gt ((H+(N:ℝ)*|b.re|)/a.re)
  have hM' : H+(N:ℝ)*|b.re| < (M:ℝ)*a.re := (div_lt_iff₀ ha).mp hM
  let f (i j : ℕ) : ℂ := repeatPath v n a i-repeatPath u m b j-(M:ℂ)*a+(N:ℂ)*b-w
  have hf (i j : ℕ) : f i j = v (i%n)-u (j%m)-w +
      (((i/n:ℕ):ℂ)-(M:ℂ))*a + ((N:ℂ)-((j/m:ℕ):ℂ))*b := by
    dsimp [f,repeatPath]
    ring
  have hfr (i j : ℕ) : (f i j).re = (v (i%n)-u (j%m)-w).re +
      (((i/n:ℕ):ℝ)-(M:ℝ))*a.re + ((N:ℝ)-((j/m:ℕ):ℝ))*b.re := by
    rw [hf]
    simp
  have hfi (i j : ℕ) : (f i j).im = (v (i%n)-u (j%m)-w).im +
      ((N:ℝ)-((j/m:ℕ):ℝ))*b.im := by
    rw [hf]
    simp [hai]
  have hhor (i : ℕ) (_ : i < 2*M*n) (j : ℕ) (_ : j ≤ 2*N*m) :
      dist (f i j) (f (i+1) j) ≤ D := by
    simpa only [f,dist_sub_right,dist_add_right] using repeatPath_step v hn a hv0 hvn hv i
  have hver (i : ℕ) (_ : i ≤ 2*M*n) (j : ℕ) (_ : j < 2*N*m) :
      dist (f i j) (f i (j+1)) ≤ D := by
    simpa only [f,dist_sub_right,dist_add_right,dist_sub_left] using repeatPath_step u hm b hu0 hum hu j
  have hbottom (i : ℕ) (_ : i ≤ 2*M*n) : 0 < (f i 0).im := by
    rw [hfi]
    simpa only [Nat.zero_div,Nat.cast_zero,sub_zero] using (show
      0 < (v (i%n)-u (0%m)-w).im+(N:ℝ)*b.im by linarith [(hierr i 0).1])
  have htop (i : ℕ) (_ : i ≤ 2*M*n) : (f i (2*N*m)).im ≤ 0 := by
    rw [hfi,Nat.mul_div_cancel _ hm,Nat.cast_mul,Nat.cast_ofNat]
    linarith [(hierr i (2*N*m)).2]
  have hcoef (j : ℕ) (hj : j ≤ 2*N*m) :
      |(N:ℝ)-((j/m:ℕ):ℝ)| ≤ N := by
    have hq : j/m ≤ 2*N := (Nat.div_le_div_right hj).trans_eq (Nat.mul_div_cancel _ hm)
    have hqr : ((j/m:ℕ):ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hq
    exact abs_le.mpr ⟨by linarith,by linarith [Nat.cast_nonneg (α := ℝ) (j/m)]⟩
  have hprod (j : ℕ) (hj : j ≤ 2*N*m) :
      -(N:ℝ)*|b.re| ≤ ((N:ℝ)-((j/m:ℕ):ℝ))*b.re ∧
      ((N:ℝ)-((j/m:ℕ):ℝ))*b.re ≤ (N:ℝ)*|b.re| := by
    have hh : |((N:ℝ)-((j/m:ℕ):ℝ))*b.re| ≤ (N:ℝ)*|b.re| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcoef j hj) (abs_nonneg _)
    simpa only [neg_mul] using abs_le.mp hh
  have hleft (j : ℕ) (hj : j ≤ 2*N*m) : (f 0 j).re < 0 := by
    rw [hfr]
    simp only [Nat.zero_div,Nat.cast_zero,zero_sub]
    nlinarith [(hrerr 0 j).2,(hprod j hj).2]
  have hright (j : ℕ) (hj : j ≤ 2*N*m) : 0 ≤ (f (2*M*n) j).re := by
    rw [hfr,Nat.mul_div_cancel _ hn,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [(hrerr (2*M*n) j).1,(hprod j hj).1]
  obtain ⟨i,_,j,_,hz⟩ := discrete_rectangle_approx_zero_rev f (2*M*n) (2*N*m)
    hD hhor hver hbottom htop hleft hright
  refine ⟨i%n,Nat.mod_lt i hn,j%m,Nat.mod_lt j hm,((i/n:ℕ):ℤ)-(M:ℤ),(N:ℤ)-((j/m:ℕ):ℤ),?_⟩
  convert hz using 1
  rw [hf]
  simp only [Int.cast_sub,Int.cast_natCast]
  congr 1
  ring

theorem path_difference_cover_horizontal (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : 0 < a.re) (hai : a.im = 0) (hb : b.im ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  rcases hb.lt_or_gt with hb | hb
  · have hzv : (fun i => star (v i)) 0 = 0 := by simp [hv0]
    have hzu : (fun i => star (u i)) 0 = 0 := by simp [hu0]
    have hva : (fun i => star (v i)) n = star a := by simp only [hvn]
    have hub : (fun i => star (u i)) m = star b := by simp only [hum]
    have hbr : 0 < (star b).im := by simpa using hb
    have hv' : ∀ i < n, dist (star (v i)) (star (v (i+1))) ≤ D := by simpa using hv
    have hu' : ∀ j < m, dist (star (u j)) (star (u (j+1))) ≤ D := by simpa using hu
    obtain ⟨i,hi,j,hj,s,t,hh⟩ := path_difference_cover (fun i => star (v i))
      (fun j => star (u j)) hn hm (star a) (star b) hzv hzu hva hub
      (by simpa using ha) (by simpa using hai) hbr hD hv' hu' (star w)
    refine ⟨i,hi,j,hj,s,t,?_⟩
    have he : ‖star (v i-u j+(s:ℂ)*a+(t:ℂ)*b-w)‖ ≤ 4*D := by
      simpa only [star_sub,star_add,star_mul,star_intCast,mul_comm] using hh
    simpa only [norm_star] using he
  · exact path_difference_cover v u hn hm a b hv0 hu0 hvn hum ha hai hb hD hv hu w

theorem path_difference_cover_general (v u : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a b : ℂ) (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = b)
    (ha : a ≠ 0) (hb : (b/a).im ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (v i) (v (i+1)) ≤ D)
    (hu : ∀ j < m, dist (u j) (u (j+1)) ≤ D) (w : ℂ) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖v i-u j+(s:ℂ)*a+(t:ℂ)*b-w‖ ≤ 4*D := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hv' : ∀ i < n, dist (v i/a) (v (i+1)/a) ≤ D/‖a‖ := by
    intro i hi
    simp only [dist_eq_norm,← sub_div,norm_div]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using hv i hi) hna.le
  have hu' : ∀ j < m, dist (u j/a) (u (j+1)/a) ≤ D/‖a‖ := by
    intro j hj
    simp only [dist_eq_norm,← sub_div,norm_div]
    exact div_le_div_of_nonneg_right (by simpa only [dist_eq_norm] using hu j hj) hna.le
  obtain ⟨i,hi,j,hj,s,t,hh⟩ := path_difference_cover_horizontal (fun i => v i/a)
    (fun j => u j/a) hn hm 1 (b/a) (by simp [hv0]) (by simp [hu0])
    (by simp [hvn,ha]) (by simp [hum]) (by norm_num) (by simp) hb
    (by positivity : 0 ≤ D/‖a‖) hv' hu' (w/a)
  refine ⟨i,hi,j,hj,s,t,?_⟩
  have he : v i/a-u j/a+(s:ℂ)*1+(t:ℂ)*(b/a)-w/a =
      (v i-u j+(s:ℂ)*a+(t:ℂ)*b-w)/a := by field_simp
  rw [he,norm_div] at hh
  have hh' := (div_le_iff₀ hna).mp hh
  calc
    _ ≤ 4 * (D/‖a‖) * ‖a‖ := hh'
    _ = 4*D := by field_simp

end

end WalkGeometry

open Module
variable {L : Type*} [AddCommGroup L]

/-- The canonical identification preserves the actual Euclidean-plane norm. -/
noncomputable def planeComplex : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

@[simp] theorem planeComplex_re (x : Plane) : (planeComplex x).re = x 0 := by
  simp [planeComplex, Complex.orthonormalBasisOneI_repr_symm_apply]

@[simp] theorem planeComplex_im (x : Plane) : (planeComplex x).im = x 1 := by
  simp [planeComplex, Complex.orthonormalBasisOneI_repr_symm_apply]

/-- The actual lattice embedding, expressed isometrically in ℂ. -/
noncomputable def complexEmbedding (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x : L) : ℂ := planeComplex (planarEmbedding b e x)

@[simp] theorem complexEmbedding_norm (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x : L) :
    ‖complexEmbedding b e x‖ = ‖planarEmbedding b e x‖ := planeComplex.norm_map _

@[simp] theorem complexEmbedding_add (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x y : L) :
    complexEmbedding b e (x + y) = complexEmbedding b e x + complexEmbedding b e y := by
  simp [complexEmbedding]

@[simp] theorem complexEmbedding_zero (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) : complexEmbedding b e (0 : L) = 0 := by
  simp [complexEmbedding]

@[simp] theorem complexEmbedding_neg (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x : L) :
    complexEmbedding b e (-x) = -complexEmbedding b e x := by
  have h := complexEmbedding_add b e x (-x)
  apply eq_neg_iff_add_eq_zero.mpr
  simpa [add_comm] using h.symm

@[simp] theorem complexEmbedding_sub (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (x y : L) :
    complexEmbedding b e (x - y) = complexEmbedding b e x - complexEmbedding b e y := by
  simp only [sub_eq_add_neg, complexEmbedding_add, complexEmbedding_neg]

@[simp] theorem complexEmbedding_zsmul (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (a : ℤ) (x : L) :
    complexEmbedding b e (a • x) = (a : ℂ) * complexEmbedding b e x := by
  simp [complexEmbedding, planarEmbedding_zsmul_signed, Complex.real_smul]

/-- The two-vector integral linear map in the supplied lattice basis. -/
noncomputable def latticeTwoVectorMap (b : Basis (Fin 2) ℤ L) (x y : L) : L →ₗ[ℤ] L :=
  Matrix.toLin b b !![b.repr x 0, b.repr y 0; b.repr x 1, b.repr y 1]

@[simp] theorem latticeTwoVectorMap_apply (b : Basis (Fin 2) ℤ L) (x y z : L) :
    latticeTwoVectorMap b x y z = (b.repr z 0) • x + (b.repr z 1) • y := by
  apply b.repr.injective
  rw [latticeTwoVectorMap, Matrix.toLin_apply]
  ext i
  fin_cases i <;> simp [Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] <;> ring

@[simp] theorem latticeTwoVectorMap_matrix_det (b : Basis (Fin 2) ℤ L) (x y : L) :
    Matrix.det (LinearMap.toMatrix b b (latticeTwoVectorMap b x y)) = latticeDet b x y := by
  rw [latticeTwoVectorMap, LinearMap.toMatrix_toLin]
  simp [Matrix.det_fin_two, latticeDet, mul_comm]

theorem latticeTwoVectorMap_injective (b : Basis (Fin 2) ℤ L) {x y : L}
    (h : latticeDet b x y ≠ 0) : Function.Injective (latticeTwoVectorMap b x y) := by
  intro z w hzw
  have h1 := congrArg (fun u => b.repr u 0) hzw
  have h2 := congrArg (fun u => b.repr u 1) hzw
  simp only [latticeTwoVectorMap_apply, map_add, map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul] at h1 h2
  have hr : latticeDet b x y * (b.repr z 0 - b.repr w 0) = 0 := by
    dsimp [latticeDet]
    linear_combination b.repr y 1 * h1 - b.repr y 0 * h2
  have hi : latticeDet b x y * (b.repr z 1 - b.repr w 1) = 0 := by
    dsimp [latticeDet]
    linear_combination b.repr x 0 * h2 - b.repr x 1 * h1
  apply b.repr.injective
  ext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left h)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left h)

/-- The exact finite quotient index equals the genuine integral determinant. -/
theorem latticeTwoVectorMap_quotient_card (b : Basis (Fin 2) ℤ L) {x y : L}
    (h : latticeDet b x y ≠ 0) :
    Nat.card (L ⧸ (latticeTwoVectorMap b x y).range) = (latticeDet b x y).natAbs := by
  let : Module.Free ℤ L := Module.Free.of_basis b
  let : Module.Finite ℤ L := Module.Finite.of_basis b
  have hh := Submodule.natAbs_det_equiv (latticeTwoVectorMap b x y).range
    (LinearEquiv.ofInjective (latticeTwoVectorMap b x y) (latticeTwoVectorMap_injective b h))
  have he : (latticeTwoVectorMap b x y).range.subtype ∘ₗ
      AddMonoidHom.toIntLinearMap ((LinearEquiv.ofInjective (latticeTwoVectorMap b x y)
        (latticeTwoVectorMap_injective b h)) : L →+ (latticeTwoVectorMap b x y).range) =
        latticeTwoVectorMap b x y := by
    ext z
    rfl
  rw [he, ← LinearMap.det_toMatrix b, latticeTwoVectorMap_matrix_det] at hh
  exact hh.symm

/-- A metric ball in the actual full lattice is a finite set. -/
noncomputable def planarLatticeBall (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) : Finset L :=
  (planarEmbedding_finite_balls b e D).toFinset

@[simp] theorem mem_planarLatticeBall (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) (z : L) :
    z ∈ planarLatticeBall b e D ↔ ‖planarEmbedding b e z‖ ≤ D := by
  simp [planarLatticeBall]


/-- Noncollinear integral vectors stay noncollinear under the actual embedding. -/
theorem complexEmbedding_div_im_ne_zero (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {a c : L} (h : latticeDet b a c ≠ 0) :
    ((complexEmbedding b e c) / (complexEmbedding b e a)).im ≠ 0 := by
  have harea : signedPlaneDet (planarEmbedding b e a) (planarEmbedding b e c) ≠ 0 := by
    rw [planarEmbedding_determinant]
    exact mul_ne_zero (by exact_mod_cast h) (planarCellDet_ne_zero e)
  have ha : complexEmbedding b e a ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    have hi := congrArg Complex.im hz
    simp only [complexEmbedding, planeComplex_re, planeComplex_im, Complex.zero_re,
      Complex.zero_im] at hr hi
    exact harea (by simp [signedPlaneDet, hr, hi])
  have hn := (Complex.normSq_pos.mpr ha).ne'
  rw [Complex.div_im, ← sub_div]
  intro hh
  have hh' := (div_eq_zero_iff.mp hh).resolve_right hn
  apply harea
  simpa [complexEmbedding, signedPlaneDet, mul_comm] using hh'

/-- Walk differences cover the actual full lattice modulo their two endpoints,
with a bounded actual-planar metric error. -/
theorem lattice_path_difference_cover (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (v u : ℕ → L) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (a c : L)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = c)
    (hac : latticeDet b a c ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (planarEmbedding b e (v i))
      (planarEmbedding b e (v (i+1))) ≤ D)
    (hu : ∀ j < m, dist (planarEmbedding b e (u j))
      (planarEmbedding b e (u (j+1))) ≤ D) (w : L) :
    ∃ i < n, ∃ j < m, ∃ s t : ℤ,
      ‖planarEmbedding b e (v i - u j + s • a + t • c - w)‖ ≤ 4 * D := by
  have ha : complexEmbedding b e a ≠ 0 := by
    intro hz
    have he : planarEmbedding b e a = 0 := planeComplex.injective (by simpa [complexEmbedding] using hz)
    have hzero : a = 0 := planarEmbedding_injective b e (he.trans (planarEmbedding_zero b e).symm)
    simp [latticeDet, hzero] at hac
  have hv' : ∀ i < n, dist (complexEmbedding b e (v i))
      (complexEmbedding b e (v (i+1))) ≤ D := by
    simpa only [complexEmbedding, planeComplex.dist_map] using hv
  have hu' : ∀ j < m, dist (complexEmbedding b e (u j))
      (complexEmbedding b e (u (j+1))) ≤ D := by
    simpa only [complexEmbedding, planeComplex.dist_map] using hu
  obtain ⟨i, hi, j, hj, s, t, hh⟩ := WalkGeometry.path_difference_cover_general
    (fun i => complexEmbedding b e (v i)) (fun j => complexEmbedding b e (u j)) hn hm
    (complexEmbedding b e a) (complexEmbedding b e c)
    (by simp [hv0]) (by simp [hu0]) (by simp [hvn]) (by simp [hum])
    ha (complexEmbedding_div_im_ne_zero b e hac) hD hv' hu' (complexEmbedding b e w)
  refine ⟨i, hi, j, hj, s, t, ?_⟩
  simpa only [← complexEmbedding_zsmul, ← complexEmbedding_sub, ← complexEmbedding_add,
    complexEmbedding_norm] using hh

/-- Determinant many-differences bound for an arbitrary full planar lattice.
The only multiplicative loss is the cardinality of an actual radius `4D` ball. -/
theorem lattice_path_difference_card (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (v u : ℕ → L) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (a c : L)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = c)
    (hac : latticeDet b a c ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (planarEmbedding b e (v i))
      (planarEmbedding b e (v (i+1))) ≤ D)
    (hu : ∀ j < m, dist (planarEmbedding b e (u j))
      (planarEmbedding b e (u (j+1))) ≤ D)
    (E : Finset L) (hE : ∀ i < n, ∀ j < m, v i - u j ∈ E) :
    (latticeDet b a c).natAbs ≤ E.card * (planarLatticeBall b e (4 * D)).card := by
  classical
  let Q := (latticeTwoVectorMap b a c).range
  have hcard : Nat.card (L ⧸ Q) = (latticeDet b a c).natAbs :=
    latticeTwoVectorMap_quotient_card b hac
  have : Finite (L ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcard]; simpa using hac)
  let : Fintype (L ⧸ Q) := Fintype.ofFinite _
  let F : E × (planarLatticeBall b e (4 * D)) → L ⧸ Q :=
    fun x => Q.mkQ (x.1.val + x.2.val)
  have hf : Function.Surjective F := by
    intro q
    obtain ⟨w, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨i, hi, j, hj, s, t, hh⟩ := lattice_path_difference_cover b e v u hn hm a c
      hv0 hu0 hvn hum hac hD hv hu w
    let r : L := -(v i - u j + s • a + t • c - w)
    have hr : r ∈ planarLatticeBall b e (4 * D) := by
      rw [mem_planarLatticeBall]
      rw [← complexEmbedding_norm]
      dsimp only [r]
      rw [complexEmbedding_neg, norm_neg, complexEmbedding_norm]
      exact hh
    refine ⟨(⟨v i - u j, hE i hi j hj⟩, ⟨r, hr⟩), ?_⟩
    apply (Submodule.Quotient.eq Q).mpr
    change (v i - u j) + r - w ∈ (latticeTwoVectorMap b a c).range
    refine ⟨(-s) • b 0 + (-t) • b 1, ?_⟩
    rw [latticeTwoVectorMap_apply]
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      b.repr_self, Finsupp.single_apply, Fin.isValue, ↓reduceIte, smul_eq_mul,
      mul_one]
    dsimp [r]
    abel_nf
    simp
  have hh := Fintype.card_le_of_surjective F hf
  have hQ : Fintype.card (L ⧸ Q) = (latticeDet b a c).natAbs := by
    rw [← Nat.card_eq_fintype_card, hcard]
  simpa only [Fintype.card_prod, Fintype.card_coe, hQ] using hh


/-- The same bound in actual Euclidean area units, with the genuine fundamental
cell area. This is the torus-area many-differences step of manuscript Lemma `lem:differences`. -/
theorem lattice_path_difference_area (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (v u : ℕ → L) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (a c : L)
    (hv0 : v 0 = 0) (hu0 : u 0 = 0) (hvn : v n = a) (hum : u m = c)
    (hac : latticeDet b a c ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (planarEmbedding b e (v i))
      (planarEmbedding b e (v (i+1))) ≤ D)
    (hu : ∀ j < m, dist (planarEmbedding b e (u j))
      (planarEmbedding b e (u (j+1))) ≤ D)
    (E : Finset L) (hE : ∀ i < n, ∀ j < m, v i - u j ∈ E) :
    |signedPlaneDet (planarEmbedding b e a) (planarEmbedding b e c)| ≤
      (E.card : ℝ) * (planarLatticeBall b e (4 * D)).card * |planarCellDet e| := by
  have hc := lattice_path_difference_card b e v u hn hm a c hv0 hu0 hvn hum hac hD hv hu E hE
  have hr : ((latticeDet b a c).natAbs : ℝ) ≤
      (E.card : ℝ) * (planarLatticeBall b e (4 * D)).card := by exact_mod_cast hc
  have hi : ((latticeDet b a c).natAbs : ℝ) = |(latticeDet b a c : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (latticeDet b a c))
  rw [hi] at hr
  rw [planarEmbedding_determinant, abs_mul]
  exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)


/-- Translation-free form: two bounded-step lattice paths with a common
initial vertex force many differences, measured by the endpoint determinant. -/
theorem lattice_path_difference_card_from_common_origin (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (v u : ℕ → L) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (p : L) (hv0 : v 0 = p) (hu0 : u 0 = p)
    (hac : latticeDet b (v n - p) (u m - p) ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (planarEmbedding b e (v i))
      (planarEmbedding b e (v (i+1))) ≤ D)
    (hu : ∀ j < m, dist (planarEmbedding b e (u j))
      (planarEmbedding b e (u (j+1))) ≤ D)
    (E : Finset L) (hE : ∀ i < n, ∀ j < m, v i - u j ∈ E) :
    (latticeDet b (v n - p) (u m - p)).natAbs ≤
      E.card * (planarLatticeBall b e (4 * D)).card := by
  apply lattice_path_difference_card b e (fun i => v i - p) (fun j => u j - p)
    hn hm (v n - p) (u m - p) (by simp [hv0]) (by simp [hu0]) rfl rfl hac hD
  · simpa only [planarEmbedding_sub_signed, dist_sub_right] using hv
  · simpa only [planarEmbedding_sub_signed, dist_sub_right] using hu
  · intro i hi j hj
    simpa only [sub_sub_sub_cancel_right] using hE i hi j hj

/-- The genuine finite difference set of lattice vertices. -/
noncomputable def latticeDifferences (V : Finset L) : Finset L := by
  classical
  exact (V ×ˢ V).image (fun z => z.1 - z.2)

theorem sub_mem_latticeDifferences (V : Finset L) {x y : L}
    (hx : x ∈ V) (hy : y ∈ V) : x - y ∈ latticeDifferences V := by
  classical
  exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

/-- Main-chain many-differences bound for vertex sets containing two walk
segments from a common origin. No norm, determinant, or bound is assumed. -/
theorem lattice_walk_many_differences (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (v u : ℕ → L) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (p : L) (hv0 : v 0 = p) (hu0 : u 0 = p)
    (hac : latticeDet b (v n - p) (u m - p) ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hv : ∀ i < n, dist (planarEmbedding b e (v i))
      (planarEmbedding b e (v (i+1))) ≤ D)
    (hu : ∀ j < m, dist (planarEmbedding b e (u j))
      (planarEmbedding b e (u (j+1))) ≤ D)
    (V : Finset L) (hvV : ∀ i < n, v i ∈ V) (huV : ∀ j < m, u j ∈ V) :
    (latticeDet b (v n - p) (u m - p)).natAbs ≤
      (latticeDifferences V).card * (planarLatticeBall b e (4 * D)).card :=
  lattice_path_difference_card_from_common_origin b e v u hn hm p hv0 hu0 hac hD hv hu
    (latticeDifferences V) (fun i hi j hj => sub_mem_latticeDifferences V (hvV i hi) (huV j hj))

end Entry002
