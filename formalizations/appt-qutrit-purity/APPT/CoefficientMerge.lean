import APPT.Core

namespace APPT.CoefficientMerge

abbrev Poly := List (Nat × Int)

def eval (f : Nat → ℝ) : Poly → ℝ
  | [] => 0
  | (k,c)::xs => (c : ℝ)*f k + eval f xs

def merge : Poly → Poly → Poly
  | [], ys => ys
  | xs, [] => xs
  | (k,c)::xs, (l,d)::ys =>
    if k < l then (k,c) :: merge xs ((l,d)::ys)
    else if l < k then (l,d) :: merge ((k,c)::xs) ys
    else (k,c+d) :: merge xs ys
termination_by xs ys => xs.length + ys.length

/-- Exact coefficient merging preserves evaluation in the real numbers. -/
theorem eval_merge (f : Nat → ℝ) (xs ys : Poly) :
    eval f (merge xs ys) = eval f xs + eval f ys := by
  fun_induction merge xs ys <;> simp_all [merge, eval, Int.cast_add]
  all_goals try ring1
  case case5 k c xs l d ys h1 h2 ih =>
    have h : k=l := by omega
    subst l
    ring

def scale (c : Int) (xs : Poly) : Poly := xs.map (fun p => (p.1,c*p.2))

theorem eval_scale (f : Nat → ℝ) (c : Int) (xs : Poly) :
    eval f (scale c xs) = (c : ℝ)*eval f xs := by
  induction xs with
  | nil => simp [scale,eval]
  | cons p xs ih =>
    rcases p with ⟨k,d⟩
    simp only [scale, List.map_cons, eval, Int.cast_mul] at *
    rw [ih]
    ring

end APPT.CoefficientMerge
