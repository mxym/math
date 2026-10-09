import APPT.CoefficientMerge
namespace APPT.CoefficientMerge

theorem eval_append (f : Nat → ℝ) (xs ys : Poly) :
    eval f (xs++ys) = eval f xs+eval f ys := by
  induction xs with
  | nil => simp [eval]
  | cons x xs ih => rcases x with ⟨k,c⟩; simp [eval, ih, add_assoc]

/-- Primitive recursion avoids well-founded proof reduction in large kernel computations.
Even the zero-fuel branch preserves evaluation; concrete equalities check the output. -/
def mergeAux : Nat → Poly → Poly → Poly
  | 0, xs, ys => xs++ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | k+1, (i,c)::xs, (j,d)::ys =>
    if i < j then (i,c)::mergeAux k xs ((j,d)::ys)
    else if j < i then (j,d)::mergeAux k ((i,c)::xs) ys
    else (i,c+d)::mergeAux k xs ys

theorem eval_mergeAux (f : Nat → ℝ) (k : Nat) (xs ys : Poly) :
    eval f (mergeAux k xs ys) = eval f xs+eval f ys := by
  induction k generalizing xs ys with
  | zero => exact eval_append f xs ys
  | succ k ih =>
    cases xs with
    | nil => simp [mergeAux,eval]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeAux,eval]
      | cons y ys =>
        rcases x with ⟨i,c⟩
        rcases y with ⟨j,d⟩
        by_cases hij : i < j
        · simp [mergeAux,hij,eval,ih]; ring
        · by_cases hji : j < i
          · simp [mergeAux,hij,hji,eval,ih]; ring
          · have he : i=j := by omega
            subst j
            simp [mergeAux,eval,ih,Int.cast_add]; ring

def fastMerge (xs ys : Poly) : Poly := mergeAux (xs.length+ys.length) xs ys

theorem eval_fastMerge (f : Nat → ℝ) (xs ys : Poly) :
    eval f (fastMerge xs ys) = eval f xs+eval f ys := eval_mergeAux ..

end APPT.CoefficientMerge
