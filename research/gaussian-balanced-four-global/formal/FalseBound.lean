import Mathlib.Tactic
-- False weakened profile: a=3/5,b=1,w=5/4,tr=5/2 meets every hypothesis.
-- Replacing 3*b/4<a by b/2<a cannot yield the trace contradiction.
example (a b w tr : ℝ)
    (hb : 0 < b) (hab : a < b) (ha : b/2 < a)
    (hw : 2*(b-a)*w = b) (htr : 2*w ≤ tr) (hupper : tr ≤ 3) : False := by
  nlinarith
