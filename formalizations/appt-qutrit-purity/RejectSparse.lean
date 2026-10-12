import APPT.SparsePolynomial
open APPT.SparsePolynomial
-- Deliberately change one mixed cubic coefficient from three to four.
example : trim (mul [([0],1),([1],1)]
    (mul [([0],1),([1],1)] [([0],1),([1],1)])) =
    [([0,0,0],1),([0,0,1],4),([0,1,1],3),([1,1,1],1)] := by decide +kernel
