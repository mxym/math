import APPT.SparsePolynomial
open APPT.SparsePolynomial
example : trim (mul [([0],1),([1],1)]
    (mul [([0],1),([1],1)] [([0],1),([1],1)])) =
    [([0,0,0],1),([0,0,1],3),([0,1,1],3),([1,1,1],1)] := by decide +kernel
