# Exact maximum purity for all qutrit-qudit APPT spectra

Private parent research draft, 9 October 2026, 04:07 UTC.
Status: complete written reduction plus exact rational certificates checked
by two implementations; NOT yet Lean-formalized, NOT publicly released,
NOT independently refereed. Novelty is not certified. This treats m=3,
all n>=3, NOT the full arbitrary-m conjecture and NOT equality of APPT
and absolute separability.

## Theorem
For every integer n>=3, the maximum purity of absolutely PPT states on
C^3 tensor C^n is

  (3n+8)/(3n+2)^2,  if 3<=n<=8;
  3/(8n),          if n>=9.

Attaining spectra are respectively
 (3,1,...,1)/(3n+2),
 (2 repeated n times,1 repeated 2n times)/(4n).
The n=2 system is the already-solved qubit-qutrit case after swapping
factors; its maximum 7/32 is not claimed as new.

This confirms the m=3 branch of Ahiable--Kothakonda--Winter's Conjecture
6.7, arXiv:2608.03390v1. It supplies the exact value of the qutrit-qudit
optimization problem left open in Tran, arXiv:2609.18568v1, Remark 1.1.
The older Dung--Khoi qutrit formula was already disproved by Tran; that
is not the claim of this draft.

## 1. Standard spectral criterion
Put D=3n and list a state's eigenvalues lambda_1>=...>=lambda_D>=0,
with total sum one. Hildebrand's qutrit-qudit criterion is equivalent to
positive semidefiniteness of both real symmetric matrices

 A = [[2 lambda_D, lambda_(D-1)-lambda_1, lambda_(D-3)-lambda_2],
      [lambda_(D-1)-lambda_1,2 lambda_(D-2),lambda_(D-4)-lambda_3],
      [lambda_(D-3)-lambda_2,lambda_(D-4)-lambda_3,2 lambda_(D-5)]],
 B = [[2 lambda_D, lambda_(D-1)-lambda_1, lambda_(D-2)-lambda_2],
      [lambda_(D-1)-lambda_1,2 lambda_(D-3),lambda_(D-4)-lambda_3],
      [lambda_(D-2)-lambda_2,lambda_(D-4)-lambda_3,2 lambda_(D-5)]].

See Dung--Khoi, arXiv:2510.19508v1, Eq. (3), citing Hildebrand,
Corollary V.3. For D=9 these are Wang--Chen--Song,
arXiv:2603.20717v1, Eqs. (7),(9). All subsequent optimization arguments
use exactly these matrices. Singular spectra follow directly from the
closed inequalities, or by APPT-preserving mixing with I/D and a limit.

## 2. Six small dimensions, with exact finite certificates
For D=9,12,15,18,21,24 set g_i=lambda_i-lambda_(i+1) for i<D and
g_D=lambda_D. Let T=sum lambda_i. The supplied exact certificates prove

 [(D+8) T^2 -(D+2)^2 sum lambda_i^2] T = sum_j c_j G_j,

with strictly positive rational coefficients. Each G_j is a cubic gap
monomial, det A, det B, a principal 2x2 minor times a gap, or
(v^t A v)g_i g_j / (v^t B v)g_i g_j for an explicit integer vector v.
These generators are nonnegative for nonnegative gaps and PSD A,B.
Putting T=1 gives the stated upper bounds.

Certificate files and term counts:
 D9: qutrit_cubic_certificate_search.json, 166;
 D12: qutrit_D12_cubic_certificate.json, 363;
 D15: qutrit_D15_fast_certificate.json, 679;
 D18: qutrit_D18_fast_certificate.json, 1139;
 D21: qutrit_D21_fast_certificate.json, 1769;
 D24: qutrit_D24_fast_certificate.json, 2596.

These are rational polynomial identities, not claims based on solver
success or rounded optimization. Every coefficient and identity was
rechecked by verify_finite_certificates_sympy.py. The D9 certificate
was also independently verified by the Fraction-only verifier.

## 3. Compress all middle eigenvalues to two endpoint populations
For D>=27 define the nine outer values
 y=(lambda_1,lambda_2,lambda_3,lambda_(D-5),...,lambda_D).
Write a=y_3, b=y_4, and M=D-9>=18. The M middle eigenvalues lie in [b,a].
Let their sum be L. There exist real t,z>=0 with t+z=M and
 L=t a+z b: if a>b choose t=(L-Mb)/(a-b), z=M-t;
if a=b choose t=0,z=M.
For every x in [b,a], (a-x)(x-b)>=0 gives
 x^2<=(a+b)x-ab. Summing yields
 sum_middle lambda_i^2 <= t a^2+z b^2.

Set
 T=sum_(i=1)^9 y_i+t a+z b,
 S=sum_(i=1)^9 y_i^2+t a^2+z b^2,
 D=9+t+z.
Thus T=1 and actual purity is at most S. The original A,B depend only
on y and are exactly the D9 matrices of Section 1 with y substituted.

## 4. One uniform exact certificate, valid for every real population
Write the ordered nonnegative y in nine nonnegative gaps g_i. Let
 w=t+z-18>=0. PSD A implies
 0<=(1,1,1) A (1,1,1)^t
   =2(sum_(i=4)^9 y_i-sum_(i=1)^3 y_i).
Consequently a<=2b, since sum_top>=3a and sum_bottom<=6b.
More explicitly, the nonnegative linear form R=2b-a satisfies

 3R = (sum_bottom-sum_top)
      +(y_1-a)+(y_2-a)+sum_(i=4)^9 (b-y_i).

The exact certificate qutrit_uniform_parameter_search.json proves

 (9 T^2 -8 D S) T = sum_j c_j G_j

with 1635 strictly positive rational coefficients. Its generators are:
1. Ordinary nonnegative monomials in the gaps and t,z;
2. The Section 2 PSD/gap generators, multiplied by monomials in t,z,w;
3. R*g_i*g_j multiplied by such nonnegative parameter monomials;
4. (t a-z b)^2*g_i times one of 1,t,z,w;
5. [c0*(9T-4D(a+b))+c1*(t a-z b)]^2*g_i times one of 1,t,z,w,
   for explicitly recorded integers c0,c1.

All generators are manifestly nonnegative under the stated hypotheses;
R>=0 was just derived, not assumed as an unresolved interface.
The identity and coefficient signs were independently verified by
verify_uniform_certificate_sympy.py, which does not import search code
or call an optimizer. Its log records exact zero residual and positive
coefficients. The discovery code independently reconstructs the same
identity with Python Fraction sparse polynomials after rational linear
algebra reconstruction. No floating value enters either identity check.

Putting T=1 yields S<=9/(8D)=3/(8n), and hence the desired upper bound
for ALL integers n>=9. In fact the algebraic certificate works for all
real t,z>=0 with t+z>=18, so no unchecked dimension tail remains.

## 5. Attainment
For (3,1,...,1)/(D+2), both criterion matrices equal
 [[2,-2,0],[-2,2,0],[0,0,2]]/(D+2), which is PSD.
The purity is (D+8)/(D+2)^2.
For (2^n,1^(2n))/(4n), n>=3 ensures the top three entries are 2/(4n)
and bottom six are 1/(4n). Both criterion matrices equal
 (3I-J)/(4n), which is PSD; its quadratic form is the sum of the three
pairwise squared coordinate differences divided by 4n.
The purity is (4n+2n)/(16n^2)=3/(8n).
Together with Sections 2 and 4 these prove the theorem.

## 6. Boundary between the two formulas
The comparison 9/(8D)>=(D+8)/(D+2)^2 is equivalent to
D^2-28D+36>=0. It is negative at the multiples of three D=9,...,24,
and positive for every D>=27 (value 9 at 27, then increasing).
Thus the two pieces agree with the inner-polytope prediction, with the
transition between n=8 and n=9.

## Verification and remaining work
All six finite identities and the single uniform identity have passed
exact independent checks. A separate D27 finite certificate was also
found and checked but is redundant for the theorem and is not needed.
Next: parent-written Lean proof of the spectral optimization, including
all certificate signs, polynomial identities, matrix-PSD implications,
normalization, middle-eigenvalue compression and attainment. Do not
label numerical LP success alone as a proof; do not claim full arbitrary
m or absolute-separability equality. No public release yet.
