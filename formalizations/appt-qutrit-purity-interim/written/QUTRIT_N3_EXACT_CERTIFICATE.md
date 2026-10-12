# Two-qutrit APPT purity: exact algebraic certificate (private working result)

Date: 2026-10-09. Status: exact rational polynomial identity independently
verified in two implementations; no Lean proof yet, no public release,
no novelty guarantee. This settles the spectral optimization for 3 by 3
provided the standard Hildebrand APPT spectral criterion. It does NOT
settle Conjecture 6.7 for arbitrary m,n.

Let lambda_1 >= ... >= lambda_9 >= 0 have sum T=1. Set
 g_i=lambda_i-lambda_(i+1) for i=1,...,8 and g_9=lambda_9.
Let A=L1(lambda) and B=L2(lambda) be the two 3x3 matrices in equations
(7) and (9) of Wang--Chen--Song, arXiv:2603.20717v1. Their explicit
entries are independently encoded in both scripts below. Assume A,B PSD.

The exact certificate in qutrit_cubic_certificate_search.json proves

 (17 T^2 - 121 sum_i lambda_i^2) T
   = sum_j c_j G_j(g),

where all 166 rational c_j are strictly positive, and each G_j is one of:
- a degree-three monomial in nonnegative gaps;
- det A or det B;
- a principal 2x2 minor of A or B times a nonnegative gap;
- (v^t A v) g_i g_j or (v^t B v) g_i g_j for an explicit integer v.

Every generator is nonnegative. Therefore sum lambda_i^2 <=17/121.
The ordered spectrum (3,1,1,1,1,1,1,1,1)/11 attains this bound:
A=B=[[2,-2,0],[-2,2,0],[0,0,2]]/11 is PSD.
The standard APPT criterion makes this an actual APPT spectrum. The
rank-deficient boundary is covered by continuity / mixing with I/9.

Uniqueness: the certificate has strictly positive pure-cube coefficients
for each g_2,...,g_8 (respectively 1,18,448,1,675/2,550,960).
Equality therefore forces all seven gaps to vanish. The remaining
quadratic target factorizes as
 17 T^2 -121 sum lambda_i^2 = 8(2g_9-g_1)(13g_1+18g_9).
PSD forces g_1<=2g_9, and normalization excludes g_1=g_9=0.
Equality hence gives g_1=2g_9 and T=g_1+9g_9=11g_9=1,
which is precisely the displayed spectrum. Conversely it attains equality.

The LP is only a certificate finder. Its output was reconstructed by
exact rational linear algebra and polynomial subtraction. A separate
checker, verify_qutrit_certificate.py, uses only Python Fraction and
sparse coefficient dictionaries, imports no optimizer or SymPy, and
independently reconstructs every polynomial from the named generators.
Both checks find identically zero residual and positive coefficients.

Sources / target distinctions:
- Ahiable--Kothakonda--Winter, arXiv:2608.03390v1, Conjecture 6.7,
  predicts the general APPT maximal purity equals that of its polytope.
- Wang--Chen--Song, arXiv:2603.20717v1, equations (7),(9), Lemma 3,
  supplies the exact two-qutrit APPT matrix criterion.
- Tran, arXiv:2609.18568v1, treats qubit-qudit purity and disproves a
  different older qutrit conjecture; this certificate is NOT a purported
  new disproof of that already disproved statement.

Next: determine whether this certificate method extends to all qutrit-
qudit dimensions, or yields a uniform parameter certificate. No public
claim of the complete general APPT conjecture is warranted.
