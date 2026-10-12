# Mixed-volume normalization guard

8 October 2026. Added after the independent reviewer's source check. The frozen
main draft is unchanged; its mixed-volume formula already uses the correct
standard normalization.

Throughout our apex-count proof, mixed volume is normalized by

    V(B[q])=Vol_q(B).

Consequently the coefficient of lambda_1...lambda_q in

    Vol_q(lambda_1 K_1+...+lambda_q K_q)

is q! V(K_1,...,K_q), not just V(K_1,...,K_q). Grouping repeated factors
therefore yields precisely

    Vol_q(aB+bZ)
       =sum_(j=0)^q binom(q,j) a^(q-j)b^j V(B[q-j],Z[j]).

This is the formula explicitly written and used in the frozen main proof.
For example q=2 and K_1=K_2=B give (lambda_1+lambda_2)^2 Vol_2(B), whose
mixed coefficient is 2 Vol_2(B). This directly checks the factorial.

In Bihan--Soprunov arXiv:1702.07676v2, the displayed coefficient statement
in Theorem 2.1 appears to omit this factorial relative to their own
definition (1.1). We do **not** import that displayed coefficient statement
literally. The citation supplies background on classical mixed-volume
polynomials, monotonicity, and the essential-collection positivity criterion;
our stated normalization and explicit binomial coefficients govern every
calculation.

In particular the beta integral used in the new cone lemma is

    binom(q,j) integral_rho^1
       [(s-rho)/(1-rho)]^(q-j)
       [rho(1-s)/(1-rho)]^j ds
       =(1-rho)rho^j/(q+1).

Its binomial factor is present in the mathematical text and is independently
recomputed by monomial integration in `check_apex_formula.py`. No result or
constant in the frozen theorem needs correction because of the source's
apparent typographical omission.
