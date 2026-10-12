# Boundary check: the new projection exponent and constant are exactly sharp

8 October 2026. Addendum after the main draft was frozen. This does not change
its proof or conclusions; it strengthens the justification for the sharp
geometric example by computing the maximum over **all** projection directions.

Fix 1<=r<=d-1, put m=r+1, and let 0<rho<1. In the standard simplex

    P=conv(0,e_1,...,e_d)

take

    K=conv(e_1,...,e_d,rho e_1,...,rho e_m).

The omitted region is the simplex with intercepts rho on the first m
coordinate rays and one on the other rays. Equivalently,

    K={x>=0, sum x_i<=1,
          rho^(-1)sum_(i<=m)x_i+sum_(i>m)x_i>=1}.

Its barycentric loss at zero is rho. The actual facet area-normal vectors,
with c=1/(d-1)!, are

    -c(1-rho^(m-1))e_i,     i<=m,
    -c(1-rho^m)e_i,         i>m,
    c(1,...,1),
    -c(rho^(m-1),...,rho^(m-1),rho^m,...,rho^m).

These follow by removing the corresponding scaled face of the omitted
simplex from each coordinate facet; the new facet vector follows directly
from its intercepts. They balance to zero. Thus Cauchy's projection formula
gives, for a nonzero direction u and the abbreviations

    A=sum_(i<=m)u_i,  B=sum_(i>m)u_i,
    A_abs=sum_(i<=m)|u_i|,  B_abs=sum_(i>m)|u_i|,

the exact ratio

    [pi_P(u)-pi_K(u)]/pi_P(u)
      =rho^(m-1) [A_abs+rho B_abs-|A+rho B|]
                    /[A_abs+B_abs+|A+B|].                         (1)

The square-bracket numerator is nonnegative by the triangle inequality and
is at most A_abs+B_abs+|A+B|. Therefore every projection direction satisfies

    [pi_P(u)-pi_K(u)]/pi_P(u) <= rho^(m-1)=rho^r.

For u=e_1-e_2, equality holds. Hence

    max_(unit u) [pi_P(u)-pi_K(u)]/pi_P(u) = rho^r.                 (2)

This proves exact sharpness of both the exponent r and the multiplicative
constant one in the apex-count projection lemma. Merely displaying one
direction of equality would not, by itself, have proved optimality of an
existence-of-direction bound; equation (1) supplies the necessary upper
bound for all other directions as well.

The assumptions used in the main theorem are genuinely met: K has d+m=
d+1+r vertices, its intersection with every facet plane of P is full
(d-1)-dimensional, and it is a (d-m)-fold pyramid over the m-dimensional
equal-intercept truncation. The endpoint rho=0 gives K=P by continuity;
rho=1 is excluded because the displayed K then loses full dimension.

This is a geometric-projection calculation. The original Entry005 defect
asymptotics, and the prescribed maximum simplex in this same family, are
verified separately in Section 7 of the frozen main draft.
