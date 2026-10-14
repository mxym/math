# Full Lih-Wang permanent chord conjecture: original whole-domain attempt

Yongxian Zhang, School of Computer Science and Engineering, South China
University of Technology; mxymmxym1@gmail.com; ORCID0009-0000-3864-3536.
14 October 2026. No external funding. OpenAI AI assistants assisted.
Original route exposition all rights reserved; prior results remain credited.
Active ordinary research, not a solved theorem, Lean or priority claim.

## L0. The complete original target and clock

The new stage starts at 2026-10-14 01:32:35 UTC after the Ryser boundary
and authorized APPT service. Requested index/metadata services, preservation,
disconnections and idle time are excluded. Without a substantial complete
solution, preserve and change full targets within 45-90 effective minutes.

Let Omega_n be all real nonnegative n-by-n matrices with every row and
column sum one, and let J_n have every entry 1/n. The complete original
Lih-Wang conjecture is, for every integer n>=3, every A in Omega_n and
every real alpha in [1/2,1],

    per[alpha J_n+(1-alpha)A]
       <= alpha n!/n^n+(1-alpha)per A.                       (L1)

The full real alpha interval [1/2,1] is the original definition, not a
chosen residual parameter band. The formulation is reproduced in the
[published 2024 introduction, equation (3)](https://www.degruyterbrill.com/document/doi/10.1515/spma-2024-0006/html)
and [Cheon-Wanless Conjecture 34](https://users.monash.edu.au/~iwanless/papers/permsurveyLAA.pdf),
page 332. The 1982 original is traced bibliographically through these
primary publications; its full text was not retrieved or claimed read.

The [formal 2024 Theorem 2.1](https://www.degruyterbrill.com/document/doi/10.1515/spma-2024-0006/html)
already covers every order-four matrix over an interval containing the
whole original alpha band. Its Theorem 2.2 covers order six with three
additional root-free polynomial hypotheses and alpha>=0.7836. The older
arXiv abstract's broader order-six wording is not substituted for the
published statement. Order-three and those published cases are not new
major targets. Current primary-author progress also covers certain sparse
order-five mixtures; it does not close L1 at all orders. No later full
resolution was found in a bounded current primary-source search.

A positive solution must prove L1 on the entire original domain. An exact
actual doubly stochastic rational A with a rational alpha in [1/2,1] and
strict reverse inequality would disprove the whole universal assertion.
It needs exact margins and two independently structured permanent checks.
Finite nonviolations, midpoint-only statements, normal/rank/mixture/root-free
classes and inadmissible alpha<1/2 examples are not a full result.

## L2. Exact all-size polynomial target

Write t=1-alpha in [0,1/2], B=A-J_n, and let r_m(B) be the weighted
nonattacking-rook sum. Both sets of margins of B vanish. Multilinearity gives

    f_A(t)=per(J_n+tB)=sum_(m=0)^n c_m t^m,
    c_m=(n-m)! n^(-(n-m)) r_m(B),
    c_0=n!/n^n,  c_1=0.                                    (L2)

Every term is obtained by choosing its m B entries and permuting the
remaining n-m columns, as in the saved exact Ryser identity. Thus the full
conjectured chord gap is precisely

    G_A(t)=(1-t)c_0+t per A-f_A(t)
          =sum_(m=2)^n c_m(t-t^m)
          =t(1-t) sum_(m=2)^n c_m sum_(j=0)^(m-2) t^j.     (L3)

There is no established sign of the last all-size polynomial for every
doubly stochastic A and every t in [0,1/2]. The centered coefficients need
not all be nonnegative, so coefficient positivity is not an available
proof. A midpoint proof alone must be accompanied by a rigorous whole-
interval implication; no such implication is assumed here.

For the known sharp control A=(I_3+C_3)/2, c_2=1/12 and c_3=-1/18, giving

    G_A(t)=t(1-t)(1-2t)/36
          =alpha(1-alpha)(2alpha-1)/36.                     (L4)

This is nonnegative on exactly the relevant half interval and is negative
for 0<alpha<1/2. It protects the original domain but is not a new
counterexample to L1. Nor may a permutation-vertex check suffice: at
t=1/2 each of I_3 and C_3 has gap 1/4, while their midpoint A has gap zero.
The gap is not concave over the doubly stochastic polytope, so convex
combinations do not inherit a lower bound merely from vertex values.

No new major-conjecture result, full Lean build, source audit, publication
or external peer review is asserted by this active route record.
