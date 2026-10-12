# Mathematical and verification audit

This is self-review supported by finite exact replay and kernel-checked
finite incidence reasoning. It is not an external mathematician review.

The maximum-weight edge exists because the family is finite and nonempty.
Every original edge has r>=2 vertices. The weighted-star count permits
repeated intersections. Each edge weight and every peak deficit is
nonnegative. The average inequality Y<=mb and r-1>0 justify the harmonic
bound and the exact deficit budget. The extraction denominator is divided
only when Y>m/(k+1). The strict retained threshold gives degree at most k.

The design-boundary argument splits at d=m/[2k(k+1)], with equality
included in the positive-denominator branch. The complementary branch
uses s<=m; thus (6) is valid for arbitrarily large deficits as well.
Empty cores satisfy all identities with zero sums and zero active count.
The degree/excess identity follows from two explicitly written double
counts. It retains multiple intersections rather than silently assuming
linearity. The active-count and variance inequalities use d_v>=1.

The iff statement concerns fractional extremality, not integer extremality
alone. Its converse supplies a genuinely feasible vector on the original
family by putting zero on deleted edges. All limits keep a and k fixed.
The numerator in (3) is o(r²) and its denominator is Theta(r²), while
its extra factor m is Theta(r), yielding o(r) deletions.

Integer rounding is attributed to Kahn 1994 Corollary 5.4. It is applied
only after deleting one original edge for every pair above the rho r
intersection threshold. The number deleted is o(r), the residual maximum
intersection is o(r), and it has at most (a+eta)r edges for every fixed
eta>0 eventually. Eta is decreased only after the limsup. Original edges
deleted in either stage are each covered by one vertex. No arbitrary
optimal fractional vector is assumed to satisfy a rounding condition.

The k=2 construction has an exact primal integer cover and a feasible
dual vector of the same value. Its matching-pair incidence argument proves
the minimum deletion count, and six finite cases are independently
exhausted. All original bad--good intersections are exactly one, so the
whole-family excess formula is exact. The n=2j^4, t=j^3 sequence shows
that deletion cannot be omitted even at fractional extremality.

Seven Lean exports were compiled without errors or warnings. Three of
them directly address actual finite incidence, with two additional finite
converse exports; all printed axioms are exactly standard Lean foundations.
They do not formalize the whole note. The exact checker uses explicit
RuntimeError checks, so Python -O preserves verification. Its fixed seed
is merely a reproducible source of feasible diagnostic vectors.

The requested GPT-6 Luna High agent performed a limited literature check,
not proof validation. It found the primary Kayll 1995 theorem resolving
Kahn 5.6 and did not verify a full resolution status for 5.5. The finite
fixed-ratio stability claim remains under broader novelty comparison.
No OpenAI/math theorem, optimizer or solver status enters this proof.
