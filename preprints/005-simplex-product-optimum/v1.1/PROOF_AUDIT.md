# Proof audit: simplex-product optimization, v1.1

## Scope

Complete written proof for products of simplices and their affine images. Not a theorem for all convex bodies. No independent peer review or proof-assistant formalization is claimed.

## Checked dependencies

1. **Geometric constants.** Facet area-normal vectors give the product identity and the simplex value c_d=(d+1)d^d/d!. Interval factors use the stated zero-dimensional projection convention.
2. **Concavity.** The differentiated expression D'(x)=(x^2-x-4)/(x(x+1)^2(x+2)^2), the strict trapezoidal estimate at x=2, and the limit D(x)->0 prove strict decrease of r(x) for x>=2. The only repeated discrete increment is r_1=r_2.
3. **Infinite scope.** Monotone h_n locates the unique optimal root at 13 from two exact comparisons. The piecewise-linear perspective reduces all dimensions to two factor counts. Finite numerical experiments are not used to infer this statement.
4. **Sharp recurrence.** Supporting lines give upper bounds even when a formal multiplicity is negative. The winning expression is feasible from n=100 onward; the exact n=99 obstruction proves the threshold sharp.
5. **Uniqueness.** The global candidates have mean part at least seven whenever two counts are possible, excluding the low-dimensional concavity degeneracy. Eighty exact finite no-tie comparisons complete the remaining range 14..99; six multiples of 13 have only one candidate.
6. **Sharp stability.** The exact runner-up root is 14. A further exact comparison gives lambda_12<2 lambda_14, so the uniform deficit is at most 112 gamma. The optimizer T_14^8 at n=112 attains the dimension-mass bound, proving sharpness of 112.

## Replay

`verification/verify_exact.py --limit 300 --output verification/exact_certificate.json`

The standard-library verifier checks seven strict rational inequalities and records positive integer margins, eighty finite no-tie cases, all optimal dimension multisets by exhaustive DP through 300, the recurrence failure at 99, and rational bounds on rho. It raises explicit exceptions, so `python -O` does not disable checks. A second run under `python -O` through dimension 112 passed.

These are finite exact checks and a differently structured DP cross-check, not a formalization of the analytic infinite-dimensional argument or an external referee report.
