# End of the weak scalar-arithmetic stage (2026-10-08)

## Result and its exact scope

A precisely bounded combination of necessary conditions is insufficient for the Bell–Skandera conclusion: positive integral coefficients and constant term one; strict Newton inequalities; irreducibility; positive integral discriminant and algebraic norm; and, for every nonzero integer pair (a,b), the uniform weak bound

`Tr((a lambda+b)^2) >= 7`,

obtained using only the nonzero integral-norm lower bound `|Norm(a lambda+b)| >= 1`. The statement does not assert satisfaction of bounds retaining the actual norm magnitude.

The candidate is

`f(t)=1+9t+28t^2+48t^3+49t^4+27t^5+8t^6+t^7`.

Its reciprocal signed monic polynomial is

`G(X)=X^7-9X^6+28X^5-48X^4+49X^3-27X^2+8X-1`.

The example is **not real-rooted** and **not a Bell–Skandera counterexample**. G has exactly three real roots, all positive; the corresponding roots of f are negative. The other four roots are nonreal. This example addresses only the weak relaxation specified above.

## Exact certificates

1. Every coefficient is a positive integer and f(0)=1. The algebraic norm, the product of all seven conjugates of a root of G, is 1. The elementary Maclaurin lower bounds `c_k >= binom(7,k)` hold.

2. The six strict Newton cross-multiplication slacks
   `c_k^2 binom(7,k-1)binom(7,k+1)-c_(k-1)c_(k+1)binom(7,k)^2`
   are `329,1568,12740,177135,5733,21`, all positive.

3. The discriminant of G is `93667157 > 1`. Its monic reduction modulo 11 is irreducible: `gcd(G,X^11-X)=1` and `X^(11^7)=X modulo G`. Since 7 is prime, the latter identity forces irreducible factor degrees to divide 7; the gcd condition excludes degree one. Thus the degree-seven reduction, and hence G over Q, is irreducible.

4. Newton sums give `p_0=7,p_1=9,p_2=25`. For every pair of integers `(a,b)!=(0,0)`,

   `Tr((a lambda+b)^2)=25a^2+18ab+7b^2=((7b+9a)^2+94a^2)/7 >= 7`.

   If a is nonzero, this is at least `94/7>7`; if a=0, b is nonzero and it is `7b^2>=7`. This is an argument for all integer pairs, not a finite search. Irreducibility implies that every nonzero affine polynomial in lambda has a nonzero integral norm. For a putative totally real root, applying AM–GM to the seven nonzero squared conjugates and using only the norm's integrality gives the uniform bound 7. Here the conjugates are not all real; the polynomial trace still satisfies this weak arithmetic test.

5. The stronger AM–GM condition retaining the actual norm magnitude is
   `Tr((a lambda+b)^2)^7 >= 7^7 * |Norm(a lambda+b)|^2`
   when the conjugates are all real. This candidate fails it already at `(a,b)=(1,-3)`:

   `Tr((lambda-3)^2)=25-6*9+9*7=34`,
   `Norm(lambda-3)=-G(3)=355`, and

   `34^7=52,523,350,144 < 103,787,006,575=7^7*355^2`.

   Thus keeping the actual affine norm magnitude excludes the candidate. The observation does not obstruct the full affine norm constraints or the complete arithmetic approach.

6. The fourth Kruskal–Katona lower-shadow inequality fails. The unique fourth binomial expansion is

   `49=binom(7,4)+binom(5,3)+binom(3,2)+binom(1,1)`,

   with decreasing upper indices. Its lower shadow is
   `binom(7,3)+binom(5,2)+binom(3,1)+binom(1,0)=35+10+3+1=49>48=c_3`.

7. Newton sums through degree four are `7,9,25,117,589`. The first 3x3 Hermite moment determinant is `-3432`; therefore the stronger moment-positivity test also excludes the candidate. Discriminant positivity alone cannot stand in for the real-root moment constraints.

The companion verifier checks the finite-field, determinant, Sturm, Newton, binomial-shadow and stronger-norm certificates using exact integer and rational arithmetic. Its coefficient identity verifies the algebra in the quantified weak-bound proof; the case split above supplies the argument for every integer pair.

## End of the stage

This modest auxiliary observation limits only the explicitly weakened scalar tests that discard norm magnitudes. It provides no complete main-conjecture result or all-degree structural inequality. The stronger actual-norm constraint already removes this candidate. Neither all affine resultant constraints nor arithmetic approaches in general are ruled out.

The original irreducible totally positive algebraic-integer and trace-bound reduction is prior work discussed in Bell–Skandera, as recorded in the dated source audit. The present attack stage is ended without expanding non-exhaustive searches. The main Bell–Skandera question remains unresolved here; no major-result or priority claim is made.

`CURRENT_SOURCE_AUDIT.md` is the original dated source-preparation record, not a new publication-time literature audit. Third-party PDFs are research sources and are excluded from the public package. The private original hashes, the revision diff, the independent review and the fresh exact-verifier record are retained separately.
