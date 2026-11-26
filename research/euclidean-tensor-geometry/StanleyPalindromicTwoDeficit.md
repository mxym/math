# Two small deficits suffice on palindromic weighted heavy paths

**Yongxian Zhang.** AI-assisted proof development and internal mathematical checks; no external peer review claimed.

**Theorem.** Suppose the heavy skeleton of a tree at cutoff \(h\) is a path on \(q\ge2\) rooted blocks, with palindromic mass order. All block masses are multiples of \(g\), where \(g>d\ge1\), and all are at least \(\max(h+d+1,2d+1)\). If the ordinary cut polynomial determines the weighted skeleton among its rivals, it also determines all rooted block series through deficit \(d\), up to simultaneous reversal. This holds for the [narrow mass band](StanleyNonpalindromicHeavyPaths.md), or for the [modular block-count family](StanleyModularBlockCountPaths.md). In particular all narrow-band cutoff-two paths on even block orders and minimum block order at least four are reconstructible; no condition on palindrome or equal endpoint decorations is necessary when this lemma is combined with the nonpalindromic case.

## Extraction with two independent deficit variables

At most two designated components will be marked, and each mark has a positive deficit \(k\) or \(l\) bounded by \(d\). Given intact skeleton masses \(u,v\) of marked components, request the high factors \(x_{u-k},x_{v-l}\), with all other designated high factors intact. Read their coefficient as a polynomial in the low variables, setting every other high exponent to zero.

All skeleton roots must belong to a high component: otherwise the entire block at that root would contribute to low components of combined mass at least \(2d+1\), while the observed low mass is \(k+l\le2d\). Every actual intact high-component mass is a multiple of \(g\). The deficits of the marked factors must thus be congruent to \(k,l\) modulo \(g\), respectively, and their minimum nonnegative representatives are exactly \(k,l\). As these already add up to the full low mass, both deficits are as specified and every purported intact factor really is intact. In particular this remains valid if \(k+l\ge g\). The bound \(u,v\ge h+d+1\) keeps marked factors high.

For two marked components with labels \(u,v\) and formal variables \(t,z\), the extracted coefficient is the bidegree \((k,l)\) coefficient of the formally labeled sum of their rooted interval products, summed over allowed placements. If \(u-k=v-l\), then \(u=v\) and \(k=l\), and the actual coefficient must be multiplied by two to label the two indistinguishable marked components. In any other case no multiplication is needed. If a marked mass equals an unmarked mass (before dividing off its deficit), the roles are already distinguished because the high indices have different residues. Coefficients with one deficit zero can be obtained by treating the relevant factor as intact and using the usual labeled multiplicities, but will not be needed in a two-mark comparison below.

## One independent sign per cut mass

Let \(J\) be the set of proper prefix masses, symmetric under \(a\mapsto N-a\), where \(N\) is total mass. For \(a\in J\), let \(P_a,Q_a\) be prefix and suffix products of normalized rooted block series, and \(T\) the whole-path product. All series initially are determined only through degree \(d\) when interpreted as known. The one-mark coefficients give \(P_a+Q_a=2S_a\) and \(T\), with constant terms filled in. The complement equations
\[
P_{N-a}=T/Q_a,\qquad Q_{N-a}=T/P_a
\]
give the known unit
\[
R_a=P_aQ_a=T(P_a+Q_a)/(P_{N-a}+Q_{N-a}).
\]
Write \(D_a=(P_a-Q_a)/2\) and note \(D_{N-a}=T D_a/R_a\).

For two marked components of masses \(a,N-a\), the labeled bivariate expression extracted above is
\[
P_a(t)Q_{N-a}(z)+Q_a(t)P_{N-a}(z)
   =2S_a(t)S_{N-a}(z)-2D_a(t)D_{N-a}(z).
\]
Consequently the product \(D_a(t)D_{N-a}(z)\) is known through degree \(d\) in each variable, coefficients with a zero degree being zero. Multiply by \(R_a(z)/T(z)\) to obtain \(D_a(t)D_a(z)\) there. The outer product of a coefficient vector with itself determines it up to sign in characteristic zero, or determines that it is zero: select any nonzero diagonal entry, take its coefficient square root up to sign, and divide that row by it. Thus, between two rival trees, each \(D_a\) agrees through \(d\) up to a sign, necessarily the same at \(N-a\) when \(D_a\ne0\).

## Three parts synchronize the signs

Assume nonzero \(D\)'s split into two nonempty groups: those with a sign flipped in the rival, and those not flipped. Let \(e\) be the smallest valuation (degree with nonzero coefficient) of any flipped \(D\) and \(f\) that of any unflipped \(D\). Both are positive and at most \(d\). Choose masses \(a,b\) from these groups attaining \(e,f\), reflecting them if needed so both are at most \(N/2\). This does not change their signs or valuations. Because the groups are disjoint and coincide on complement pairs, \(a\ne b\), and \(c=N-a-b>0\) is the mass of the interval between the appropriate pair of cuts. Set
\[
X_{ij}=[t^e z^f]\bigl(D'_i(t)D'_j(z)-D_i(t)D_j(z)\bigr).
\]
Then \(X_{ab}\ne0\). If \(e<f\), the unflipped \(D_b\) has zero coefficient in degree \(e\), so \(X_{ba}=0\); if \(e>f\) the flipped \(D_a\) has zero coefficient in degree \(f\), with the same conclusion. For \(e=f\), \(X_{ba}=X_{ab}\). It follows that \(Y_{ab}:=X_{ab}+X_{ba}\ne0\).

If \(c\notin J\), the cuts for the labeled triple of masses \(a,b,c\) can have \(c\) only in the middle. Marking \(a,b\) gives \(2S_a(t)S_b(z)-2D_a(t)D_b(z)\) as the sum of the two placements. Equality of the extracted coefficient at \((e,f)\) would then give \(X_{ab}=0\).

If \(c\in J\), all permutations of the three labels are allowed: since \(J\) is reflection-invariant, any first and last labels occur as prefix and suffix, and their positive middle mass makes these cuts disjoint. Count all six formal permutations even if numerical masses repeat, with the coefficient convention above. For marks \(i\) and \(j\) and untouched \(k\), if \(k\) is the middle segment we get \(2S_i(t)S_j(z)-2D_i(t)D_j(z)\). For \(i\) in the middle, write \(U_s=(P_s^{-1}+Q_s^{-1})/2\) and \(E_s=(P_s^{-1}-Q_s^{-1})/2=-D_s/R_s\). Its two possible placements give
\[
2T(t)\left[
 S_j(z)\bigl(U_j(t)U_k(t)-E_j(t)E_k(t)\bigr)
 +D_j(z)\bigl(E_j(t)U_k(t)-U_j(t)E_k(t)\bigr)\right].
\]
This is the sum of \(P_j(z)T(t)/(P_j(t)Q_k(t))\) and its reversal. The \(j\)-middle case exchanges \(i,j\) and \(t,z\).

The known series \(T,R_s,U_s\) are unchanged and have constant 1. The terms involving antisymmetric factors from just the same index do not change. Any two distinct antisymmetric factors whose product changes must come from opposite groups, so such a difference starts in total degree \(\ge e+f\). In the expression \(E_j(t)E_k(t)\) it therefore has no degree \(e\) coefficient in \(t\); the corresponding expression in \(z\) has no degree \(f\) coefficient. This remains true even if \(e+f>d\), since only coefficients through \(d\) in each variable were used. In the cross term \(-2T(t)D_j(z)U_j(t)E_k(t)\) only the constants of the unchanged units can contribute at total degree \(e+f\); it gives \(+2X_{kj}\). The symmetric \(j\)-middle contribution is \(+2X_{ik}\). Thus comparison gives
\[
-X_{ij}+X_{kj}+X_{ik}=0
\]
for all ordered choices of marked labels \(i,j\); if \(e=f\) the reversed ordered comparison is just the same one. Adding each equation to its reverse gives \(Y_{ij}=Y_{jk}+Y_{ik}\). Cyclic choices force all three \(Y\)'s to be zero. These computations apply to repeated masses because marks and variables formally label the roles; the factor of two rule deals exactly with equal marked high signatures. This contradicts \(Y_{ab}\ne0\) and rules out a nonconstant sign assignment. A simultaneous negative sign is precisely path reversal. Each rooted block series is then the ratio of its successive oriented prefix products, using \(T\) at the last step.

At cutoff two the first deficit coefficient counts nonroot leaves, which together with the block mass specifies the number of single leaves and two-vertex arms. At general cutoff \(h\) take \(d\ge\sum_{j\le h}j b_j\) to recover the full rooted block by the existing bounded-branch logarithmic derivative argument.

[Independent finite checks](stanley-marked-path-verify.js) are supplementary; the proof does not use them. See also the [separated interval-mass version](StanleySeparatedHeavyPaths.md).
