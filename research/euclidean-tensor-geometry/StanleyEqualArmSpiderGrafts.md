# Align arbitrary rooted grafts on an equal-arm spider

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

Take a spider core of \(d\ge3\) arms of equal length \(L\ge1\), and identify every vertex with the root of a graft block of common order \(s\). Off-root branches have order at most \(h\). Let \(T_h=\sum_{j\le h}j b_j\), where \(b_j\) counts rooted trees of order \(j\), let \(T\le T_h\) sum the orders of distinct branch types actually present, and put \(D=s-h-1\). Write \(F_v\) for the normalized block profile, \(G_a=\prod_{v\in a} F_v\) for a full arm's profile (excluding the center), and \(K=\mathbb Q(x_1,\ldots,x_h)\).

Suppose \(D\ge\max(T_h,dT)\), and the \(d\) vectors
\[
(1,G_a,G_a^2,\ldots,G_a^{d-2})\quad\text{in }(K[u]/(u^{D+1}))^{d-1}
\]
are linearly independent over \(K\). Then the ordinary chromatic symmetric function determines the whole grafted tree among all trees. It suffices in particular that the \(G_a\) themselves are linearly independent. No center type or designated marker need be known. The profiles and the rank condition are recoverable from the same cut data.

For example, two arbitrary distinct equal-order rooted blocks \(A,B\) can be placed in any order on each arm, provided their total counts \(e_a\) of type \(B\) differ across arms. Indeed \(G_a=F_A^L H^{e_a}\) for \(H=F_B/F_A\). If \(\nu=\operatorname{val}(H-1)\), the binomial Vandermonde separates these profiles under \((d-1)\nu\le D\), implied by the stated bound. The center may be either type.

## Certify the core

The [heavy top layer](StanleyHeavyEdgeCore.md#1-factorization-by-heavy-components) and the tail bound \(D\ge T_h\) certify the multiset of rooted blocks, including in any rival, and their common order. Zero-deficit [labeled mass queries](StanleyEqualOrderGraftMarkers.md#extract-the-labeled-series-by-intact-mass) give the core's cut polynomial with the component masses scaled by \(s\). In particular a rival has \(q=dL+1\) core vertices, \(d\) leaves as counted by singleton sides of one-edge cuts, and every one-edge cut has smaller side at most \(L\). Choose any centroid of its core. Each of its branches has order at most \(q/2\), hence at most \(L\), and the branch orders sum to \(dL\). Each branch contains a different original leaf. There are therefore exactly \(d\) branches, each of order \(L\) and with exactly one original leaf. Each is a path starting at the centroid, proving the same core shape.

## Recover the full-arm multiset, even in the presence of repetitions

Use core vertex counts for the component sizes below, and give their deficit slots independent variables. For \(1\le r<d\), query \(r\) components of size \(L\) and one of size \((d-r)L+1>L\). The large component contains the center, so each \(L\)-component is an entire arm. Give the \(r\) arms the same variable \(u\), put the center component's variable at zero, and divide by \(r!\). This recovers \(e_r(G_1,\ldots,G_d)\) through degree \(D\). For the split separating one entire arm, give that arm variable zero and its complement variable \(u\). Divide by the known product of all block profiles. The result is \(\sum_a 1/G_a=e_{d-1}/e_d\), which recovers \(e_d\) since this unit ratio has nonzero constant \(d\).

The elementary data recover the full multiset of actual \(G_a\), even before assuming any rank condition. Any two distinct candidate profiles have difference of valuation at most \(T\): their ratio's logarithmic derivative shares the denominator of degree \(T\) built from the present branch attachment factors, and its nonzero numerator has degree at most \(T-1\). Candidates are available from the certified finite block multiset. If \(P\) is a profile occurring \(\mu\) times in the target, the coefficient of \(Y^\mu\) in \(\prod_a(Y+P-G_a)\) is the product of the nonzero differences \(P-G_a\); its valuation is at most \((d-\mu)T\). Any rival with strictly more occurrences of \(P\) would give zero at that coefficient, contradicting the equality through \(D\). Applying the same test with the target and rival interchanged, including to any profile missing on one side, proves exact equality of the multisets. One can equivalently search the finite candidate multisets against the recovered elementary data. The center profile is then the total product divided by \(\prod_a G_a\).

## Align all successive leaf tails

Let \(A_{a,\ell}(t)\) be the product on the outermost \(\ell\) vertices of arm \(a\). For \(1\le\ell\le L\) and \(0\le r\le d-2\), query a designated component of size \(\ell\), \(r\) other components of size \(L\), and a center component of size \(q-\ell-rL>L\). The \(L\)-components are entire arms, and the \(\ell\)-component is a leaf tail on one remaining arm: cutting off an interval not reaching its leaf would leave another small component on that same arm, which is not possible among the \(L\)-slots. Give the designated component variable \(t\), the full-arm slots variable \(u\), and the residual slot zero. Divide by \(r!\), also when \(\ell=L\), since the designated slot is labeled separately. The data yield
\[
\sum_a A_{a,\ell}(t)e_r(G_1,\ldots,\widehat G_a,\ldots,G_d).
\]
The identity \(e_r(G\setminus G_a)=\sum_{j=0}^r(-1)^j G_a^j e_{r-j}(G)\) is triangular in \(r\). Thus the data recover \(\sum_a A_{a,\ell}(t)G_a(u)^j\) for \(0\le j\le d-2\), through degree \(D\) in each variable. Independence of the feature vectors lets us solve for the tail series coefficient by coefficient in \(t\), with one series for each arm. Successive tail ratios recover the individual block profiles, which the certified block multiset identifies to order \(D\). Attach them in order from the leaf and use the recovered center.

## Two small-length cases without individual arm independence

For \(L=1\), only certification precision \(D\ge T_h\) is required. The one-edge singleton queries give \(\sum_a F_{\mathrm{leaf},a}\), and subtracting from the sum of all certified block profiles identifies the center. The unordered leaves then finish the tree.

For \(L=2\), keep \(D\ge\max(T_h,dT)\). Allow repeated full-arm profiles; require only that the feature vectors of the **distinct** full-arm profiles be independent, and that the different certified singleton block profiles be linearly independent. The same alignment with \(\ell=1\) separates the sum of leaf profiles within each full-arm group. Singleton independence gives the multiplicities in each group, and for each leaf profile \(F\) in the group \(G\), the inner block is \(G/F\). For example, a spider with two-vertex arms and two block types is covered even if every arm has the same full-arm profile: there is only one feature group in that case.

## Scope and reproducibility

The [exact modular checker](verify-stanley-equal-arm-queries.js) exhausts 38,776 core forests of nine spiders with \(d=3,4,5\) and \(L=1,2,3\), checking 90 elementary, reciprocal, and tail query identities. It tests the combinatorial identities rather than serving as the proof.

[Martin–Morin–Wagner](https://arxiv.org/abs/math/0609339) treat plain spiders, and [Crew](https://arxiv.org/abs/2106.04417) recovers the size of the original branching trunk and its twig lengths. This is instead a statement about a heavy core after removal of arbitrary small branches: the original tree need not itself be a spider. The [uniform graft equivalence](https://arxiv.org/abs/2611.18940) and [Awan's proper-core weight conditions](https://arxiv.org/abs/2609.13464v2) impose different hypotheses. This note does not settle general decorated spiders with feature-dependent long arms, or the full Stanley conjecture. The [path result](StanleyLogarithmicPathInversion.md) does not require feature independence.
