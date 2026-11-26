# Rooted-type markers for untagged caterpillar heavy cores

**Yongxian Zhang.** AI-assisted proof development and internal mathematical checks; no external peer review claimed.

Use cutoff \(h=2\). Suppose the heavy skeleton has \(q\ge3\) vertices, is a caterpillar, and its blocks have exactly two distinct rooted types \(A,B\), with all skeleton leaves of one of these types and all internal vertices of the other. Their masses need not differ. Write \(s_i\) for the mass of a block of type \(i\) and \(v_i\) for its number of two-vertex arms. Assume all masses are divisible by a common integer \(g_0>2q\), and all exceed \(\max(2q^2,2+2q)\). Then the ordinary chromatic symmetric function reconstructs the whole tree among all trees. When the two masses are equal, neither a distinct-mass assumption nor an affine arm-count assumption is needed.

As in [the top-layer factorization](StanleyHeavyEdgeCore.md#1-factorization-by-heavy-components), the ordinary unsigned cut polynomial recovers all heavy block orders and their high rooted tails, including multiplicities, also in any rival. The first deficit coefficient counts the nonroot leaves, which together with \(s_i-1\) determines the two-vertex arms and single leaves, because all off-skeleton branches have size at most two. It follows that the multiset of the two rooted types is certified even in arbitrary rivals. The minimum order keeps that coefficient above the cutoff.

## Extract both type counts

Specialize \(x_2=0\). With formal variable \(y=x_1t\) for a marked singleton deficit, a single leaf contributes \(A_0(y)=1+y\) and an arm contributes \(B_0(y)=1+y+y^2\). The rooted series of a type-\(i\) block is the unit
\[
F_i(y)=A_0(y)^{s_i-1-2v_i}B_0(y)^{v_i}.
\]
Fix an intact component of mass \(m\). Its feasible type counts \((a,b)\) satisfy \(s_A a+s_B b=m\), \(a,b\ge0\), \(a+b\le q\). Put \(g=\gcd(s_A,s_B)\), and pick one feasible pair \((a_*,b_*)\) with smallest \(a_*\). All others have
\[
(a,b)=(a_*,b_*)+j(s_B/g,-s_A/g),\qquad j=0,\ldots,q
\]
with infeasible indices simply omitted. Its rooted series is \(F_A^{a_*}F_B^{b_*}H^j\) with \(H=F_A^{s_B/g}/F_B^{s_A/g}\). This \(H\) is \(A_0^uB_0^v\) for some integers \(u,v\), not both zero: if \(v=0\), then \(u=(s_A-s_B)/g\); if also \(u=0\), equal masses force \(v_A=v_B\), contrary to distinct types. If \(u+v\ne0\), \(H-1\) has valuation 1. Otherwise \(v\ne0\) and \(H=(B_0/A_0)^v\) gives valuation 2. This includes \(s_A=s_B\) with different arm counts.

For every prescribed mass list \((m_i)\), label its entries. Request high factors \(x_{m_i-k_i}\) with \(0\le k_i\le2q\) and the singleton factor \(x_1^{\sum k_i}\) in \(U|_{x_2=0}\). There are at most \(q\) high pieces in the requested lists; the total low mass is at most \(2q^2\), so all roots of any contributing tree are in high components (a low root forces its whole block into low components). All actual intact masses are multiples of \(g_0\). An actual intact mass for a requested index \(m_i-k_i\) cannot be smaller than \(m_i\) because the gap would be at least \(g_0>k_i\); equality on total mass then forces every association. The intended high factors are indeed high. Multiply the coefficient by the factorial multiplicity for each identical high signature \((m_i,k_i)\) to recover all label assignments, including when \(k_i=0\).

Thus for this mass list the data give the labeled cut sum of \(\prod_i F_A(y_i)^{a_i}F_B(y_i)^{b_i}\) through degree \(2q\) in each variable \(y_i\), prior to recognizing the skeleton's shape. Divide out the known anchor units and substitute \(z_i=H(y_i)-1\). The result is the substitution in a polynomial \(\sum_{\text{cuts, labels}}\prod_i (1+z_i)^{j_i}\) of degree at most \(q\) in each variable. The substitution is injective at the given precision because distinct powers \(z_i^j\) have different leading orders at most \(2q\); invert triangularly, entry by entry. Reexpand in the powers of \(1+z_i\) and forget labels by the appropriate multiplicity. This recovers the entire cut deck labeled by the counts of \(A,B\).

## Collapse the leaves and order the decorated core

A skeleton one-edge split with a singleton side identifies a leaf and its type. Its occurrences certify that these roles are disjoint in every rival. Filter the full labeled cut deck to records with no leaf-only component. Precisely these cuts retain every leaf edge: a cut leaf edge isolates its leaf, while if all those edges survive, every component contains an internal vertex. The resulting deck is the induced internal core with each internal vertex decorated by its attached leaf count, readable additively on components.

The number of internal vertices and all one-edge splits of the core are now known; counting singleton splits certifies that the core is a path even in every rival (cores of size one or two are automatic). Give each component the numerical weight \(C\,(\text{internal count})+\text{leaf count}\), with \(C>q\). Then all individual core weights lie in \([C,2C-1]\) and the [narrow-band composition theorem](StanleyNonpalindromicHeavyPaths.md#mass-order), using [Billera–Thomas–van Willigenburg](https://arxiv.org/abs/math/0405434), orders them up to reversal. Reading the leaf counts restores the entire typed caterpillar skeleton, and reattaching the certified rooted blocks gives the tree. This is still a restricted subtree skeleton theorem, not a resolution of the general Stanley question.
