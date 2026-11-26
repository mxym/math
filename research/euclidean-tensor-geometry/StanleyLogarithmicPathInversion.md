# Recover arbitrary rooted grafts along a path by logarithmic cut probes

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review or priority claim.

## Theorem

Take any path on \(n\ge2\) vertices, and graft a rooted tree \(A_i\) at each vertex, identifying its root with that vertex. Every branch off a root has order at most \(h\), but the rooted types, their multiplicities, their orders \(s_i=|A_i|\), and their placements are otherwise arbitrary. Let
\[
g=\gcd(s_1,\ldots,s_n),\qquad
D=\min\{g-1,\min_i(s_i)-h-1\},\qquad
T_h=\sum_{j=1}^{h} j b_j ,
\]
where \(b_j\) counts rooted tree types of order \(j\). If \(D\ge 2T_h-1\), the ordinary chromatic symmetric function of the resulting tree determines it **among all trees**. In particular this applies to any mixture of equally sized rooted grafts of sufficiently large common order, with no restrictions on type independence or marker counts, and also to arbitrary unequal orders satisfying the common-divisor and tail conditions.

More precisely, let \(T\) be the sum of the orders of the distinct rooted branch types actually present in the certified blocks. The proof needs \(D\ge T_h\) for certification and \(D\ge 2T-1\) for inversion. If the sequence of block orders is not palindromic, \(D\ge T_h\) suffices. For equal orders the moment bound can instead be \(D\ge 2T-3\) by subtracting a background log derivative, as described below. All bounds are independent of the length of the core path. These are sufficient conditions, not a characterization.

## Recover the cut-profile queries and certify the path

Use the [heavy-edge top layer](StanleyHeavyEdgeCore.md#1-factorization-by-heavy-components) and [tail identification](StanleyHeavyEdgeCore.md#3-from-a-decorated-core-to-the-full-tree). The heavy edges at cutoff \(h\) are exactly the core edges, since each core block exceeds \(h\) and every attached branch has size at most \(h\). The top high-variable layer gives the multiset of the orders and normalized rooted cut profiles through their respective deficits \(s_i-h-1\), including in any rival. The tail bound identifies the multiset of full rooted blocks. Neither this step nor the following queries require distinct top variables.

Let \(F_i(t)\) be the normalized rooted series of a block. Its constant is 1, and its degree is \(s_i-1\), attained by cutting all of its edges. For a set of core vertices \(C\), let \(F_C=\prod_{i\in C} F_i\), and let \(F_{\rm all}\) denote the known full product. All cuts of the core have positive intact masses \(m_C=\sum_{i\in C}s_i\). For a queried labeled list \((m_1,\ldots,m_k)\) of multiples of \(g\) summing to the total order, choose high indices \(m_i-d_i\) with \(0\le d_i\le D\), each index \(>h\). In any contribution the actual intact mass for such a component is a multiple of \(g\) and cannot be below \(m_i\), since \(d_i<g\). The total mass forces equality and accounts for every root. As in [the labeled extraction](StanleyEqualOrderGraftMarkers.md#extract-the-labeled-series-by-intact-mass), multiply by the factorials of repeated \((m_i,d_i)\) signatures. This recovers the sum of products of the respective \(F_C(t_i)\), over all labeled core cuts with the specified masses, separately through degree \(D\) in every \(t_i\). In particular labels with identical masses may still be distinguished by their slot.

For two-component cuts with designated mass \(m\), the number of first-side occurrences is at most two: one prefix and one suffix, because all weights are positive. Endpoints are handled separately when the mass is zero or total. At two occurrences let \(P,Q\) be the two first-side profiles. Their labeled query is
\[
V(t,u)=P(t)F_{\rm all}(u)/P(u)+Q(t)F_{\rm all}(u)/Q(u).
\]
The two marginals \(S=P+Q\), \(L=F_{\rm all}/P+F_{\rm all}/Q\) give
\[
2V(t,u)-S(t)L(u)
=(P(t)-Q(t))\,\big(F_{\rm all}(u)/P(u)-F_{\rm all}(u)/Q(u)\big).
\]
If the truncated difference \(P-Q\) starts with \(d t^j\), the second factor starts with \(-d u^j\). Hence the \((j,j)\) coefficient determines \(-d^2\), and the \(u^j\) coefficient recovers the whole difference through degree \(D\) up to sign. The same conclusion if the displayed centered query is zero is that the two profiles agree through \(D\). Thus the profiles are recovered as a pair through \(D\). A single occurrence needs only the first marginal.

For each distinct rooted branch type \(\tau\) actually present, let \(p_\tau(t)\) be its attachment factor, of degree \(|\tau|\) and constant 1. The common denominator
\[
\Delta=\prod_{\tau}p_\tau,\qquad \deg\Delta=T
\]
is known. For any component put \(b_C(u)=F_C'(u)/F_C(u)\). It is additive over vertices, and \(\Delta b_C\) has degree at most \(T-1\). Therefore a profile known through \(D\ge T\) determines the complete rational \(b_C\): take its log derivative through degree \(T-1\), multiply by \(\Delta\), and keep the polynomial numerator. The number \(r\) of core vertices in the component is then determined from its mass and the degree of its profile,
\[
r=m-\deg F_C=m-\lim_{u\to\infty}u b_C(u).
\]
This avoids enumerating subsets of blocks.

The constant coefficient of the two-component query supplies the number of first-side occurrences at each mass in **any** rival. Thus the same extraction recovers the core cardinalities of all of its cut sides, with multiplicities. For \(n\ge3\), singleton sides of one-edge cuts count the leaves. The target core has exactly two leaves, so every rival also has a path core. The case \(n=2\) requires no test.

## Read interval moments from at most three components

For any query, set the designated slot to \(t\), all remaining slots to \(u\), and divide the summed product by \(F_{\rm all}(u)\). The result is the sum of the kernels \(F_C(t)/F_C(u)\) over designated occurrences. It is known modulo \(t^{D+1}\) and \(u^{D+1}\); collapsing other axes does not lose a term of \(u\)-degree at most \(D\). On the diagonal \(t=u\) each kernel is 1, and
\[
\left.\partial_t\frac{F_C(t)}{F_C(u)}\right|_{t=u}=b_C(u),\qquad
-\left.\partial_t\partial_u\frac{F_C(t)}{F_C(u)}\right|_{t=u}=b_C(u)^2 .
\]
For a coefficient of degree \(k\) in either derivative, with \(k\le D-1\), each original exponent needed is at most \(k+1\): for the mixed derivative both exponents are at least 1 and sum to \(k+2\). These identities give exact sums of the first moments for \(D\ge T\) and of the second moments for \(D\ge 2T-1\), since their respective denominators are \(\Delta,\Delta^2\) and numerator degree bounds are \(T-1,2T-2\).

For mass \(m\), sum over three-component queries with that first mass and with the two other masses ordered, and divide the tagged occurrence sums by two to forget their order. In a path each strict interior interval of mass \(m\) occurs exactly once as the designated component. A prefix or suffix with \(r\) vertices occurs \(n-r-1\) times, from the arbitrary remaining cut in its complement. By the two-component data each such boundary occurrence has its known individual \(r,b_C\), even if two boundary occurrences have the same mass. Correct their contributions to multiplicity one. This determines the number of intervals at each mass, the sum of their \(b_C\), and, at the second-moment precision, the sum of their \(b_C^2\). The whole interval at total mass is handled using \(F_{\rm all}\) and counted once. No individual interval profile, other than at a prefix/suffix, has to be recovered.

## Polynomial inversion of the physical mass positions

Let \(W_0,\ldots,W_n\) be the cumulative masses along the core with \(W_0=0,W_n=N\), where \(N\) is the total order. Write \(S_i\) for the cumulative sum of \(b_j=F_j'/F_j\), \(M=S_n\), and \(z_i=S_i-M/2\). In a new variable \(v\), define
\[
B(v)=\sum_i v^{W_i},\quad
A(v)=\sum_i z_i v^{W_i},\quad
C(v)=\sum_i z_i^2 v^{W_i}.
\]
Under reversal their polynomials become \(B^*=v^N B(v^{-1})\), \(A^*=-v^N A(v^{-1})\), \(C^*=v^N C(v^{-1})\). The prefix/suffix data give \(B+B^*, A+A^*, C+C^*\), including the known endpoint contributions. Positive interval differences \(W_i-W_j\) for \(i>j\) record exactly the intervals' masses, and \(z_i-z_j=b_{(j,i]}\). Thus the interval counts give
\[
B B^*=\sum_{i,j}v^{N+W_i-W_j}.
\]
The mass-zero coefficient is \(n+1\); negative differences have the same counts as positive. From the sum and product, recover the unordered pair of roots \(\{B,B^*\}\), and choose one orientation of the mass support.

If \(B\ne B^*\), take the known signed first-moment polynomial
\[
E=\sum_{i,j}(z_i-z_j)v^{N+W_i-W_j}=AB^*+BA^* .
\]
The positive differences give \(b_C\) and the negative differences their opposites. Then \(A=(E-B(A+A^*))/(B^*-B)\), so no second moment is needed in this case. If \(B=B^*\), take instead the squared-moment polynomial
\[
G=\sum_{i,j}(z_i-z_j)^2v^{N+W_i-W_j}
=CB^*+BC^*+2AA^*=B(C+C^*)+2AA^*.
\]
Use equal signs on the two difference orientations. Thus \(AA^*\) is known, and the sum gives the unordered pair \(\{A,A^*\}\). These inversions hold over \(\mathbb Q(x_1,\ldots,x_h,u)\) with the rational moment variable \(u\). In either case the ordered support of \(B\) and successive differences of the centered values recover the \(b_i\) up to a common path reversal. Distinct rooted types have distinct \(b_i\) because equality of log derivatives makes their unit normalized series identical, and the rooted cut factorization recovers the type. Attach the resulting sequence of blocks to finish.

For equal orders, divide every \(F_i\) by one fixed block profile \(F_0\) and use these unit ratios throughout. Globally known products and signature queries are changed only by known factors. All \(b_i\) are now \(O(u^{-2})\) at infinity, since equal degrees cancel their \(1/u\) terms. Their common denominator is still \(\Delta\), and square numerators have degree at most \(2T-4\). This yields the stated \(2T-3\) sufficient moment precision. The analogous low-degree scalar specialization in [first-jet path reconstruction](StanleyEqualOrderGraftMarkers.md#a-first-jet-path-theorem-using-cuts-into-at-most-three-components) may be sharper for affine palettes.

## Scope and comparison

The path argument borrows the idea of comparing a prefix polynomial with its reciprocal from [Acharya–Das–Milenkovic–Orlitsky–Pan](https://arxiv.org/abs/1403.2439), but needs both boundary and interval data, and uses rational log derivatives to distinguish all graft types without singleton independence. The earlier [proper \(q\)-caterpillars](https://arxiv.org/abs/2307.02234), [path trunks with two branching vertices](https://arxiv.org/abs/2308.03980), [proper-core distinct-weight criteria](https://arxiv.org/abs/2609.13464), and [uniform graft equivalences](https://arxiv.org/abs/2611.18940) impose different structural hypotheses. This theorem allows arbitrary rooted branch shapes within the chosen bound, and repeated or coincident block orders anywhere. It does not remove the tail and common-divisor hypotheses for unequal orders, or reconstruct arbitrary branching cores.

## Exact corroboration

Run `node verify-stanley-log-path-moments.js` from this directory. The checker tests the three-component multiplicity correction and reciprocal moment identities on 3,276 paths with mass entries from {2,3,7} and signed integer tags, including 156 palindromic supports. These finite checks corroborate the inversion identities; the proof above gives the theorem for all lengths.
