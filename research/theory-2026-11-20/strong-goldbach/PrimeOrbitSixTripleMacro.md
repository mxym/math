# Three macroscopic nonseed labels must all be near-linear in a six-label smooth-center orbit

Fix an odd prime p and finite prime alphabet F. Consider any sequence of even F-smooth centers N→∞ coprime to p where the all-composite forward factor orbit from p has size six. Order its labels, and pass to any convergent subsequence of weights w_x=lim log x/log N with precisely three weights positive. Then **all three positive weights are one**. The three small labels S={p,q,r} and three large labels must have the exact [balanced, common-multiplier parametrization](PrimeOrbitBalancedReturn.md). This excludes both the one-high/two-intermediate and the two-high/one-intermediate patterns, not the three-high parametrization or the four-macro branch. By [the multi-seed theorem](PrimeOrbitMultiSeedMinimal.md), q and r themselves tend to infinity, although this divergence is not needed below.

The orbit is terminal with rank(I−A)=4 by the [smooth six-label theorem](PrimeOrbitSixSmoothTerminal.md) and its prerequisites. At least one label is high (weight 1) by the [opposite extremes](PrimeOrbitSixTerminalExtremeLabels.md); by “intermediate” we mean weight strictly between 0 and 1. All labels here occur in odd composites so are ≤(N−3)/3. Fix a subsequence with mass matrix P=lim(A_ij log x_j/log N), W=diag(w_i). The rows of P are stochastic and its diagonal is zero. The matrix P−W has rank ≤4 by the ranks of (A−I)diag(log x_j/log N). The three small rows have disjoint supports since gcd(N−s,N−s') divides s−s'=N^{o(1)}. Every edge targeting a positive-weight prime has positive limiting mass on a subsequence on which the bounded exponent is fixed, as we assume throughout.

## Two special facts about the small rows

First, the rows at q and r each use at least one positive-weight factor. For example, in its absence N−q=p^a r^b. Then

    a log p+b log r−log N = log(1−q/N) ≠ 0

has absolute value N^(−1+o(1)). Put T=log N/log r→∞. In [Bugeaud, Theorem 1.1 (1.3)](https://arxiv.org/pdf/2209.00275) the marked r-exponent is O(T), all fixed-base coefficients on p and the actual prime factors of N are O(log N); after division by log r the normalized parameter is O(T), giving log absolute value at least −C log(2r) log(2T)=−o(log N). The b=0 case uses the ordinary fixed-base bound (1.2). This is impossible. Interchanging q,r proves the second row assertion.

Second, in all three small rows the p-column has mass zero. Indeed if v_p(N−t) log p ≥ c log N for any small input t along a subsequence with fixed c>0, take the integral pair (N,t). At infinity and at all actual prime divisors of N (a fixed subset of F on a subsequence) choose the coordinate forms. At p choose (X−Y,Y). These places are distinct since p∤N. The product of their absolute values on the pair is at most t·p^(−v_p(N−t))≤N^(−c+o(1)): the N factor at infinity cancels its valuations on F, and all finite factors from t have absolute value ≤1. The pair is primitive because (N,t)=1, height N. The [p-adic Subspace Theorem, Evertse's notes, Theorem 1.1 with r=n=2](https://pub.math.leidenuniv.nl/~evertsejh/dio2011-padicsubspace.pdf) forces finitely many rational ratios, impossible since t/N→0 and t>0. (At t=p the column entry is already zero.)

## One high

Write M for the unique high label, I,J for the two intermediates. [The six-polynomial argument](PrimeOrbitSixOneHighResultants.md) excludes a high with a small parent. Suppose then there is no small-to-M edge. Since q,r each uses an intermediate factor and have disjoint supports, each targets a different one of I,J, and the p row has no macroscopic factor. The nonempty support of P_p lies in {q,r} by the second special fact. At most one small column is therefore available to the other two small rows. At least one of them, call it t, has a singleton row P_t=e_J (relabel I,J if necessary). Thus N−t=v J^e with fixed e≥1, v=N^{o(1)}. For F_J(T)=vT^e−T+t we have N−J | F_J(N), and F_J(s)>0, N^{o(1)}, at each small prime s. As gcd(N−J,N−s)|F_J(s), P_J is disjoint from the three small rows.

Those three rows and P_J span row(P−W): all four are independent by disjointness, and P_J belongs to that row space since e_J=P_t does and the J row of P−W is P_J−w_J e_J. For either remaining macro i=I,M its row (P−W)_i has negative i-coordinate and all other coordinates nonnegative. In a disjoint nonnegative basis this requires that its containing block have support {i} alone. In particular M belongs only to the P_J block (no small source reaches M), so P_J=e_M and N−J=uM with u=N^{o(1)}, u≥3.

Define F_M(T)=v(1−u)^e T^e−T+t. Modulo N−M we have J=N−uM≡(1−u)N and vJ^e=N−t, hence N−M divides F_M(N). At a small prime s≠t, F_M(s)≡t mod s is nonzero; at s=t it equals v(1−u)^e t^e≠0. These absolute evaluations are N^{o(1)}, so P_M is disjoint from every small row. But P_M lies in the four-row span since e_M=P_J does. The only possible block is e_M, contradicting (P_M)_M=0. This excludes the last one-high case.

## Two highs

Let Y be the sole intermediate. At least one high, call it M, has a small parent s: otherwise q and r would both target Y, contrary to disjointness. Thus N−s=uM with u≥3, u=N^{o(1)}, and P_s=e_M. For every small t the positive integer

    u(N−M)−(u−1)(N−t)=s+(u−1)t

is N^{o(1)}, so P_M is disjoint from the three small rows. These four disjoint rows again span row(P−W). Negative macro diagonals force each of the other two macros to have its own singleton among these four rows. Thus three distinct parents among S∪{M} are singleton blocks for the three macros. A macro child R_i of such a parent t (which can be M) satisfies N−t=v_i R_i^{d_i}, v_i=N^{o(1)}, d_i=1/w_i a fixed positive integer. The two high exponents are 1; the intermediate exponent is d≥2.

If a small row has no macro, it must be p. The other two smalls and M then supply all three singleton parents. Every high H is expressible as (aN+c)/b with a,b>0 and nonzero c, where a,b,|c| are N^{o(1)}: M and any other directly small-parented high have this form from a single division; if the other high's designated parent is M, one further affine division gives it. No such H divides N−Y: otherwise N−Y=zH with z=N^{o(1)}, so bY+zc=(b−za)N. The left side is strictly positive of order N^(w_Y+o(1)) since b≥1, b,z,|c|=N^{o(1)} and 0<w_Y<1. It is thus smaller than N. Consequently P_Y is supported entirely on the small columns (loops forbidden). It is in the disjoint four-row span since its own e_Y block belongs there, hence P_Y=P_p, the sole block on small columns. Yet gcd(N−Y,N−p)=N^{o(1)}. For a small parent t of Y use F_Y(T)=v_iT^d−T+t as above; F_Y(p)>0. For parent M use F_Y(T)=u v_i T^d−(u−1)T−s, satisfying N−Y|F_Y(N) by uM=N−s; its value at p is nonzero modulo p since s≠p. The same evaluation bound gives the contradiction.

Otherwise all three small rows directly parent distinct macro labels R_i, each with N−s_i=v_i R_i^{d_i} and only small factors in v_i. In fact no macro targets any macro. An intermediate cannot be a second parent of a direct high (two smaller inputs would differ by a positive multiple of that high); a high cannot target the other direct high (the affine substitution below); a high cannot target the intermediate Y because the gcd of its complement with the complement at Y's small parent divides the positive N^{o(1)} expression displayed above for M, valid verbatim for either direct high. Loops are excluded. For the promised affine substitution, a putative N−H_a=z H_b between distinct direct highs and N−s_i=v_i H_i gives

    N[(v_a−1)v_b−z v_a]=−v_b s_a−z v_a s_b,

a negative nonzero subpower integer on the right, impossible.

Eliminate the three macro coordinates of Af=f. The first-return matrix K on S is irreducible with all row sums ≥2 and nullity(I−K)=2. As in the [balanced return lemma](PrimeOrbitBalancedReturn.md), K−I=abᵀ is strictly positive integral rank one with positive integer vectors and gcd(a_i)=1. For W₀=∏_{j=1}³ s_j^{b_j}, the s_i-row identity is now

    s_i W₀^{a_i}=v_i (N−R_i)^{d_i}.

Indeed the d_i occurrences of R_i each contribute the whole small-smooth complementary monomial on first return. Reducing modulo N and using v_i R_i^{d_i}=N−s_i gives W₀^{a_i}≡(−1)^{d_i+1} mod N. Since W₀ is a unit at N and gcd(a_i)=1, W₀²≡1 mod N and W₀>1 implies W₀≥√(N+1). On the other hand W₀^{a_i}=N^{d_i+o(1)}, because all v_i,s_i are subpower and 2N/3≤N−R_i<N. Thus all a_i are bounded; fix them on a subsequence. Ratios of logarithms give a_i/a_j=d_i/d_j, and since the d_i include 1, primitivity forces a_i=d_i for all i. At the intermediate index the s_i-valuation of s_i W₀^d is 1 modulo d; that of v_i(N−Y)^d is 0 modulo d since v_i divides N−s_i and s_i∤N. This is impossible. Hence the two-high case is entirely excluded.

Only three highs remain, exactly the hypothesis of the balanced return theorem.

**Dated comparison.** [Kelanemer's September 2026 revision](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) concerns neighboring terminal exponent matrices; the full text remained inaccessible. The exact rows and weight regimes in this note are conditional restrictions, with no priority assertion or claim to decide the remaining balanced orbit, four-macro case or binary Goldbach.
