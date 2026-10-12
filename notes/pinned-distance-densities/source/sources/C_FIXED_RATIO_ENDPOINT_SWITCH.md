# Fixed-ratio nested train tracks: a different critical index and an endpoint switch

Date: 8 October 2026. Status: new proof candidate; collective independent review remains deferred. This note does not modify the earlier superlacunary candidates.

## 1. Concrete family and principal conclusions

Fix rational 1<alpha<2 and define

    a=(alpha-1)/2,    b=alpha/2,    c=1-b.

Choose a positive integer K, and an initial admissible length L_1 sufficiently large. For every later stage set

    L_j=K n_{j-1},    n_j=(K+1)n_{j-1},    j>=2.     (1.1)

The integer conditions on aL_j,bL_j,L_j/2 are ensured by taking L_1 a multiple of their common denominator. At each stage use the same actual digit sets:

    horizontal free positions: [1,aL_j] union (L_j/2,L_j],
    vertical free positions: [1,bL_j].

All remaining digits are zero and all free bits are fair and independent. Restrict to the same fixed bottom and top coding cylinders, producing E_-,E_+ and lambda,mu. Pins may range over the whole bottom rectangle P_-; the source is in the top rectangle P_+, with fixed vertical separation v_0>0. Let nu_p=(D_p)_*mu denote the original cross-distance law.

The positive results do not need superlacunarity:

**A. Interval stability.** If aK>1, then every nu_p has a positive sublaw obtained by a fixed horizontal-band deletion, with bounded jointly continuous density. Every actual distance set D_p(E_+) contains an interval of a uniformly positive length.

**B. Exact open integrability range.** Assume for simplicity aK>2, and put

    D_K=K(3/2-alpha)+1-alpha.

If D_K>0, define

    q_K = c(K+1)/D_K.                               (1.2)

Then all pins in P_- have original distance densities uniformly in L^q for every 1<=q<q_K. Every original pin p in E_- fails L^{q_K}, and consequently fails every higher L^q. Thus the critical index is **not attained**.

**C. Bounded regime.** Under aK>2, if D_K<0, the original density is jointly continuous and bounded, uniformly over p in P_-. If D_K=0, the proof gives every finite L^q, uniformly for each fixed q; whether the original density is bounded at this boundary is left open.

The phase transition between B and C is

    alpha=3/2-1/[2(K+1)].                            (1.3)

This differs from the superlacunary family's alpha=3/2 bounded-density threshold. More importantly, its finite critical endpoint fails, whereas the superlacunary critical endpoint is attained.

These conclusions concern these explicitly placed source and pin sets. They are not claims from Hausdorff and packing dimension alone.

## 2. The geometry, regularity, and exact packing dimension

The free-position counts at each intermediate depth are exactly those in the full-phase note. Their sum is at least alpha times the depth and equals alpha n_j at every stage endpoint. Thus lambda and mu are alpha-Frostman and their supports have Hausdorff dimension alpha. Every coordinate support has Lebesgue measure zero because its endpoint cover has total length at most C2^{-(1-b)n_j}. The horizontal marginal satisfies an (alpha-1)-Frostman interval bound and is nonatomic.

Here the packing dimension is strictly below two. Its exact value is

    beta_K=(alpha+2aK)/(1+aK).                       (2.1)

To verify this, at relative depth l in a stage beginning at n, the total free count is alpha n+f_X(l)+f_Y(l). The ratio to n+l is piecewise a quotient of affine functions, and is monotone on each of the four intervals determined by aL,L/2,bL,L. At l=0,L/2,L the ratio is alpha. The two possible peaks are

    B_1=(alpha+2aK)/(1+aK),
    B_2=(alpha+(3b-1)K)/(1+bK).

The numerator of B_1-B_2 after clearing denominators is

    a(1-b)K^2 > 0.

Therefore the upper box dimension is B_1=beta_K. Every fixed coding cylinder has the same upper box dimension: the prefix changes the count by a constant, and the later stage depths tend to infinity. Every nonempty relatively open support set contains a coding cylinder. Taking closures in a countable upper-box cover and applying Baire's theorem shows that its packing dimension also equals beta_K.

Thus the family has actual parameters

    dim_H E_-=dim_H E_+=alpha,
    dim_P E_-=dim_P E_+=beta_K<2.

No regular subset with equal Hausdorff and packing dimensions is selected in the proof.

## 3. Replacement estimates used, with their geometric content

Let mu_j fill the binary tails after n_j, and fix a parent square of side h=2^{-n}, n=n_{j-1}. The actual conditional replacement is

    xi_{A,w} x zeta_{B,v},
    A=2^{aL}, B=2^{bL}, w=2^{-L/2}, v=2^{-L}, L=Kn,

where xi is uniform on A horizontal intervals of width w in their respective equal bins, and zeta is uniform on B vertical microintervals of width v. Their key resolving identity is Bw=A.

For clarity, the two elementary estimates imported from the complete proofs in the companion notes are recorded here:

    fixed band epsilon:
    ||masked replacement density - masked parent density||_infinity
       <=(4D_0/h)[1/(v_0 A)+1/(epsilon Bw)];          (3.1)

    band epsilon=h/A:
    ||difference||_infinity
       <=C D_0[1/(h v_0 A)+log(2A)/(h^2 Bw)].        (3.2)

Both are for the same original pin and unnormalized positive laws. Their proof is elementary: a measure equidistributed among N bins integrates a BV test with error at most Var/N. First average the vertical grid against the distance pushforward of one horizontal strip. At fixed output radius r, the roots are X-p_1=+/-sqrt(r^2-(Y-p_2)^2), so r/|X-p_1| is monotone in Y on each branch; the total variation is at most twice its supremum on each of at most two intervals. Then average the horizontal grid after making the vertical coordinate uniform; its reciprocal vertical derivative is uniformly bounded and similarly monotone on two intervals. This gives (3.1).

For (3.2), retain the actual minimum horizontal separation d_i for each strip. At epsilon=h/A, the bin ordering gives

    (1/A)sum_i d_i^{-1}<=C h^{-1}log(2A).

Sum the first BV estimate over strips before using a worst separation. This produces (3.2). Parent masses sum to one, so their weighted sum never introduces a count of cells. These estimates do not assume a Lebesgue coordinate in the infinite limiting law.

## 4. Proof of interval stability under aK>1

For a fixed epsilon>0, sum (3.1) over the parent squares with their original masses. The masked density increment at stage j is bounded by

    C(1+epsilon^{-1})2^{n-aL}
       =C(1+epsilon^{-1})2^{-(aK-1)n}.              (4.1)

Since n=n_1(K+1)^{j-2}, this is summable if aK>1. The initial filled-tail density is bounded. Hence the masked stage densities converge in L-infinity, uniformly over all pins. The fixed cut boundaries are null for the limiting horizontal law, so weak convergence identifies the limit with the actual positive masked source law.

The finite filled-tail densities are jointly continuous in pin and radius: polar coarea integrates a finite rectangle-indicator density over a circle, and a circle has only finitely many intersections with the rectangle boundaries and the fixed band's boundary. Dominated convergence applies for almost every angle. Uniform convergence preserves joint continuity.

The horizontal interval estimate bounds the lost mass by C epsilon^{alpha-1}. Choose one fixed epsilon so that this is at most 1/2. On the compact pin/output domain, the resulting continuous density has mass at least 1/2 in every fiber and has a uniform modulus of continuity. Each fiber therefore is positive on an interval of a common positive length. Its support lies inside the actual compact distance image D_p(E_+). This proves statement A.

The same proof applies to reversed top/bottom cross distances. It gives intervals for every pin in E_- union E_+.

## 5. Upper integrability under fixed growth

Use the auxiliary band epsilon_j=h/A to decompose the original unmasked density increment. Write sigma=1-1/q, with sigma=1 for q=infinity.

**Away from the band.** Equation (3.2) and Bw=A give a global supremum bound

    C(1+L)2^{2n-aL}=C(1+Kn)2^{-(aK-2)n}.           (5.1)

For aK>2, its sum is finite. It also bounds every finite L^q norm up to a fixed support-length constant.

**Inside the band.** The global horizontal band mass is at most

    M_j,M_{j-1}<=C A^{-1}2^{-bn}.                   (5.2)

The band meets only a bounded number of aligned bins of width h/A, and each occupied bin has mass C A^{-1}2^{-bn}. The actual vertical filled-tail densities are at most

    H_j=C2^{(1-b)(n+L)},    H_{j-1}=C2^{(1-b)n}.    (5.3)

The laws are globally products. Vertical coarea and interpolation yield a distance-density bound C M H^sigma in L^q. For the current stage this is at most

    C 2^{[-b-aK+(1-b)(K+1)sigma]n}
      =C 2^{[D_K-c(K+1)/q]n},                     (5.4)

where 1/infinity=0. The previous stage has the additional favorable factor 2^{-c sigma L}.

If D_K>0, (5.4) is summable exactly for q<q_K. If D_K<0, it is summable for q=infinity. If D_K=0, it is summable for every fixed finite q. Combining with (5.1) proves Cauchy convergence in all the asserted L^q spaces. Weak convergence identifies the actual original law. In the L-infinity case, uniform convergence of jointly continuous finite densities gives a jointly continuous raw density. This proves the upper portions of B and C.

A slightly weaker sufficient hypothesis for a particular finite q is available: each conditional away-band output lies in an interval of length O(h), so Minkowski improves (5.1)'s L^q exponent from 2-aK to 2-1/q-aK. Thus the upper conclusion for a finite q also holds when

    aK>2-1/q,    D_K-c(K+1)/q<0.                  (5.5)

In particular, when D_K>0, the whole range q<q_K follows under the weaker strict inequality aK>2-1/q_K. The simpler assumption aK>2 is used in the main statement to keep all three regimes together.

## 6. Failure at the finite critical endpoint

Fix p in E_-. The same true horizontal track containing p_1 has source mass

    m_j=2^{k-bn-aL},

and its distance image is covered by a set U_j with

    |U_j|<=C2^{(b-1)(n+L)-k}->0.                   (6.1)

The covering uses the quadratic horizontal error and the actual vertical microintervals. It is the same geometry as the superlacunary lower bound.

If the original density g_p belonged to finite L^q, Holder's inequality localized to this actual set gives

    int_{U_j} g_p(r)^q dr
       >= m_j^q/|U_j|^{q-1}
       >= c_q 2^{[qD_K-c(K+1)]n}.                  (6.2)

For q>q_K the right side diverges. More importantly, at q=q_K it is bounded below by a fixed strictly positive constant, independent of j. Since |U_j|->0, this contradicts the absolute continuity of the integral of the integrable function g_p^{q_K}. Therefore g_p does **not** belong to L^{q_K}.

This last step is essential: a constant lower bound for the *whole* L^q norm alone would not prove endpoint failure. It is the constant lower bound localized on sets of vanishing Lebesgue measure that proves it.

This establishes the exact range 1<=q<q_K under statement B's hypotheses. It does not settle the L-infinity question when D_K=0.

## 7. Explicit examples and the endpoint contrast

### Same Hausdorff dimension, different original-law L2 behavior

Take alpha=13/10, so a=3/20, b=13/20.

* Fixed ratio K=14 satisfies aK=21/10>2. Then

      D_K=5/2,    q_K=21/10,    beta_K=55/31.

  Every original cross-distance law is in L^2. It is in L^q for every q<21/10 and fails at q=21/10 and above.

* The superlacunary construction at the same alpha has packing dimension two and attained critical index 7/4. Every original pin fails L^2.

Both are concrete deterministic singular-coordinate constructions. This does not prove that packing dimension alone causes the difference; the actual placement and stage schedule are controlled here.

### A finite-ratio L-infinity boundary

Take K=9 and alpha=29/20. Then aK=81/40>2 and D_K=0. The proof supplies every finite L^q but does not decide L-infinity. This is a precise remaining question, not a claimed continuous-density theorem at that boundary.

### Why the endpoint switch is real

For a superlacunary sequence, the leading critical stage exponents cancel but the inherited horizontal mass leaves the summable factor 2^{-n/2}. At a fixed ratio, the critical exponent itself shifts to q_K. This new exponent cancels the entire n-and-L power simultaneously, leaving a positive amount of L^{q_K} mass on the shrinking track images. The endpoint is therefore excluded rather than attained.

## 8. Dependencies and limitations

The companion complete proofs are:

* `round8_pinned_traintrack_repair_20261008/TRAINTRACK_POSITIVE_REPAIR.md`, frozen SHA-256 aa85b4e46f8752754ce187d8413d200763d87639997f73b0782f874eefb79f81.
* `round8_pinned_phase_diagram_20261008/FULL_PHASE_DIAGRAM_AND_INTERVALS.md`, SHA-256 d91c8031c1ab5fecd2980d9048b3f630e2fc925882b9a052f3440a9649ccb0a7.

The only imported analytical lemmas are the two BV quadrature estimates restated with their proof mechanism in Section 3. All fixed-ratio deductions and the endpoint nonmembership argument are proved in this note.

Positive further masks are controlled by domination under a fixed bounded positive good law, with the true retained-mass normalization cost. No arbitrary-mask high-frequency shell decay is claimed. General branching/Frostman data do not imply the rectangular-resolution hypotheses, and these examples do not establish a new unrestricted Falconer threshold. The finite-scale far-track idea is discussed in [Guth-Iosevich-Ou-Wang, Section 1.2](https://arxiv.org/html/1808.09346v1); novelty of the present complete model-specific phase statements remains to be reviewed.
