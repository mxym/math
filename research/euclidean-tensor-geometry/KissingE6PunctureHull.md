# A sharp polar-puncture identity for E₆ and robust kissing bounds in dimension seven

Normalize roots to squared norm 2. For the 72 signed E₆ roots R in six dimensions write P(M)={v : v·r≤1 for every r∈R∖M} and P₀=P(∅).

**Puncture hull theorem.** For every set of at most **three** omitted signed roots,
`P(M)=conv(P₀ ∪ M).`
Three is sharp: some four-root sets have a new vertex outside that hull.

**Packing consequence.** Any seven-dimensional kissing configuration containing at least **70 of 72** points of a fixed E₆ equator has at most **126** points. If exactly **71** are present, the bound is **125**, and attainable. With exactly 69 retained and no two of the three omissions opposite, the bound is 127. These concern arbitrary continuous configurations, not just antipodal codes or a finite point grid.

[Novgorodtsev, Theorem 3](https://www.preprints.org/manuscript/202610.0335), handles the *full* E₆ equator and classifies its 126-point extensions. The puncture argument does not determine the unrestricted seven-dimensional kissing number.

## 1. Exact chamber certificate for the hull identity

Fold v into a dominant E₆ chamber and write yᵢ=v·αᵢ≥0. The simple-root graph has chain 0–1–2–3–4 with an additional edge 2–5. Write G for its Cartan matrix. A positive root with simple-root coefficient vector c has v-inner-product c·y. The set C of actually violated signed roots is an upper ideal in the coefficientwise order on positive roots. For each possible ideal C of size at most four we take the closed chamber cell with c·y≥1 on C and c·y≤1 off C. Imposing only minimal members of C and maximal members of its complement suffices. All these cells are bounded: each coordinate is nonnegative and appears with positive coefficient in at least one retained upper inequality.

The [integer verifier](verify-kissing-e6-puncture-hull.js) generates every positive root by simple reflections and every ideal by adjoining maximal elements of its complement. It solves all six-constraint bases of each cell by exact determinants, and tests every vertex. Write B for the subset strictly violated at a vertex, which can be smaller than C on a boundary. At sizes 0, 1, 2, 3 there is respectively one ideal and seven vertex incidences each. Every vertex either belongs to P₀ or equals the arithmetic mean of the roots of B. In coordinates the latter test is |B|y=Σ_{r∈B}Gr. The maximum squared norm in P₀ is 4/3 (compute yᵀG⁻¹y on the first cell). By Weyl symmetry the same description applies in every chamber. For any point of P(M) its actual violation set is contained in M, and its whole closed cell has no violations outside that set. Convexity proves the inclusion in conv(P₀∪M); the reverse is immediate from inner products of distinct roots.

At size four there are two chamber ideals, each with seven vertices. Each has one exception, of squared norm 11/6, with inner product 3/2 against each of the four omitted roots. Writing q for this point, q·v≤√((11/6)(4/3)) for all v∈P₀. Both this bound and 3/2 are strictly less than q·q=11/6, so q itself separates from the claimed hull. This proves sharpness.

## 2. Lifting a punctured polar to one hemisphere

An outsider x=(v,z) not among the original roots satisfies v∈P(M), ‖v‖²+z²=2. For |M|≤3 the hull theorem gives ‖v‖²≤2, with equality only at an omitted root, by strict convexity. Actual outsiders therefore have z≠0. On one hemisphere use the nonnegative height h(v)=√(2−‖v‖²). Under a convex combination, h is at least the combination of the heights. It follows by expanding the two convex combinations and using nonnegative heights that the minimum same-side lifted dot product is bounded below by the minimum for generator pairs in P₀∪M.

Two generators in P₀ have height at least 1/√2, so their same-side angular distance is at most 120° and their lifted dot is at least −1. A generator in P₀ has dot ≥−1 with every signed root by central symmetry. Two nonopposite root generators have dot ≥−1. Hence if M contains no opposite pair, each individual hemisphere of actual outsiders is projectively compatible: their pairwise dots belong to [−1,1].

**Apex isolation lemma.** Suppose M={r,−r}. An outsider violating r, i.e. v·r>1, belongs to P({r})=conv(P₀∪{r}). Write v=t r+(1−t)w, where w·r=1 and w∈P₀: extend the segment from r to its P₀ endpoint to the cutting plane. The intersection point still satisfies every other root inequality and satisfies r·w=1. Then t=v·r−1. In fact only the bound ‖w‖²≤3/2 is needed. It gives
`‖v‖²≤3/2−t+3t²/2,` and `z²≥(1−t)(1/2+3t/2).`
If x is low (|z|<1/√2), then t>2/3. Since ‖w−r‖²=‖w‖², this also gives ‖v−r‖²≤z²/3. A high member (v′,z′) of the same violating group and hemisphere would then have
`v·v′+zz′ ≥ r·v′ − ‖v−r‖√(3/2) + |z|/√2 > 1.`
Another low member would instead give even horizontal dot >5/3−1/√3>1, since r·v′>5/3 and ‖v−r‖<1/√6. Thus any violating low is its group's only member on that side.

Members violating neither ±r are projectively compatible with both groups; each group is internally compatible, by the preceding no-opposites calculation for a single omission. Two high members are always compatible on the same side. Projective conflicts must therefore join opposite groups and touch a low. If there are lows in only one group it is a singleton; if both groups have lows both are singletons. Removing at most one outsider per hemisphere leaves a projectively compatible set.

## 3. Count and the single-hole sharp example

[Anstreicher's theorem](https://optimization-online.org/2001/01/248/) gives at most 63 projective kissing lines in dimension seven, with equality only for E₇. For m nonopposite omissions use the 36−m paired equatorial axes and all q outsider lines in one hemisphere. If m>0 they cannot attain 63: reflection closure of the paired axes restores every missing axis, whereas none is in this collection of lines. In detail every root x has ten decompositions x=y+z, with y·z=−1 and all twenty y,z on different axes. At most two other lost axes cannot spoil all ten. The E₇ equality case would contain y,z and hence their reflected root x. Thus q≤63−(36−m)−1. Adding both hemispheres and the 72−m retained roots yields 124+m for m≥1, and 126 for the full equator. In the opposite-pair case use the 35 paired axes; the projective subset on each side has at most 62−35=27 lines, and one more outsider is possible. So the total is at most 70+2·28=126. Deleting one equatorial E₆ root from E₇ realizes 125 when exactly 71 are present.

## 4. Related A₅ consequence and precise limitation

In dimension six, containing **29/30** roots of a fixed A₅ equator likewise implies at most **71** points; deleting one from a standard E₆ containing A₅ attains this. Containing exactly **28/30** implies at most **72** when the two omitted roots have nonpositive inner product. This argument makes no assertion for the two-hole A₅ case of positive inner product.

Indeed A₅ consists of eᵢ−eⱼ on the sum-zero subspace of six coordinates. Vertices of its punctured polar have integral coordinate differences: at a vertex the graph of tight differences vᵢ−vⱼ=1 is connected, otherwise a nonzero componentwise shift preserving the total sum is possible. Every ordered coordinate difference is ≤2 because with only two missing inequalities there is a retained two-edge directed path for each ordered pair. A vertex of range ≤1 is in the intact polar. At range 2 every extremal high-to-low ordered pair must be omitted; if the omitted arrows do not share a head or a tail, this forces a unique maximum and minimum and all other coordinates are at the middle level, giving exactly a root. The hull identity therefore holds in these cases. The unpunctured squared radius is 3/2, since its vertices have two levels separated by 1, with squared norm k(6−k)/6. The hemisphere and isolation proof now applies unchanged; the extremal projective code is E₆ with 36 lines, and the paired A₅ roots restore missing roots via an intermediate coordinate. When two omitted arrows share a head or tail, one obtains instead a centered three-level feasible point with levels (1,−1,−1,0,0,0) before centering, or its negative; its squared norm 17/6 exceeds 2. The convexification used here genuinely fails.
