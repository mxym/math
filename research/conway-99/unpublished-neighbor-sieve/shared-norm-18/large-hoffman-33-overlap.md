# Large intersection with a negative intriguing 33-set

This corollary requires no restriction on the seven-rank, shell palette, symmetry, or presence of short neutral fields. Let G be any SRG(99,14,1,2), C a Hoffman coclique (22 vertices), and T a negative intriguing 33-set, i.e. A1_T=6·1−4·1_T. Then G[T] is a union of simple cycles. Write δ=|C∩T|. If δ≥13, **every cycle of T meets C**. The maximal gap along one of these cycles between successive members of C is ≤7,6,5,3 edges for δ=13,14,15,16 respectively. In particular T\C is a disjoint union of exactly δ paths with maximum lengths at most 6,5,4,2 in vertices. No δ≥17 is possible by independence on the cycles.

The projection inequality in the [33-site cross-Gram note](all-cycles-hit.md) uses only real SRG site marks and the two equitable indicator equations, not seven-integrality. It therefore gives
    X=1_(C∩T)ᵗ(3I−A_T)^{-1}1_(C∩T) ≤ (δ²+4δ+88)/42
unchanged. Let m be the number of sites belonging to a touched cycle, and r=(3−√5)/2. For the δ successive marked-site gaps g_i around the touched cycles, sum g_i=m and each g_i≥2; as before √5 X=δ+2 sum_(h≥1) sum_i r^(g_i+...+g_(i+h−1)). If some cycle is missed then m≤30. For δ=13,14,15 the lower bounds from integer convexity at total maximal length 30 already exceed the upper bound, using only h≤4,2,2 respectively. For δ=16 the gap lengths alone give m≥32. This is the complete all-cycles proof and does not need the sparse-palette length-four or triangle-flip prohibitions.

For the gap maxima, let c be the number of gaps strictly bigger than 2; c>0 since the total length is 33. In traversing the cyclic order of gaps, at least max(δ−hc,0) order-h runs consist entirely of gaps 2. The c exceptional single gaps have sum 33−2(δ−c); their exponential sum is likewise bounded below by integer convexity. These are disjoint contributions (a single gap of length 4/6/etc is not a sequence of 2-gaps). The checker's short rational comparisons exclude c≤2 at δ13 and c≤1 at δ14. The total gap excess above length two is 33−2δ, so the largest gap is at most 2+(33−2δ)−(c−1). At δ15,16 use simply c≥1. The path statement follows because C is independent and every cycle is met.

The companion arithmetic uses only √5<223607/100000 and r>38196/100000. The conclusions at δ≥13 are separate from the rank-42 two-type face, where only 5 and 12 occur.

Run `python3 large-hoffman-33-overlap.py` to replay the few rational comparisons.
