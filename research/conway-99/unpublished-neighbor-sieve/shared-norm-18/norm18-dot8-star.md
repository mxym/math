# No three norm-18 markings share a star of dot-eight overlaps

For a hypothetical Conway 99 graph, **N16=0 implies N18≤55,666**, where both totals count actual oriented integer eigenvectors. Norm 20 and all charge types remain unrestricted. This improves the previous [71,866 bound without norm 16](exclusion.md#counting-windows).

## A fourth norm-18 marking would have two height-three sites

Let o be a positive root of an oriented norm-18 marking with its four negative neighbors Q. The [support and seed description](../short-shell-moments.md#a-bound-using-only-the-root-and-its-four-negative-neighbors) gives independent nine-element signs; each selected site sees four of the opposite sign. Each pair in Q has a unique second common neighbor besides o, its pair label. A marking's set of positive pair labels contains at least four of the six. Suppose three markings t1,t2,t3 at this seed contain all three labels through a single p∈Q, and all their pairwise dots equal 8. Put Y=Q minus p and let X be those three pair labels.

The three X, like the three Y, are independent. Each x in X touches exactly its own named member of Y, because x already has p and that member as its two common neighbors with o. Thus X∪Y induces three independent edges. Put h=1_X−1_Y and D=3I−A. Its entries sum to zero, h²=6 and hᵗAh=−6; since D²=7D+2J, (Dh)²=168. Each t_i equals h on the six sites, and t_i is a −4 eigenvector, giving (Dh)·t_i=42. Consequently
```
u = Dh − (t1+t2+t3)
u² = 168 + (3·18 + 6·8) − 2·3·42 = 18.
```
This is an actual integer neutral −4 eigenvector because ADh=−4Dh for zero-sum h. At a leg x∈X, (Dh)_x=4 and u_x=1; at y∈Y, u_y=−1. At o, Dh takes value 3 because o sees all Y and no X, while the three t_i sum to 3. Likewise p sees all X and no Y and u_p=0. These distinct zero sites each see at least three u-neighbors of one sign. The [unconditional norm-18 height-three theorem](height-three.md) says there is at most one such site. This contradiction excludes the proposed dot-eight star triple, **without a rank or shell assumption**.

## Counting the same oriented shell

Now assume only N16=0. By the [three-label panel theorem](panel-heights.md#the-three-label-exclusion-and-the-rank-38-contradiction), two seed markings sharing at least three positive labels have dot 8 or 10. Dot 10 gives a norm-16 difference, hence is impossible. Four shared labels are impossible at dot 8: the root, four negative parents and four positive labels already give nine coincident signed sites, while the difference of norm 20 is unit and so cannot have any opposite overlap. Therefore choose arbitrarily any four positive pair labels per marking. They form distinct independent four-subsets of the six labels. For each parent star of three labels, at most two of the chosen four-sets contain that star, by the fourth-marking argument.

For this seed let j and k count edges between labels whose parent pairs meet or are disjoint respectively. At each parent its three labels span at most one edge by the neighborhood matching, and there are three potential opposite-pair edges. The [stdlib verifier](norm18_dot8_star.py) takes all 4⁴·2³=2,048 supercharts, with no graph-label realizability restriction. Each independent four-set contains zero or one parent star. Count the star-free four-sets and, for each star, the smaller of two and its number of independent extensions. This gives an upper bound m on the root multiplicity satisfying 4m+5j+8k≤44 in every case.

There are 99·560 seeds and every oriented marking is counted at nine positive roots. The [literal prism transition count](exclusion.md#counting-windows) gives Σj=8(99·84−6P) and Σk≥99·336+6P, with P the number of induced triangular prisms. Using the established P≤851, we obtain
```
36 N18 ≤ 44·55440−40(99·84−6P)−8(99·336+6P)
       ≤ 2,004,000.
```
Divide by 36 and round down to get the stated 55,666. No common-neighbor label, unoriented support or other charged shell is substituted for the count in this bound.
