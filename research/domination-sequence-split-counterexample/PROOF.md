# A split graph with nonunimodal domination sequences

AI-assisted research draft. A separate [internal audit](REVIEW.md) found no gap. The manuscript has not undergone external peer review or proof-assistant verification. No priority is claimed. The graph is finite, simple, connected, undirected and given deterministically. No random choice of graph and no extrapolation from an asymptotic estimate are needed.

**Target.** For a graph G let d(k) count all subsets of size k whose closed neighborhoods cover G. Its ordinary domination polynomial has these numbers as coefficients. The unnumbered conjecture of Alikhani and Peng (2009 preprint, 2014 publication) asks whether d(k) is always weakly increasing then weakly decreasing. Here we give a fixed graph on which this fails. The same graph works for total domination (every vertex has a selected neighbor, whether or not selected itself) and connected domination (the selected vertices dominate and induce a connected graph). The variant consequences are subordinate to the ordinary result. Nothing here addresses the tree case or minimal graph order.

## 1. The graph and exact conditioning

Set q=2^40, b=q², and work over the field with q elements. Take b affine points (x,y) and b nonvertical lines (s,h), with incidence y=sx+h. Every base position has degree q; two distinct positions on one side have at most one common neighbor, including the same-x or same-slope cases. Give each point two disjoint groups of variable vertices, of sizes 1 and 6; give every line three disjoint groups, of sizes 2, 2 and 3. All groups at all positions are disjoint. Make all 14b variable vertices a single clique. For every point-line incidence and each of the 2·3 choices of one group at each endpoint, add a fresh auxiliary vertex with open neighborhood exactly the union of the two groups. The auxiliaries are independent. There are 6bq auxiliaries and N=14b+6bq vertices in total. This defines a connected split graph with no isolated vertex.

Sample D by independent fair inclusion of *every* vertex. Let S and T be the sets of point groups and line groups respectively missed by D. Write U and V for the base positions containing at least one group in S or in T, respectively, and u=|U|, v=|V|. Let E(S,T) be the number of ordered-by-side pairs of missed groups on incident positions. Each of these pairs labels a distinct auxiliary which must be selected for it to be dominated. Every other auxiliary is dominated by a selected clique vertex irrespective of its own inclusion. The clique is dominated if it is hit at least once. If the whole clique is missed, E=6bq and all auxiliaries must be selected; these together dominate every clique vertex since every variable has an auxiliary neighbor. Thus even for an empty selected clique,

    Pr(D dominates | S,T) = 2^(−E(S,T)).                                  (1)

Define A={S empty} and B={T empty}. On either event, there are multiple selected clique vertices, and every auxiliary has a selected clique neighbor. Thus every sample in A or B is ordinary dominating, total dominating, and connected dominating, regardless of which auxiliaries are selected. Both events have probability

    w = (63/128)^b,

since (1−1/2)(1−1/64)=(1−1/4)²(1−1/8)=63/128. The overlap has mass w²; no disjointness assumption about A and B will be used.

## 2. Incidence estimates

For a set of u>0 positions on either side, let d_j be the incidence counts on opposite positions. We have sum d_j=qu and sum d_j² ≤ qu+u(u−1), by counting ordered pairs of distinct positions. Consequently

    |Γ(U)| ≥ (qu)² / (qu+u(u−1)) ≥ b u/(q+u).                       (2)

This works on either side. Since the opposite side has b=q² positions,

    sum_j (d_j−u/q)² = sum_j d_j²−u² ≤ qu.

For v opposite positions, Cauchy–Schwarz now gives the lower bound on distinct base incidences

    e(U,V) ≥ uv/q−sqrt(quv).                                       (3)

If both supports are nonempty, E(S,T)≥e(U,V), because each such incident pair of positions produces at least one pair of missed groups.

## 3. Bounding all mixed ordinary dominating samples

Put δ=2^(−16). First fix the precise pattern S on one side, with support U of size u>0. A group of size k is missed with probability π=2^(−k). The probability of S is w times the product of π/(1−π) over its missed groups, hence at most w. Conditional on S, miss events for individual opposite groups are independent. If n_j is the number of missed groups adjacent in the auxiliary-pair relation to opposite group j, E is the sum of n_j over missed opposite groups. By (1), summing over all opposite patterns gives

    Pr(D dominates | S) = product_j (1−π_j(1−2^(−n_j)))
                         ≤ (1−1/128)^|Γ(U)|
                         ≤ 2^(−|Γ(U)|/128).                        (4)

Indeed on every opposite position in Γ(U) at least one group (in fact every group there) has n_j≥1; and π_j≥1/64. The last inequality follows from 1−x≤exp(−x)≤2^(−x). The identical bound applies fixing a missed pattern on the other side. A support of size u permits at most 7^u precise missed-group patterns since each position has at most three groups.

Therefore the probability of a dominating sample with 1≤u≤δb, divided by w, is at most

    sum_{1≤u≤δb} binom(b,u) 7^u 2^(−bu/[128(q+u)]).                (5)

The same estimate holds for v. To bound the first part (u≤q) use (2) ≥qu/2. Its sum is at most sum_{u≥1}x^u with x=7b·2^(−q/256)≤2^(−12). This numerical bound follows from b=2^80 and q/256=2^32≥95, since 7<8. Hence this part is at most 1/4095. In the second part (q<u≤δb), (2) gives |Γ|≥b/2, and

    sum_{0≤u≤δb} binom(b,u)7^u
    ≤ δ^(−δb)(1+7δ)^b ≤ 2^(30δb).

Here δ^u≥δ^(δb), and 1+x≤2^(2x) for x≥0 since ln 2≥1/2. Thus the second part is at most 2^(−b/512) since 30δ≤1/512.

For u,v>δb, the ratio of the error to uv/q in (3) is at most 1/(δ sqrt(q))=1/16. In particular E≥uv/(2q)≥δ² q b/2=128b. Summing (1) under the original probability distribution on *all* group patterns costs no entropy factor: the probability on this range is at most 2^(−128b), and w≥2^(−2b).

By the union bound (overlap only helps),

    Pr(D dominates, S and T both nonempty) / w
     ≤ 2(1/4095 + 2^(−b/512)) + 2^(−126b) < 1/100.                (6)

For example both powers of two on the right are smaller than 1/4096. Thus every possible selection of auxiliaries in a mixed configuration, including selections forced to dominate themselves, is accounted for.

## 4. Distinct sizes of the two phases

Write X=|D|. Conditioning on one phase simply conditions each of that side's groups to be nonempty, leaving all other groups and all auxiliaries independent and fair. The expected number from a k-group conditioned nonempty exceeds the unconditioned k/2 by k/[2(2^k−1)]. Thus

    μ_A=E(X|A)=N/2 + (1/2+6/126)b=N/2 + 23b/42;
    μ_B=E(X|B)=N/2 + (2/3+3/14)b=N/2 + 37b/42.

In particular μ_B−μ_A=b/3. In each phase the variance of a group size count is at most its squared maximum. Independence of all groups and the free auxiliaries on each phase gives

    Var(X | A), Var(X | B) (each) ≤ (1²+6²+2²+2²+3²)b+6bq/4
                                 = 54b+3bq/2 ≤ 2bq.                (7)

Let r=b/32. Define three integer windows by intersecting closed real intervals of radius r with the integers, centered at μ_A, (μ_A+μ_B)/2 and μ_B in that order. Call them I_A,I_M,I_B. They are all inside [0,N], since their centers are N/2+O(b) (in fact between N/2 and N/2+b), and are disjoint in the displayed order since b/6>2r. Each contains between 2r−1 and 2r+1 integers.

By Chebyshev (7), the probability conditional on either phase that X lies outside its own window is at most 2048/q<1/100. Now let F be *any* family of subsets containing all samples in A∪B and contained in the family of all dominating sets. Each outer window has probability Pr(D∈F, X∈I)≥99w/100 from its own phase alone. The middle window has probability ≤3w/100: at most w/100 from each phase since it is disjoint from their own windows, and at most w/100 from everything else by (6). No subtraction of w² is necessary.

Let f(k) count members of F of size k; f(k)/2^N=Pr(D∈F,X=k). Averaging over the windows supplies integers k_A<k_M<k_B such that

    f(k_A)/2^N, f(k_B)/2^N ≥ (99w/100)/(2r+1),
    f(k_M)/2^N ≤ (3w/100)/(2r−1).

The upper bound is strictly smaller than the two lower bounds for r≥1. A weakly unimodal sequence cannot have an intermediate term strictly below both endpoint terms. This gives a strict valley for each family separately (the three indices may depend on the family). In particular F may be ordinary dominating, total dominating or connected dominating, by §1. The closed forms of the windows, not the exact individual coefficient values, witness existence of the valley at this fixed finite q. Because connected dominating sets are closed upwards in a connected graph (each added vertex touches the old dominating set), their coefficient sequence has interval support up to N; thus its failure of unimodality also rules out log-concavity.
