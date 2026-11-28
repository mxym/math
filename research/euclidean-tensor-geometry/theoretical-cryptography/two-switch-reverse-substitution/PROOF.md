# Sharp reverse substitution for two-switch pair regions

## 1. Model and hypotheses

A finite access structure Γ on parties P is an upward-closed collection of qualified sets with ∅ not qualified. A party is important if it belongs to a minimal qualified set. A perfect scheme has finite shares and secret S with positive entropy; qualified views determine S, and forbidden views are independent of S. Its convec has coordinates H(X_i)/H(S). Let K(Γ) be the Euclidean closure of these vectors, as in Khazaei §2.2. This is a convex upward-closed set: independent repetitions with separate secrets give rational entropy-weighted averages (or first replace secrets by uniform ones using the usual convec convention), and independent added randomness increases coordinates. For completeness, to approximate any desired weight using two finite schemes, independently repeat the first n times and the second m times; the first weight is n H(S₁)/(n H(S₁)+m H(S₂)), and such weights are dense in [0,1]. To increase one coordinate, append independent noise of the desired entropy (finite alphabets and a continuous one-parameter distribution attain every nonnegative entropy). The same operations permit taking limits. Every important party has contribution at least one: if a forbidden set becomes qualified by adding that party, the conditional mutual information with the secret is one in normalized units. Dummies may be omitted and padded with zero entropy or independent noise.

For p an important party of Γ on R∪{p}, and a nonempty structure Δ on a disjoint Q, the substitution Ω=Γ[p←Δ] declares T∪U, T⊆R, U⊆Q, qualified precisely as follows: evaluate Γ on T∪{p} if U is Δ-qualified, and on T otherwise. Let c=(c_R,c_Q) be a composite convec. Its reverse factor is the supremum of r∈(0,1] such that there exist factor convecs x∈K(Γ), y∈K(Δ) satisfying r x_i≤c_i for i∈R and r x_p y_q≤c_q for q∈Q (Khazaei §3.1, equation (13)). We also use the Shannon relaxation, where the normalized entropy function h is any monotone submodular set function on dealer plus parties, with h(∅)=0, h(S)=1, and increments h(T∪{S})−h(T) equal to zero on qualified T and one on forbidden T. No reverse procedure operating on the code or the same secret alphabet is asserted; this is a statement about existence and domination of normalized contribution vectors.

An unordered pair of important parties {u,v} has a **two-switch witness in order u,v** if there are nested background sets C₀⊊C₁⊊C₂ disjoint from {u,v}, all forbidden, for which the qualification flags with added members of {u,v} are:

    background      neither    only u    only v    both
    C₀                 0          0          0       1
    C₁                 0          1          0       1
    C₂                 0          1          1       1

Some pairs have both orientations. The backgrounds need not be singleton increments and C₀ need not be empty.

A **two-switch pair region** is a closed factor convec region that is exactly
`x_i≥0` for all i, `x_i≥1` for important i, and `x_u+x_v≥3` for the edges {u,v} of a specified graph E on the important parties, each edge admitting at least one two-switch witness. It is not enough that these inequalities are merely valid; they must completely describe the region. The theorem below can either assume this equality for both factors in the model used or, when equality holds for actual closed convecs, deduce it for Shannon convecs as well by the entropy argument in §2. The graph E may be empty.

## 2. Elementary inequalities and the exact factor formula

For either actual normalized entropy or the Shannon relaxation, write h(U) for a party-only value. In addition to standard monotonicity and submodularity we have:

- If A⊂B, A forbidden and B qualified, then h(B)−h(A)≥1. Apply monotonicity to A∪{S}⊂B∪{S}.
- If A and B are qualified but A∩B is forbidden, then h(A)+h(B)−h(A∩B)−h(A∪B)≥1. Apply submodularity to A∪{S}, B∪{S}.

A two-switch witness implies h(uv)≥3. Write A={u,v} and h(A|C)=h(A∪C)−h(C). At each transition C_old→C_new pick the newly qualifying singleton w (first u, then v). Apply the second strong inequality to A∪C_old and {w}∪C_new, whose intersection {w}∪C_old is forbidden. Then use ordinary submodularity to bound h({w}∪C_new)−h({w}∪C_old)≤h(C_new)−h(C_old). The result is h(A|C_old)−h(A|C_new)≥1. At C₂ the first strong inequality gives h(A|C₂)≥1. Finally h(A)≥h(A|C₀) by ordinary submodularity, proving h(uv)≥3. This proves each pair inequality even in the Shannon model. In particular if K(Γ) has the asserted pair description, the Shannon singleton region coincides with K(Γ): every Shannon point satisfies the described inequalities, and actual convec limits are Shannon points. For the latter, extend actual schemes to their normalized entropy functions and take a convergent subsequence; each entry is bounded by the sum of the singleton values on its set.

We use three elementary facts about substitution. Grouping all Q into one share makes an outer scheme with the unchanged contributions on R. Conversely choose an outer forbidden T such that T+p qualifies. Condition on X_T and retain Q to get an inner convec bounded coordinatewise by c_Q. For each important q in Δ, choose a minimal Δ-qualified set D with q∈D, condition on X_(D∖{q}), and discard all other inner shares except q. With q present, the inner test becomes true, and without q it is false. This makes an outer convec whose p-coordinate is at most c_q and whose other coordinates are at most their c_i. These conditioning operations preserve the relative secret entropy: the conditioning coalition is forbidden; any newly forbidden joint view including the conditioning coalition is independent of the secret, and any qualified joint view still determines it. Averaging the conditional convecs over positive-probability views gives normalized conditional entropies bounded by the original coordinates, and stays in the closed convex factor region. In the Shannon model the same argument is contraction h(C∪·)−h(C), followed by restriction. For limiting composite convecs the inequalities persist; one may take convergent subsequences of the extracted vectors on bounded coordinates, including the grouped coordinate bounded by ∑_Q c_q.

For two factors with the pair description, let

    κ = min( {c_q : q important in Δ}
             ∪ {(c_j+c_k)/3 : {j,k} ∈ E_Δ} ).

The minimum is nonempty because Δ is nonempty and does not qualify ∅. It is the largest t such that t y≤c_Q for a factor convec y, since those conditions characterize feasibility of c_Q/t by upward closure and the exact pair description. The extracted inner convec shows κ≥1. Grouping Q shows that every pair inequality on untouched outer coordinates holds for c_R; the unit lower bounds there also hold.

For any c, the following is an exact formula in the closed model:

    ρ(c) = min( {1} ∪ {(c_i+κ)/3 : {p,i} ∈ E_Γ} ).                (1)

In fact an r-witness has r x_p≤κ, so the pair {p,i} forces 3r≤c_i+κ. Conversely for any positive r≤ the right side set x_i=c_i/r on R, x_p=κ/r, y=c_Q/κ. The singleton and untouched pair conditions hold, and those involving p are precisely the displayed bounds. These factor convecs witness domination, including at the endpoint. If p belongs to no pair edge, the factor is one. Moreover the single-party contractions above give

    c_i+c_q ≥3  for all {p,i}∈E_Γ and important inner q.             (2)

Hence inner singleton terms of κ can never force a factor below one. The nontrivial terms of (1) come from two pair edges, one in each factor.

## 3. The two chain telescopes

**Theorem.** On two-switch pair regions, ρ(c)≥8/9 for every single substitution and every composite convec, including the Shannon relaxation. If every edge {p,i} of the outer pair graph has a witness ordered p,i, then ρ(c)=1. These are uniform claims under explicit factor hypotheses, not a claim about arbitrary access structures.

To prove this, choose outer {i,p} and inner {j,k} edges. Relabel the inner pair so that a witness has order j,k. The outer witness may have either order i,p or p,i. Condition on the union of the two C₀ background sets. This is a forbidden composite coalition, so normalization is unchanged and single-share contributions after conditioning are at most the original ones. At the two remaining outer increments use bundle labels A,B; at the inner increments use a,b. All these bundles and i,j,k are disjoint. Regard labels as grouped variables, with h of a label-set equal to the conditioned h of its full union. Therefore ordinary and strong inequalities apply on the label sets.

Only the three prefixes ∅,A,AB of the outer increments and ∅,a,ab of the inner increments are used. For a label-set with these prefixes, let I,J,K be the presence indicators of i,j,k. The replacement bit P available to the outer structure is respectively J AND K, J, or J OR K at inner prefixes ∅,a,ab. Composite qualification at the three outer prefixes is respectively:

    outer prefix        order i,p          order p,i
    empty               I AND P            I AND P
    A                   I                  P
    AB                  I OR P             I OR P

Here the capital K above is the presence bit of k only, not a convec region. The table follows by evaluating the two witness truth tables, so it uses no assumption about non-prefix coalitions.

The following certificates are sums of elementary inequalities, all with coefficient one. In the tables, `S U V` denotes h(U)+h(V)−h(U∩V)−h(U∪V)≥b, and `M U V` denotes h(V)−h(U)≥b. The value b is determined by the qualification rules just stated: for S it is one exactly for two qualified sets with forbidden intersection; for M exactly for forbidden U and qualified V. Juxtaposition denotes union of distinct labels. Every M row has U⊂V.

**Order i,p:**

    type U       V        b
    S    i       jA       0
    S    i       jka      0
    S    i       Aa       0
    S    j       ia       0
    S    ij      k        0
    S    ijk     ijA      1
    S    jkA     jAB      0
    S    ijkA    jkABa    1
    S    jkAB    jABa     1
    S    ija     iAa      1
    M    jka     ijka     1
    M    jAa     ijAa     1
    S    jAa     ABa      0
    S    kABa    ABab     0
    S    ijkABa  kABab    1
    M    ABab    ijkABab  1

**Order p,i:**

    type U       V        b
    S    i       jk       0
    S    i       ja       0
    S    i       kab      0
    S    j       Aa       0
    S    k       jA       0
    S    ijk     jkA      1
    S    ijA     jAB      0
    S    ijkA    ijAa     1
    M    jAB     ijAB     1
    S    ija     jAa      1
    S    kAa     Aab      0
    S    ikAa    kABa     0
    S    ijkAa   ikABa    1
    M    kABa    ijkABa   1
    S    ikab    kAab     1
    M    iAab    ikAab    1
    S    iAab    ABab     0
    M    ABab    iABab    1

For each table the total left side is 3h(i)+h(j)+h(k): expand an S row into its two positive terms minus its union and intersection; expanding the M rows cancels all nonempty non-singletons and leaves a term −5h(∅)=0. The right sides sum to 8 and 9 respectively. Since conditioning cannot increase singleton entropy, these inequalities imply

    3 c_i+c_j+c_k ≥ 8  (outer order i,p), or ≥9 (outer order p,i). (3)

This proof applies to arbitrary bundle sizes. It does not assume that the composite convec is linear or is produced by a forward construction. Equations (1) and (2) and taking the minimum over the inner pair terms now give ρ≥8/9, and give ρ=1 in the stated orientation. The use of a normalized Shannon inequality proof makes the same bound valid for Shannon composite convecs when the factor regions agree, even when the composite lacks an actual scheme.

## 4. All factors on at most four participants; sharpness

By Stinson's [Table 1 and Theorem 5.4](https://www.terpconnect.umd.edu/~abarg/626/Stinson%20Secret%20Sharing%2092.pdf), the four nonideal types on at most four important parties are #5, #8, #12, #13 below. One can remove dummies; a qualified singleton can be separated and given the secret; components whose minimal qualified sets use disjoint party sets can be implemented independently given the same secret. All structures on fewer than four important parties are ideal (threshold, pair-star, or such a disjoint combination), so these reductions leave only the listed nonideal types. An ideal structure has the pair description with no edges: an ideal scheme supplies its all-one vector on important coordinates, and the unit lower bounds and independent padding characterize the whole region. This also covers structures with a qualifying singleton and a nonempty residual structure on at most three parties.

Here are the pair graphs of the four nonideal types. A string denotes a set of party labels. Each ordered witness triple `(u,v; C₁,C₂)` uses C₀ empty; its order is the first two entries.

    type   minimal qualified sets        pair edges             witnesses
    #5     12, 23, 34                    23                     (2,3;1,14), (3,2;4,14)
    #8     12, 23, 24, 34                23, 24                 (2,3;1,14), (2,4;1,13)
    #12    12, 23, 134                   12, 23                 (2,1;3,34), (2,3;1,14)
    #13    12, 23, 24, 134               12, 23, 24             (2,1;3,34), (2,3;1,14), (2,4;1,13)

The displayed chains satisfy the truth table in §1 by testing membership of the listed minimal qualifiers. We verify that the singleton and pair inequalities indeed give the entire region, rather than only a rate bound. A star of pair constraints with all coordinates ≥1 has exactly the upward closure of the segment joining the endpoint vectors with center 2 and all leaves 1, or center 1 and all leaves 2 (other parties 1). To see this, clamp the center to [1,2]; the minimal allowed leaf coordinates at center x are then 3−x, and all nonleaves can be set to one. All four graphs in the table have this form, using either endpoint of 23 as center in #5. The following schemes realize the two endpoints in each case.

Use uniform field secrets over a prime field with at least seven elements. Independent component schemes of the same secret realize the union of their qualified families: forbidden views in every component have the same law for every secret, and the conditional tapes are independent. An ideal star gives its center a mask t and each adjacent leaf the same s−t; each edge can also be shared by a two-term additive split. An ideal triangle uses two-of-three Shamir, and a three-party unanimous coalition uses three-term additive sharing.

- **#5:** use the star with edges 12,23 plus an independent additive split on 34, or the star with edges 23,34 plus the split on 12. This doubles exactly party 3 or 2.
- **#8:** use the ideal triangle on 234 plus an independent split on 12, or the star with center 2 and leaves 1,3,4 plus an independent split on 34. The dimensions are (1,2,1,1) and (1,1,2,2).
- **#12:** the dimensions (1,2,1,1) result from a degree-two Shamir polynomial at four distinct nonzero points: party 2 receives two evaluations, party 4 receives a copy of one of those, and parties 1 and 3 each receive one of the other two. Qualification requires at least three distinct points; this gives exactly 12,23,134. For (2,1,2,1), combine the star with center 2 and leaves 1,3 and an independent three-term share on 134.
- **#13:** the first endpoint (1,2,1,1) uses a degree-two Shamir polynomial at five distinct nonzero points, with party 2 receiving two evaluations and each other party one. The other endpoint (2,1,2,2) combines center-2 star sharing on all three leaves with an independent three-term share on 134.

Every vector in the polyhedron is now attainable in closure by direct-sum interpolation and independent noise. Section 2 gives the matching Shannon necessity; the constructions prove these regions agree in both models. Thus the theorem covers all factor pairs of size at most four. In particular, for inner factors satisfying the theorem, all replacements in #5 give exact reversal, as do replacements at 2 or at any vertex of pair-degree zero in the other three types. Ideal factors also give exact reversal: an ideal outer has no pair edges and (1) is one; an ideal inner has only singleton terms in κ and (2) gives one. No assertion is made that every remaining fixed pair and orientation attains 8/9.

**Sharpness of the uniform factor.** Use the composite from Khazaei Theorem 8.1, equation (48), Appendix B.2. The outer Γ is #12 with replaced party 3; untouched ordering (1,2,4) gives c_R=(3,1,1). The inner structure is a #12 with one extra singleton-qualified anchor. That paper's scalar-linear construction has inner coordinates (2;3,2,3,2), anchor first, over any finite field. Drop the anchor to obtain a perfect scheme for the unanchored substitution, whose two factors each have four parties. Restricting shares deletes the anchor without affecting any of the remaining qualification rules. Here κ=min(2,5/3,5/3)=5/3, and the only outer pair containing 3 is 23. Formula (1) gives exactly (1+5/3)/3=8/9. This also shows sharpness in the Shannon model. The linear construction and its factor at the anchored point are prior work; what is proved here is the uniform lower bound, including over composite convecs unrelated to that example.

## 5. Closure operations and scope

The pair-region hypothesis is not itself a bound on the number of parties. For instance, adding any number of singleton-qualified anchors to a structure with a two-switch pair region just appends unit lower bounds: restrict away the anchors for necessity and assign the secret to them for sufficiency. The original chains avoid the anchors. For the four explicitly realized classes, an alternative extension is to make a fixed set B of new parties jointly mandatory, requiring both the old qualification test and the presence of every party in B. Conditioning on all mandatory shares gives the old region as a lower constraint (that set by itself is forbidden). For sufficiency use independent uniform pads indexed by B, one per new party, and share the secret minus their sum using the old scheme. For uniform field or uniform bit-string schemes, missing any pad gives perfect secrecy; a forbidden old view is also independent of the secret conditional on all the pads. This yields the claimed added unit coordinates for the linear endpoint families above and their closures. Old chains lift by adjoining all of B to every background. Singletons, pair conditions, and the general theorem therefore apply to families with unbounded numbers of parties, e.g. these extensions of the four explicit families.

The theorem is about one replaced party and closed normalized entropy convecs. It is not a bound beyond 1/2 for arbitrary substitutions, not a claim about common finite alphabets for reversing an individual scheme, and not a determination of the depth-uniform simultaneous Csirmaz reverse factor in Khazaei §9.
