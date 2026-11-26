# Untagged repeated-block caterpillar theorem

**Yongxian Zhang.** AI-assisted proof development and internal mathematical checks; no external peer review claimed.

Source prerequisite: the [root-count lifting proof](StanleyLiftedRootCountDeck.md), before its path-specific ordering step. Under its affine-arm and separation hypotheses, these sections extract the multiset of heavy masses, certify the affine-arm class against arbitrary tree rivals, and reconstruct its joint cut deck, labeling each component by (intact mass, skeleton root count). The path hypothesis is used only in the later ordering step, not in extraction. Below is a replacement ordering step for caterpillar skeletons.

## Statement
Keep those affine-arm and separation hypotheses. Suppose the heavy skeleton is a caterpillar with at least three vertices. Its allowed masses fall into disjoint sets of leaf types and internal types (the same mass may occur many times in one role). Assume each pair (m,r) uniquely determines the vector of multiplicities of allowable masses in any r-element submultiset of the global mass multiset. Then the original tree is determined among all trees by its chromatic symmetric function.

In particular, exactly two masses A ≠ B, one on every skeleton leaf and the other on every non-leaf, suffice: solve a+b=r and Aa+Bb=m. No extra separation between A and B is necessary beyond the prerequisite extraction assumptions. More generally, the condition holds if the mass differences from the smallest mass are distinct powers of an integer radix greater than the total number of skeleton vertices, times a common factor.

## Proof
The lifted deck gives the cut deck with full count vectors of mass types. For a skeleton of size at least three, a partition from a single cut has a singleton side iff the edge is incident to a leaf, and at most one side is a singleton. Read all leaf mass types and counts from these cuts. They are fixed in every rival; because the global count of each leaf type equals its count among these leaf singletons, each rival has exactly the same disjoint type roles.

Filter deck records to those where each component contains an internal type. This exactly filters to cuts confined to the induced internal core: cutting any leaf edge isolates a leaf, whereas keeping all leaf edges ensures every component contains an internal vertex. Thus the retained deck is the cut deck of the internal core, labeling each core vertex by the count vector of the star consisting of itself plus all of its attached skeleton leaves. Each component count vector is the sum of the corresponding vertex labels. This is an equality of weighted decks including multiplicities.

The number of internal vertices in a side is the sum of the internal-type coordinates. The single-cut records with a singleton internal side therefore certify that every rival's internal core is a path, since the genuine core is a path and thus has exactly two leaves when the core has at least three vertices. With one or two internal vertices a connected core is automatically a path.

Choose a radix R greater than the skeleton size q. If there are t mass types, write E(v)=sum_i v_i R^i (indices 0,…,t-1), and C=R^t. For each component of each retained cut, map its label v to C times its internal count plus E(v). This is additive, so it gives exactly the L-polynomial of a composition whose part for each core node is C+E(v) in [C,2C-1]. The [narrow-band composition theorem](StanleyNonpalindromicHeavyPaths.md#mass-order), drawing on [Billera–Thomas–van Willigenburg](https://arxiv.org/abs/math/0405434), determines the ordered composition up to reversal. Read its parts' type labels via radix expansion, then reconstruct the core's own mass and the attached leaves by type. Reattach the already-certified heavy blocks to recover the original tree.

The restriction is disjoint leaf/internal mass types, not individual tagging. No conclusion for non-caterpillar skeletons or overlapping roles.

For two rooted types with the same order, use [rooted-type marker extraction](StanleyCaterpillarRootedTypeMarkers.md) instead. The [verification script](stanley-caterpillar-fibers-verify.js) checks the filtering step on 161 finite skeletons; the proof does not rely on enumeration.
