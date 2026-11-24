# High triangles of actual norm-twenty markings

Work in a hypothetical SRG(99,14,1,2). Assume the actual neutral minimum is 20, the neutral shells of norms 24 and 26 are empty, and the actual signed-unit charge-two shells of costs 28 and 30 are empty. The elementary short-slot results imply that all neutral fields of norms 20 and 22 are signed units; their two sign shores are independent, since a same-sign edge gives an actual charge-two switch of cost 28 or 30 respectively. The latter short affine fields are themselves unit: a positive entry at least 2 translates to charge one of cost at most 17, and a negative entry at most -2 translates to charge three of cost at most 33. In the latter equality case the translated pivot is +1, whereas a charge-three field of cost 33 is entirely nonpositive.

Consider three actual norm-20 fields \(t_1,t_2,t_3\) with each paired dot \(a_{ij}\in\{9,10\}\). Each difference has norm 22 or 20 and is unit, so all three fields have consistent signs at every site they share. Let \(C\) be the sites in all three supports with the inherited signs, and let \(P_{ij}\) be the sites common to \(t_i,t_j\) but not \(t_k\). Then \(|P_{ij}|=a_{ij}-|C|\). When the markings share a rooted positive four-parent seed, \(C\) includes that positive root and its four negative parents.

## Pair-only cells

Set \(w=t_i+t_j-t_k\), \(K=\|w\|^2=60+2(a_{ij}-a_{ik}-a_{jk})\), so \(K\in\{38,40,42,44\}\). Its doubled signed sites are precisely \(P_{ij}\). Each sign of \(P_{ij}\) has size at most three. Indeed, by negating \(w\) if needed suppose that four doubled sites are positive; they are independent because they all lie in the same sign shore of \(t_i\). Subtract the sum of their four \(d_x=(3I-A)e_x\). This has charge \(-4\) and cost \(K+4\le48\), but the four chosen entries become \(-1\) and the coordinate sum is +44, hence the cost is at least \(44+2\cdot4=52\), a contradiction. If \(K\le40\), three same-sign doubled sites are likewise impossible: the translated cost at charge \(-3\) is \(K-3\le37\), whereas three wrong-sign unit entries need at least \(33+6=39\).

For \(K=38,40\), every opposite-sign pair of \(P_{ij}\) is adjacent. A nonadjacent pair with doubled values \(+2,-2\) would give a genuine neutral field of norm \(K+42-56=K-14\) by subtracting \(d_x-d_y\), forbidden at 24 or 26. Thus when \(|P_{ij}|=4\), this cell is a genuine \(K_{2,2}\) with two vertices of each sign. All its four triangle caps lie outside the union of the three field supports. A cap in \(t_i\) or \(t_j\) would make a same-sign edge there. A cap in the remaining field alone would make a same-sign edge in one of the differences \(t_i-t_k\), \(t_j-t_k\): whichever sign the cap has, its edge to the opposite-signed corner has disjoint membership across those fields. Consequently every signed site outside this square meets at most one of its four corners, since opposite corners use their two common neighbors inside the square and adjacent corners have their unique cap outside the union.

In particular an all-dot-ten triangle has \(K=40\) for every choice of omitted marking and consequently \(|C|\ge6\).

## Five or six common vertices of one sign

Write \(z=t_1+t_2+t_3\), with \(L=\|z\|^2=114+2s\), where \(s\) is the number of dot-ten pairs. Suppose six common negatives exist, and let \(B\) be six of them. They are independent. Since \(D_B=\sum_{x\in B}d_x\) has squared norm \(21|B|+2|B|^2\) and \(z\cdot D_B=-21|B|\), the folded field
\[
 b=z+D_B+\mathbf 1
\]
has charge \(-3\) and cost \(L-87\le33\) (adding the all-ones vector folds charge six to minus three). The absolute-charge bound forces equality, so all dots are ten and \(b=1_Y\) for a genuine 33-set \(Y\). It has \(B\subset Y\), and \(Y\) has induced degree two by the affine equation. Any other common negative would give \(-2\) in \(b\): it sees no \(B\)-site, as it shares a negative marking shore with all of \(B\). Likewise a pair-only negative gives \(-1\) in \(b\), impossible. Thus \(C^-=B\) and every pair-only site is positive.

For a common positive \(x\), \(b_x=4-d_B(x)\) and \(d_B(x)\le4\). If \(d_B(x)=3\), then \(x\in Y\) and already has three neighbors in \(B\subset Y\), impossible. Thus every common positive sees four \(B\)-sites. Two common positives share precisely two \(B\)-neighbors, since two four-subsets of six intersect in at least two and \(\mu=2\). Their two-point complements in \(B\) are pairwise disjoint. Hence there are at most three common positives; there are at least two because each pair-only cell has at most two positives and size \(10-(6+|C^+|)\). The exact possibilities are \((|C^+|,|C^-|)=(2,6),(3,6)\). Every common positive is itself a root of a shared seed, with its four \(B\)-neighbors as the parents. The sign-reversed statement also holds. In particular no sign appears on seven common sites.

If exactly five common negatives form \(B\), then the same folded \(b=z+D_B+\mathbf1\) instead has charge \(-4\) and cost \(L-66\). Its coordinate sum is +44. Each pair-only negative gives a wrong-sign unit \(-1\) and consumes two units of slack between squared norm and sum. Thus the total number of pair-only negatives over the three disjoint pair-only cells is at most \((L-110)/2=2+s\). In particular an all-dot-ten triangle cannot have common support size six with five of those sites negative: its three pair-only \(K_{2,2}\) cells would supply six wrong-sign sites but only five are allowed. This five-site argument does not imply a 33-set.

In the \((3,6)\) case the three disjoint two-point complements of the common positive neighborhoods partition \(B\). A zero site outside the union of the three field supports meets at most one \(B\)-site, since there its \(b\)-value is \(1-d_B(x)\). Negative sites of the union cannot meet \(B\). Each same-part pair of \(B\) already has both common neighbors among the three common positives. Each cross-part pair has precisely one common positive and needs one further witness. Thus the remaining positive-site witnesses partition the 12 edges of the literal \(K_{2,2,2}\) on \(B\) into edges and triangles. A pair-only positive has two or three \(B\)-contacts, and a singleton positive has one or two, by \(b_x=1+|\{i:t_i(x)=1\}|-d_B(x)\). If there are \(j\) pair-only positives with three contacts, the remaining blocks are \(3-j\) pair-only edges and \(9-2j\) singleton edges; \(j\in\{0,1,2,3\}\). This is only a necessary skeleton.

## Exact recovery from the sum

The high triangle is uniquely determined by its sum \(z\) in the graph. Every source has \(t\cdot z\ge38\). Distinct actual norm-20 fields have dot at most ten by the assumed minimum. For \(m\) candidates satisfying that large dot,
\[
 (38m)^2/\|z\|^2\le\|\textstyle\sum t\|^2\le10m(m+1).
\]
As \(\|z\|^2\le120\), this gives \(m\le4\). If two distinct triples yield \(z\), either they share a source or are disjoint. Sharing two sources makes all three equal; sharing exactly one gives an equality of two pair sums, but taking the dot with one source gives at least 29 on its own side and at most 20 on the other. Disjoint triples would give six candidates, also impossible.

In the six-common-negative case, \((Y,B)\) therefore determines the triangle by \(z=1_Y-D_B-\mathbf1\). Two distinct six-sets \(B,B'\) attached to the same \(Y\) cannot have a source in common. For \(y\in B\setminus B'\), a source in the first triangle has value \(-1\), while the second sum has value \(d_{B'}(y)\ge0\), inconsistent with that same source and pairwise sign coherence in the second triangle. If \(|B\cap B'|=5\), the two sums differ by \(d_x-d_{x'}\) of squared norm at most 56, and each has squared norm 120. Their dot is therefore at least 92, whereas the nine cross dots of their distinct source fields sum to at most 90. Thus the six-sets giving one fixed \(Y\) meet in at most four sites.

This classifies only the stated overlap regimes and gives no upper on the total high-triangle population strong enough to exclude a rank or palette.

## A graph-wide necessary triangle count

At a given seed, join two fields when their dot is 9 or 10. Under the current neutral-shell assumptions, a dot of 7 or 8 would give a forbidden norm-26 or norm-24 difference, and a dot above 10 would violate the norm-20 minimum. Thus nonedges have dot at most six, and there is no independent 5-set by the [near-seed projection](n20-low-five-projection.md). If the seed contains \(m\) oriented fields and \(T\) high triangles, removing one vertex per triangle leaves at least \(m-T\) fields in a triangle-free graph with independence number at most four. By \(R(3,5)=14\), \(T\ge m-13\). Summing over all \(99\binom74\,2^4=55,440\) seeds gives
\[
 \sum_{\text{seeds}}T \ \ge\ 10N_{20}-720,720
\]
for the actual oriented \(N_{20}\), since each field has ten positive roots. A high triangle with fewer than six common negatives can occur at no more than one positive seed: two distinct positive seed roots have at most two common neighbours, so their four-parent sets would need at least six common negative sites. The six-common-negative triangles instead occur at exactly two or three positive seeds as classified above. This is a lower bound on the incidences to be ruled out; no sufficiently strong graph-wide upper is asserted.
