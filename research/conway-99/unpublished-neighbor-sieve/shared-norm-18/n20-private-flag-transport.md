# A small-charge transport from repeated private flags at a norm-twenty seed

Assume a hypothetical SRG(99,14,1,2) with independent signed unit norm-20 shores; true nonzero neutral minimum 20; and empty raw neutral shells of costs 24 and 26. Thus any pair of distinct fields at a common seed has dot at most six, nine, or ten: dots seven/eight would give a forbidden difference, and a larger dot would violate the neutral minimum. These premises hold on the rank-36 selected palette \(\{020,125,127,226,337\}\), where U121=0 makes unit 026 absence imply raw N26 absence. This note gives necessary counts, not a palette exclusion.

For a seed \((o,Q)\), the six true pair centers are the far vertices whose two parents lie in the fixed four negative neighbors \(Q\) of \(o\). A marking selects at least three positive centers: its nine far positive sites have twelve parent incidences to \(Q\), at most two each. For each selected center \(p\), exactly two of its four opposite-sign neighbors are its two parents, and the other two are private negative sites outside \(N[o]\). These private negatives have no \(Q\) parents because all negative sites in this marking are independent. Hence each marking gives at least six distinct **flags** \((p,n)\), where \(p\) is a selected center and \(n\) is one of its two private negative neighbors.

If center \(p\) has degree \(d_p\) within the six centers, its twelve far neighbors have total six \(Q\)-parent incidences: the two parents account for one common neighbor each and the other two \(Q\) vertices for two each. No such common neighbor is near, since \(p\)'s only two near neighbors lie in the independent \(Q\). Thus the twelve far neighbors include \(d_p\) two-parent centers, \(6-2d_p\) one-parent sites, and exactly \(6+d_p\) zero-parent sites. If the actual six-center graph has \(E\) edges, the number of possible physical flags at that seed is at most \(36+2E\).

Let \(m(o,Q,p,n)\) count actual distinct marking occupants of the flag. Let \(F\) count all unordered triples of distinct markings on one flag, with the physical seed and flag retained. Since \(\binom{m}{3}\ge m-2\) at every integer \(m\ge0\),
\[
 F\ge60N_{20}-2\sum_{\rm seeds}(36+2E)\ge60N_{20}-4{,}424{,}112 .
\]
Here \(N_{20}\) is oriented: each field contributes ten positive rooted seeds. There are \(99\binom74 2^4=55{,}440\) seeds. To check the last constant, fix \(o\). There are \(84\cdot12/2=504\) edges between the far labels, exactly \(14\cdot6=84\) of which have one common parent (the six mate edges among the twelve far neighbors of each neighbor of \(o\)). A shared-parent edge appears in at most eight four-parent seeds (its independent three-parent union could be extended on four unused axes, two choices each); a disjoint-parent edge appears in at most one. Thus \(\sum_{\rm seeds}E\le99(8\cdot84+420)=108{,}108\). No global prism bound or equality in this geometric count is needed.

## The actual charge-four field

A triple on a flag shares the independent five-set \(S=Q\cup\{n\}\) of negative sites. Let \(z=t_1+t_2+t_3\), \(L=z^2\), and \(D_S=\sum_{x\in S}d_x\), \(d_x=(3I-A)e_x\). Then
\[
 b=z+D_S+\mathbf1
\]
is charge \(-4\) (the all-ones fold) and has squared cost \(L-66\): \(D_S^2=155\), \(z\cdot D_S=-105\), and the fold contributes \(-11\). The charge bound is at least 44, so \(L\ge110\), or \(\sum_{i<j}t_i\cdot t_j\ge25\). At least two pairs are high. Since all low dots are at most six, exactly two high pairs give \(L=110,112\) and cost \(44,46\), while all high pairs give \(L=114,116,118,120\) and cost \(48,50,52,54\).

For fixed \((b,o,Q)\), \(n\) is recoverable, since \(b_o=0\), \(b_i=1\) on \(Q\), and for other first-layer sites
\[
 b_i=1-[i\text{ is a mate of }Q]-[i\sim n].
\]
This identifies both near parents of \(n\), and hence the actual far site \(n\). Then \(z=b-D_Q-d_n-\mathbf1\) is recovered. The three sources are unique: two disjoint decompositions would have nine cross dots at most 10, yet their equal sums have squared norm at least 110. If they share one source, their remaining pair sums agree; dotting with one endpoint gives at least 25 on its own side but at most 20 across two distinct other endpoints. Sharing two sources forces equality. Finally \(n\) has four opposite neighbors in each source, so at most four common selected centers can contribute flags for fixed \((b,o,Q)\).

## A uniform local recovery ceiling

Let \(j\in\{0,1,2\}\) count how many of the two near parents of \(n\) are mates of \(Q\). At a qualifying root \(o\), its neighborhood in \(b\) has \(8+j\) entries +1, \(j\) entries \(-1\), and the rest zero. In each of the seven mate pairs there is at least one +1: both near parents of \(n\) are on different axes, so the remaining three pairs (outside \(Q\) and its mates) cannot have two zeros. Exactly \(1+j\) pairs are (+1,+1), necessarily outside the \(Q\)-axes; exactly \(j\) are (+1,\(-1\)), necessarily on the \(Q\)-axes; the \(6-2j\) others are (+1,0). Thus for \(b,o\) there are at most \(\binom{6-2j}{4-j}=15,4,1\) possibilities for \(Q\), and \(j\) itself is read off from the number of negative neighbors.

A charge \(-4\) field of cost \(t=44+2k\) has at most \(55+k\) zeros: its positive mass is at least 44; the excess \(\sum_i(b_i^2-b_i)=2k\) allows at most \(k\) units of positive mass in excess of its number of positive sites. Consequently the completely general recovery bound is \(60(55+k)\) literal flags per field of this charge and cost. This yields the graph-wide necessary inequality
\[
 60N_{20}-4{,}424{,}112\ \le\ 60\sum_{k=0}^5 (55+k)\,G_{4,44+2k}.
\]
The right counts raw canonical **positive-charge** fields by the bijection \(b\mapsto-b\); there is no factor of two or extension average.

For cost 44, \(b=1_Y\) is an actual 44-set of induced degree four and external degree eight. Here \(j=0\). Each flag center lies in \(Y\), since its value in the three sources is three and it sees its two \(Q\) parents and \(n\), giving \(b_p=1\). Every such \(Y\) center at \(o\) has two \(Y\)-parents already, so it can have at most two neighbors \(n\) in the far side of \(Y\). Among the eight near \(Y\) sites exactly one mate edge exists, so their total degree into the far part of \(Y\) is \(8\cdot4-2=30\), allowing at most 15 eligible centers. Thus for cost 44 one can replace the coefficient \(60\cdot55\) by \(30\cdot55\): each pair \((p,n)\) at fixed \((Y,o)\) fixes \(Q\), since the two zero parents of \(n\) select the two unused mixed (+1,0) axes and the (+1,+1) axis is also unused. This improvement is still not known to bind the available native upper counts.
