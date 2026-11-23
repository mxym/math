# The positive seven-set determines a unit cost-25 charge-one label

> **Provenance:** The injectivity statement is already proved in the [signed-support census](signed-supports.md#seven-positive-and-eighteen-negative-sites). The argument below is an alternative rank-free proof, not an additional classification.

Let \(A\) be a hypothetical \(\mathrm{SRG}(99,14,1,2)\), and let \(b\) be an actual **signed-unit** solution of \(Ab=-4b-2\mathbf1\), \(b^2=25\). Its positive and negative sets have sizes seven and eighteen. Its positive set uniquely determines the field. There is no Seidel-rank, seven-class, or palette assumption. This caps a collision on a *whole seven-set*, not a smaller seed or the full graph-wide population.

Write \(d_i=(3I-A)e_i\). For a charge-\(a\) label, \(b\cdot d_i=7b_i+2a\). If its positive graph has \(e_P\) edges and its negative graph \(k\), summing the cross incidences gives \(k=e_P+3\): a positive site sees \(6+d_P\) negatives, and a negative site sees \(2+d_N\) positives. Positive-pair capacity gives \(18+4k\le42-e_P\) since each negative site with negative degree \(d_N\) witnesses at least \(1+2d_N\) positive pairs. Therefore \(e_P\le2\), \(3\le k\le5\).

The negative graph is a forest. A negative triangle \(S\) gives \(b+\sum_{i\in S}d_i\) of charge four and cost \(25+39+2(-21+6)=34\), below its absolute mass 44. For a \(j\)-set \(S\) of negatives, \(b+\sum_{i\in S}d_i+\mathbf1\) has charge \(j-8\) and cost \(102-11j+2j^2-14e(S)\), by expanding against \(\|\sum_{i\in S}d_i\|^2=21j+2j^2-14e(S)\). A four- or five-cycle makes this cost at most 34 or 27, below absolute mass 44 or 33 respectively. There are at most five edges, so no longer cycle.

Suppose two different unit labels \(b,b'\) share the positive set \(P\). Let \(C\) be their common negatives, and \(X,Y\) the two exclusive negative sets, of equal size \(d=18-|C|\). Their difference is **unit**: there is no opposite-sign overlap because the entire positive set is fixed and is disjoint from every negative. Thus the neutral difference is of squared norm \(2d\). By the [minimum and Fano classification](../short-support-packing/README.md), \(d\ge7\). For \(d=7,8,9\) use the published exterior height restrictions: Fano exterior heights are at most one, [norm-16 heights](shared-norm-18/exclusion.md) are at most two, and [norm-18 heights](shared-norm-18/height-three.md) are at most two except possibly one height-three site. The seven sites of \(P\) are exterior to the difference and so receive at most 7, 14, 15 contacts respectively into a sign side. But each exclusive negative site needs at least two contacts into \(P\), requiring \(2d\); all three cases fail.

For larger \(d\), write \(e\) for the equal number of induced edges in each difference sign, \(Q=\sum_{x\in X\cup Y}\deg_{\rm own}(x)^2\), and \(h_z\) for the common number of contacts into either sign at an exterior site \(z\). Let \(H_j=\#\{z:h_z=j\}\), \(T=\sum_{j\ge3}\binom{j-1}{2}H_j\), \(D=\sum_{j\ge3}(j-2)H_j\), so \(T\ge D\). Counting contacts and positive-pair common neighbors gives
\[
 \sum_z h_z=10d-4e,\qquad
 \sum_z\binom{h_z}{2}=d(d-7)-7e-Q/2,\qquad
 H_0=99-19d+d^2-3e-Q/2-T.
\]
Indeed the full pair capacity on a sign side is \(2\binom d2-e\). Its own support witnesses the same-sign degree-pair term, the opposite support witnesses \(\sum\binom{4+d_{\rm own}}2\), and subtracting them yields the second moment shown. The last relation follows from \(\binom{h-1}2=\binom h2-h+1\), with the exterior zero sites contributing the \(H_0\) correction.

Put \(E=e(X,C)=e(Y,C)=\sum_{z\in C}h_z\). The \((1,25)\) equation on \(X\) gives
\[
 \sum_{p\in P}h_p=2d+2e+E.
\]
The left side is at most \(14+D\), while \(E\ge18-d-H_0\). Substitution gives
\[
 5e+Q/2+T-D\le(d-10)^2-5.
\]
This excludes \(d=10,11,12\). At \(d=13\) the left side is at least 5: for each height \(j\) the summand of \(T-D\) is nonnegative and at least \(j-3\); the seven sites of \(P\) receive at least 26 contacts. But the right side is 4. Thus \(m=|C|\le4\).

Finally every vertex \(v\in N\cup N'\) sees \(\gamma_v\ge2\) positives in the common \(P\), and its internal negative degree in any available labeling is \(\gamma_v-2\). Both negative graphs have \(k=e_P+3\) edges. Since their shared vertices have total negative degree \(2e(C)+E\) in either, the sum of these degrees over the union is \(4k-2e(C)-E\). The union therefore witnesses at least
\[
 (36-m)+2(4k-2e(C)-E)
 =36-m+6k+2e-2e(C)
\]
positive-pair slots, using \(k=e+E+e(C)\). For \(1\le m\le4\), the forest bound \(e(C)\le m-1\) makes this at least \(56-3m\ge44\). For \(m=0\) it is \(36+8k\ge60\). Both exceed the full positive-pair capacity \(42-e_P\le42\). No two fields share the same positive set.
