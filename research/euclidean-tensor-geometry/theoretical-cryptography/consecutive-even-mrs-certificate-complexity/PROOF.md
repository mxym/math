# Constant subcubes for consecutive even-degree rotation symmetric functions

## 1. Definitions and statements

Let \(d\ge4\) be even, \(n\ge 2d-1\), and let
\[
 F_{d,n}(x)=\bigoplus_{j\in\mathbb Z/n\mathbb Z}\prod_{i=0}^{d-1}x_{j+i}.
\]
A window means \(d\) consecutive positions of this circle. A certificate at \(x\) fixes some coordinates to their values at \(x\) and leaves the function constant on the resulting subcube. Its minimum size is \(C(F_{d,n},x)\); the maximum over \(x\) is \(C(F_{d,n})\). Write \(bs(F_{d,n},x)\) for the maximum number of pairwise disjoint sets of coordinates each of whose simultaneous flips changes the value at \(x\). A certificate must meet each such set, so \(bs(F_{d,n})\le C(F_{d,n})\), with the same pointwise inequality.

Write
\[
 m=d+2,\qquad n=qm+\rho,\quad 0\le\rho<m,\qquad
 h=m-\rho,\qquad
 \mu=\begin{cases}
 \min\{\lceil\rho/2\rceil,h\},&h\le q+1,\\
 \lceil\rho/2\rceil,&h>q+1 .
 \end{cases}
\]
Then
\[
 \boxed{C(F_{d,n})=bs(F_{d,n})=n-\mu\qquad(n\ge2d-1).}
\]
The lower witnesses are adapted from Li--Zhang, Theorem 6.17; Section 6 includes a direct verification. Under their length hypothesis \(q\ge\max\{2,d/2-1\}\), this is exactly their block-sensitivity formula: if \(h\le\lceil\rho/2\rceil\), then \(3h\le d+3\) and \(h\le d/2\le q+1\) (for \(d=4\) use integrality of \(h\)). For smaller \(q\), the distinction can matter: at \(d=8,n=17\), it gives \(C=bs=13\) rather than the \(14\) from the unqualified large-length formula. Quadratics were already handled in their §4. Thus the equality answers the sufficiently-large-length question in §10 for these consecutive families, and also covers a range of shorter lengths. It does not classify lengths below \(2d-1\), other monomial supports, or pointwise equality.

Here \(q\ge1\) because \(n\ge2d-1\) and \(d\ge4\). Always \(0\le\mu\le d/2\): for \(\rho\le d\) use \(\lceil\rho/2\rceil\), and for \(\rho=d+1\) use \(h=1\le q+1\). If \(\mu=0\) the upper bound is immediate.

## 2. Long-run lemma

In a nonconstant word, a *long run* is a maximal cyclic one-run of length \(L\ge d\). If its two boundary zeros are fixed, the surviving windows wholly inside this run start at the indices \(0,\ldots,L-d\) in run coordinates. Define \(P(a)=\#\{j:0\le j\le L-d,\ j\le a\}\bmod2\). With the run centered at its original ones, use \(z_i=1+x_i\) over \(\mathbb F_2\). For a nonempty set \(T\) of free run coordinates with \(\max T-\min T<d\), the coefficient of \(\prod_{i\in T}z_i\) in the restricted run polynomial is
\[
 P(\min T)+P(\max T-d).
\]
Indeed, a term contributes exactly when its start is between \(\max T-d+1\) and \(\min T\), inclusive. If the span is at least \(d\), the coefficient is zero. A run coordinate with even window incidence satisfies \(P(i)=P(i-d)\). Split these coordinates by \(P(i)\in\mathbb F_2\). Any one class can be left free simultaneously: the equality at its largest position and the common value at its smallest position make every nonconstant coefficient zero. In particular, if \(u\) run coordinates have even incidence, at least \(\lceil u/2\rceil\) can be freed. This is the prefix-parity argument of Li--Zhang's sextic Lemma 9.1, applied at arbitrary even \(d\).

In fact \(u\ge L-d\). Put \(c=L-d+1\) and \(a=\min\{c,d\}\). The ordinary (integer) incidence counts ramp up through \(1,\ldots,a-1\), then have \(a\) repeated \(\lvert c-d\rvert+1\) times, then ramp down through \(a-1,\ldots,1\). This follows by intersecting the two intervals of possible starts. If \(c<d\) is odd, the two ramps contain \(c-1\) even counts; the plateau is odd. If \(c<d\) is even, the two ramps contain \(c-2\) even counts, and including the plateau gives \(d-1\) even counts. If \(c\ge d\), only the odd ramp entries contribute to odd counts, exactly \(d\) of them, since \(d\) is even. Thus \(u\ge L-d\) in each case. We can free a set of size at least \((L-d)/2\) in each long run, preserving its contribution.

## 3. Short-cluster lemma

Between consecutive long runs are all positions of an intervening *cluster*. When there is just one long run there is one cluster, the complementary interval. Each cluster starts and ends with zeros (possibly the same zero if its length \(M\) is one), and has no length-\(d\) all-one interval. The whole circle is partitioned by the long runs and these clusters.

For \(M=1\) fix its zero; zero free coordinates then suffice for the bound \(2\lvert S_{\rm cluster}\rvert\ge M-2\). For \(M\ge2\) keep both endpoint zeros fixed. Choose an inclusion-minimal additional set of original zero coordinates, such that the chosen zeros together with the endpoints meet every length-\(d\) interval wholly inside the cluster. Such a choice exists by the no-long-run property in the cluster. In linear coordinates let the selected zeros be \(0=z_0<z_1<\cdots<z_k<z_{k+1}=M-1\), and put \(g_i=z_{i+1}-z_i\). Hitting all the windows is equivalent to every \(g_i\le d\), since otherwise the two zeros enclose at least \(d\) unhit positions. For \(1\le i\le k\), minimality gives \(g_{i-1}+g_i\ge d+1\): otherwise \(z_i\) could be removed. If \(k\ge1\), then
\[
 k(d+1)\le \sum_{i=1}^{k}(g_{i-1}+g_i)
 =2(M-1)-g_0-g_k\le2(M-2).
\]
Consequently \(k\le(M-2)/2\), also trivially for \(k=0\). Free every position except the selected zeros; there are at least \(\lceil(M-2)/2\rceil\) such positions. A window contained in the cluster is killed by the chosen zeros. A window meeting the cluster and its complement passes through one of the two fixed boundary zeros along its cyclic order, so it is also killed. These conclusions use the same fixed boundary zeros as Section 2; the two sets of free coordinates can be used together without creating cross-terms.

## 4. Nonconstant words with long runs

Let \(b\ge1\) be the number of long runs of \(x\). If \(b\le q\), apply Sections 2--3 to all parts and take their union \(S\). Any surviving window lies in one long run; its whole run polynomial is constant under the chosen freedom. The length contributions give
\[
 2|S|
 \ge\sum_{\text{long runs}}(L-d)+\sum_{\text{clusters}}(M-2)
 =n-b(d+2)\ge\rho .
\]
This proves \(|S|\ge\lceil\rho/2\rceil\), hence the required \(\mu\).

If \(b\ge q+1\), then \(n\ge b(d+1)\ge(q+1)(d+1)\) since each long run is followed by a nonempty cluster. Equivalently \(h\le q+1\), so the second term in the minimum defining \(\mu\) is available. Let \(g\) be the number of clusters consisting of a single zero. Every other cluster has length at least two, so
\[
 n\ge bd+g+2(b-g)=b(d+2)-g,\qquad
 g\ge d+2-\rho.
\]
Free precisely those \(g\) zeros and fix all other coordinates. A window cannot contain two such positions: along a cyclic arc between successive such zeros there is a full long run of at least \(d\) positions. Thus the restriction of the polynomial to the \(g\) free variables is affine. At any one such zero, flipping it from zero to one while leaving the others at their original zeros creates exactly \(d\) all-one windows, because the two adjacent one-runs both have length at least \(d\). That number is even, so each affine coefficient is zero. All \(g\) zeros are jointly free.

## 5. Words with no long run, and the all-one word

If \(x\ne 1^n\) has no long run, its original zeros meet every cyclic window. Take an inclusion-minimal subset \(Z\) with this property. The cyclic gaps between successive elements of \(Z\) have lengths at most \(d\); as \(n>d\), there are at least two selected zeros. As in Section 3, deleting any selected zero proves that the sum of its adjacent gap lengths is at least \(d+1\). This also holds for exactly two selected zeros, since deleting one leaves only a single gap of length \(n>d\). Summing over the circle gives
\[
 |Z|(d+1)\le2n .
\]
Fix \(Z\) to zero and free all other positions. The function is identically zero on this subcube, and \(n-|Z|\ge n(d-1)/(d+1)\ge d/2\) for \(n\ge2d-1,\ d\ge4\).

At \(x=1^n\), leave the \(\mu\) positions \(0,2,\ldots,2(\mu-1)\) free, and center at ones as in Section 2. For a nonempty subset of free positions the separation \(e\) between its extremes in the displayed order is even and at most \(d-2\). If \(e>0\), the other arc between the extremes has length \(n-e\ge d+1\), too long for a window (which has \(d-1\) steps). A window containing both ends must therefore run across the displayed short interval, containing the entire subset. There are exactly \(d-e\) such windows: lift the extreme positions to \(a,a+e\), then the possible starts range from \(a+e-d+1\) through \(a\); these starts are distinct modulo \(n\). The same count \(d\) holds for a singleton. In either case the coefficient of the centered monomial is zero, since \(d-e\) is even. Hence these positions are jointly free. This finishes the pointwise upper bound.

## 6. Matching global lower bound

We adapt the witness families of Li--Zhang, Theorem 6.17. First suppose \(h\le q+1\) and \(h\le\lceil\rho/2\rceil\), so \(\mu=h\). Build the word with \(q+1\) runs of length \(d\), separated by \(h\) one-zero gaps and \(q+1-h\) two-zero gaps. Its length is \((q+1)m-h=n\). Every one-coordinate is sensitive because exactly one existing window contains it. Each zero in a two-zero gap is sensitive because flipping it creates exactly one window, extending the neighboring run (the other zero remains fixed). Only the \(h\) one-zero gaps are insensitive. Thus \(n-h=n-\mu\) disjoint singleton flips suffice for the lower bound.

Otherwise write \(\rho=2t+\eta\) with \(\eta\in\{0,1\}\), so \(\mu=t+\eta\) and \(2t\le d\). In fact \(\rho\ne d+1\), since then \(h=1\le q+1,\lceil\rho/2\rceil\) would put us in the first case. Use one exceptional one-run \(1^{d+2t}\) followed by \(2+\eta\) zeros and \(q-1\) ordinary segments \(1^d00\). Its length is \(n\). The exceptional run has \(2t+1\) windows and exactly \(2t\) insensitive coordinates, at offsets
\[
 1,3,\ldots,2t-1;\qquad d,d+2,\ldots,d+2t-2 .
\]
If \(2t\le d-2\), the odd plateau and even ramp entries from Section 2 give exactly those positions. If \(2t=d\), the plateau instead has two entries both equal to the even number \(d\); these supply the offsets \(d-1,d\), while the two ramps give offsets \(1,3,\ldots,d-3\) and \(d+2,d+4,\ldots,2d-2\). This is exactly the same pair of lists. The middle zero of the three-zero gap, if present, is also insensitive; all boundary zeros and ordinary run positions are sensitive as above. For each \(j=0,\ldots,t-1\), pair the exceptional-run coordinates \(2j+1\) and \(d+2j\). Each is individually in an even number of active windows and their distance \(d-1\) means exactly one active window contains both (its start is \(2j+1\le2t\)). Simultaneously flipping their two ones to zero deletes an odd number of active windows, by inclusion-exclusion. The pairs are disjoint and avoid all sensitive singletons. Ignoring the possible middle zero, we have \((n-2t-\eta)+t=n-\mu\) disjoint sensitive blocks. The argument includes \(\rho=0\) with no pairs. This concludes the matching lower bound.

## 7. Reproduction and scope

The upper construction uses only cyclic runs, inclusion-minimal zero sets and interval parities. Its simultaneous freedom is certified by Boolean polynomial coefficients, not just first- or second-order derivatives. The checks enumerate small words and directly expand their restricted Boolean polynomials; separately, a truth-table subcube recurrence computes the exact worst pointwise certificate size without using run structure, and direct evaluation checks the lower-witness blocks in all tested residues, including when the large-length formula does not apply. Neither finite check is needed for the general proof.
