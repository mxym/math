# The matching upper bound in every intermediate dimension

Use the sampling model and notation of PROOF.md. For every fixed \(d\ge3,\ 2\le k\le d-1\) and compact convex body \(K\) with interior,
\[
 E D_k(X_n)=\Theta_{K,d,k}\!\left(n^{d-k+\min(1,k/(d-k+2))}\right).
 \tag{1}
\]
The lower bound in the companion proof suffices. The upper bound is immediate from the total number of possible completions when \(k\ge d-k+2\). We prove the nontrivial upper bound \(O(n^{d-k+k/(d-k+2)})\) below. No claim about a leading constant or a distributional limit is made.

Put \(r=d+1-k,\ c=r+1=d-k+2\), and normalize \(|K|=1\). All constants may depend on the fixed body and dimensions.

**Tube estimates.** For a fixed affine subspace of codimension \(b\) meeting \(K\), the distance \(Y\) of one uniform point to it satisfies \(\Pr(Y\le u)\le C u^b\). This follows by projecting a bounded ball containing \(K\) onto the subspace and integrating the perpendicular \(b\)-ball of radius \(u\). Consequently \(E Y^{-s}\le C_s\) uniformly over those subspaces whenever \(0<s<b\), by integration of the small-distance tail.

For \(k\) independent base points, let \(a\) be the \((k-1)\)-volume of their simplex. Successive base-height formulas express \(a\) as the product of \(k-1\) distances to the successive affine spans divided by \((k-1)!\). Their conditional tube exponents are \(d,d-1,\ldots,c\). The last distance has tail bounded by \(Cu^c\); conditioning on all the earlier distances therefore gives
\[
 \Pr(a\le s)\le C s^c
 \tag{2}
\]
since their product has uniformly bounded inverse \(c\)-th moment, by iterating the conditional estimate with exponents all strictly greater than \(c\). For \(k=2\) the earlier product is empty. Degenerate bases form a null event.

Now fix a nondegenerate base \(S\) of volume \(a\) and complete it with \(r\) fresh uniform points to form a \(d\)-simplex of volume \(W\). Its new distance factors have conditional tube exponents \(r,r-1,\ldots,1\); specifically \(W=a[(k-1)!/d!]\prod_{j=1}^r Y_j\). The same argument, using the final linear tail and uniformly bounded prior reciprocal moments, shows that
\[
 \Pr(W\le s\mid S)\le C s/a,\qquad
 E[e^{-\lambda W}\mid S]\le C/(\lambda a)\quad(\lambda>0).
 \tag{3}
\]
The second inequality follows by integrating the first against \(\lambda e^{-\lambda s}\,ds\).

**Conditional moments including overlapping completions.** Let \(D(S)\) count empty completions of this designated base within the full sample. For any fixed positive integer \(t\), uniformly over nondegenerate bases \(S\), for all sufficiently large \(n\)
\[
 E[D(S)^t\mid S]\le C_t(n^{r-1}/a)^t .
 \tag{4}
\]
In the expansion of this power, an ordered list of \(t\) completion label sets (each having \(r\) nonbase labels) uses \(v=tr-l\) distinct labels for some \(l\ge0\). Each intersection pattern permits at most \(n^v\) assignments and there are only finitely many patterns, depending on \(r,t\). At least \((t-l)_+\) of the sets can be retained pairwise disjointly: as long as a label appears more than once, remove one whole set containing that label, thereby reducing the current number of repeated occurrences (total occurrences minus number of distinct labels) by at least one.

Condition on the positions of all \(v\) used labels and on \(S\). For all the simplices to be empty it is necessary that the other \(n-k-v\) samples avoid their union. Thus the conditional joint probability is bounded by \(\exp[-(n-k-v)|\mathrm{union}|]\); any additional restrictions on the \(v\) labels need not be imposed for this upper bound. With \(s=(t-l)_+\) retained simplices of volumes \(W_1,\ldots,W_s\), the volume of the union is at least \((W_1+\cdots+W_s)/t\), even when the simplices intersect. Each retained simplex depends only on its disjoint label set and the fixed base. Integrating and applying (3), the probability conditional just on \(S\) is at most \((C_t/(na))^s\), since \(n-k-v\ge n/2\) eventually. For \(l<t\), the contribution of one pattern is at most
\[
 C_t n^{tr-l}(na)^{-(t-l)}=C_t (n^{r-1}/a)^t a^l .
\]
For \(l\ge t\), bound it by \(n^{tr-l}\le n^{(r-1)t}\). The volume \(a\) is bounded above by a body-dependent constant, so summing all patterns proves (4).

**Maximum over bases.** For \(b>0\) and any integer \(t>c\), (2) implies
\[
 E\min(1,(b/a)^t)=\int_0^1 \Pr(a<b z^{-1/t})\,dz
 \le C b^c\int_0^1 z^{-c/t}\,dz\le C' b^c .
 \tag{5}
\]
Take the conditional Markov bound (4) at threshold \(y n^{r-1+k/c}\), capped at probability one. Use (5) with \(b=C_t^{1/t}n^{-k/c}/y\), and union-bound over at most \(n^k\) possible bases. For \(y\ge1\) this gives
\[
 \Pr\{D_k(X_n)>y n^{r-1+k/c}\}\le C y^{-c}.
\]
Integrating in \(y\) is legitimate since \(c>1\). This proves the required upper bound, completing (1).
