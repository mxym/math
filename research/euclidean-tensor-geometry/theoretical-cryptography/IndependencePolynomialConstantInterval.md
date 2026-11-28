# Improved constants at prescribed independence number

**Yongxian Zhang.** AI-assisted mathematical development, with an independent internal rederivation and a separate exact replay of the finite examples. No external peer review or priority claim.

Let \(N(r)\) be the least order of a graph with independence number \(r\) and a nonunimodal independence polynomial, and \(N_{\rm conn}(r)\) the corresponding minimum among connected graphs. Put \(L=\log_2(5/4)\). Then
\[
 \frac{2}{\tfrac12+L}
 \ \le\ \liminf_{r\to\infty}\frac{N(r)-r}{\sqrt r}
 \ \le\ \limsup_{r\to\infty}\frac{N_{\rm conn}(r)-r}{\sqrt r}
 \ \le\ \frac{2}{L}.
\]
The outer constants are approximately \(2.433302879\) and \(6.212567439\). This strengthens both constants in the [earlier released proof](https://doi.org/10.5281/zenodo.24615591), which established the \(\sqrt r\) scale and bounds \(1.82676\) and \(10.88974\). The new upper bound is for **connected graphs**; it is not a cograph upper bound. The earlier connected cograph construction and its \(10.88974\) constant remain valid. Neither the existence nor the value of an exact limiting constant is established.

## 1. A sharper bound for the right tail of clique centers

Work in the complement \(H\) of \(G\). Fix a maximum clique \(K\) of size \(r\), leaving \(q\) vertices \(U\). Each clique \(S\) in \(H[U]\), including the empty one, contributes \(x^s(1+x)^d\) to the clique polynomial, where \(s=|S|\), and \(d\) is the size of the common neighborhood of \(S\) within \(K\). Put \(D=r-d\ge s\) and \(\mu=2s-D\le s\), so the associated binomial distribution of clique size has center \((r+\mu)/2\).

A uniform random clique chooses \(S\) with probability proportional to \(2^{-D(S)}\): the choices in \(K\) are all \(2^d\) subsets of the common neighborhood. Write \(Z=\sum_S2^{-D(S)}\ge1\). Expose membership of the \(q\) outside vertices in a fixed order. For any prefix with positive probability, deleting the next vertex maps the possible completions that include it injectively into those that omit it. Earlier choices are unchanged; clique membership is preserved; and \(d\) can only increase, so the weights do not decrease. Therefore each conditional inclusion probability is at most \(1/2\). Sampling with independent uniform random numbers at the steps couples the outside size \(s\) below \(\operatorname{Bin}(q,1/2)\).

Fix \(C<2/(\tfrac12+L)\) and \(0\le q\le C\sqrt r\). For fixed \(\eta>0\), Hoeffding gives
\[
 \Pr(\mu>q/2+\eta\sqrt r)\le
 \Pr(s>q/2+\eta\sqrt r)\le\exp(-2\eta^2 r/q)
\]
for \(q>0\); for \(q=0\) the event is empty. On the left, if \(-\mu>Lq+\eta\sqrt r\), then \(2^{-D(S)}\le 2^{-Lq-\eta\sqrt r}4^{-s}\). Summing over cliques and using \(Z\ge1\) bounds this tail by \(2^{-\eta\sqrt r}\), since \(\sum_S4^{-s}\le(1+1/4)^q\).

Retain the terms with
\[
              -Lq-\eta\sqrt r\le\mu\le q/2+\eta\sqrt r.
\]
Choose \(\eta>0\) small enough that \(C(L+1/2)+2\eta<2\). The retained centers then have scaled \(\mu\)-width strictly less than two. The total discarded mass of the normalized polynomial is \(\exp(-\Omega(\sqrt r))\), uniformly for \(q\le C\sqrt r\).

## 2. The central curvature and the tail splice

Consider any fixed window \(k=r/2+O(\sqrt r)\). All retained terms have \(d=r-O(\sqrt r)\), since \(D=2s-\mu=O(\sqrt r)\), and the index \(j=k-s\) is strictly inside their binomial support. Their normalized binomial masses at \(k\) are bounded below by a positive constant times \(r^{-1/2}\), uniformly over the window, by Stirling's local estimate. Since the retained probability is \(1-o(1)\), their aggregate coefficient \(P_k\) in the normalized polynomial has the same lower bound. The discarded contribution at \(k,k-1,k+1\) is at most the total exponentially small discarded mass.

Set \(z=(2j-d)/\sqrt r=(2k-r-\mu)/\sqrt r\). Give each retained term weight equal to its fraction of \(P_k\). As in the earlier proof, the termwise two adjacent ratios are \(R=(d-j)/(j+1)\) and \(Q=j/(d-j+1)\), and uniformly
\[
 R-1=-2z/\sqrt r+O(r^{-1}),\quad Q-1=2z/\sqrt r+O(r^{-1}),\quad
 R+Q-2=4(z^2-1)/r+O(r^{-3/2}).
\]
Their weighted averages therefore multiply to \(1+4(\operatorname{Var}(z)-1)/r+O(r^{-3/2})\). Because the range of \(z\) is bounded strictly below two, its variance is at most \(1-\varepsilon\) for a fixed \(\varepsilon>0\). The retained adjacent ratios are bounded and all three coefficients change by relative \(o(1/r)\) upon restoring the discarded terms. Hence the full coefficients are strictly log-concave in this window.

To connect the central window to the tails, use
\[
 E=\lceil10q+30\ln r\rceil,\qquad a=\lfloor(r-E-2)/2\rfloor,\qquad
 b=\lceil(r+q)/2\rceil.
\]
Every term is nonincreasing in steps \(k\to k+1\) for \(k\ge b\), since \(\mu\le q\). We check increasing signs up to \(a\) directly. Write \(B_k=\binom rk\) and \(\delta=r-s-d\). Whenever a term can lose mass in a step it is in its support at \(k\), and its coefficient relative to \(B_k\) satisfies
\[
 \frac{\binom d{k-s}}{B_k}\le (k/r)^s
                   \left(\frac{r-k}{r-s}\right)^\delta .
\]
This is the falling-factorial ratio from the earlier proof, also valid for the range here because \(s<r\).

For \(1\le k\le r/4\), a negative term has \(d\le2(k-s)\). Those with \(s\le k/2\) have \(\delta\ge r/2\), so their total relative loss is at most \(e^{-k/4}(1+k/r)^q\le1\) for large \(r\). For \(s>k/2\), summing the looser bound with \(\binom qs(k/r)^s\le(2e q/r)^s\) contributes \(o(1)\). The main binomial's relative increment is at least \(3/2\) for large \(r\), and the step at zero is immediate.

For \(r/4\le k\le a\), terms with \(d+s>r-E\) cannot decrease: their binomial increment is nonnegative since \(2k\le d+2s-1\) (and the step is not beyond their support). All other terms have \(\delta\ge E\). Since \(k-s\ge r/5\) for large \(r\), their total relative loss is at most \(2^q e^{-E/5}<1/r\). The main binomial's increment is at least \(B_k/r\), so the full increment is positive. The indices \(a,b\) both lie at distance \(O(\sqrt r)\) from \(r/2\). The strict log-concavity proved above on \(a<k\le b\) makes consecutive ratios nonincreasing between the increasing left steps and the nonincreasing right steps. Thus no decline can be followed by a strict rise. This proves the lower constant for every fixed \(C<2/(\tfrac12+L)\).

## 3. The connected anchor construction

Fix \(C>2/L\). For each \(r\), choose \(k=C\sqrt r+o(\sqrt r)\) and an integer \(t\) with \(t-k\log_2 5=o(1)\). Indeed, the fractional parts of multiples of the irrational \(\log_2 5\) are dense, and for any requested accuracy a finite initial set is a net on the circle, as is every translate of that finite set. One may therefore choose \(k\) in a block of \(\lfloor r^{1/4}\rfloor\) consecutive integers starting near \(C\sqrt r\) with the required accuracy tending to zero.

Put \(s=r-t\) and \(e=t-2k\), both positive for large \(r\). In \(H\) take the \(r\)-clique split into \(s\) common vertices, \(e\) exclusive vertices, and \(2k\) anchors paired in \(k\) disjoint pairs. There is one extra vertex per pair. These \(k\) outside vertices form a clique. Each is nonadjacent to its own anchor pair and all exclusive vertices, and adjacent to all common vertices and to the other anchors. Add another isolated vertex in \(H\), making its complement connected. On deleting the exclusive vertices, the remaining unisolated vertices form the join of \(K_s\) and \(k\) copies of \(K_2\) disjoint union \(K_1\). A clique involving an exclusive vertex has no outside vertex. The overlap between this join and the original core is exactly the clique on the \(s+2k\) common vertices and anchors, so the full polynomial is
\[
       (1+x)^r+(1+x)^s(1+3x+x^2)^k-(1+x)^{s+2k}+x .
\]
Its degree is \(r\). This is a union with overlap, not a claim of a cograph decomposition.

Normalize the coefficients by \(2^r\). The first two terms have masses \(1\) and \(5^k/2^t\to1\), means \(r/2\) and \(s/2+k\), and their variances are asymptotic to \(r/4\). The subtracted term has mass \(2^{-(t-2k)}\), exponentially small on the \(\sqrt r\) scale. The additional \(x\) has no effect at central indices. The second summand is the distribution of \(\operatorname{Bin}(s,1/2)+J\), where \(J\) is an independent sum of \(k\) variables taking values \(0,1,2\) with probabilities \(1/5,3/5,1/5\), respectively. Thus \(\mathbb EJ=k\) and \(\operatorname{Var}(J)=2k/5\). Its deviation from the mean is at most \(r^{3/8}=o(\sqrt r)\) with probability \(1-o(1)\). Conditional on such a deviation, the fair-binomial local limit theorem applies uniformly on compact standardized intervals; on the exceptional event use the uniform \(O(r^{-1/2})\) maximum fair-binomial point mass.

Writing \(x=(2j-r)/\sqrt r\) and multiplying the normalized coefficients by \(\sqrt r/2\), the rescaled coefficient profile consequently tends uniformly on compact standardized intervals to
\[
                          \varphi(x)+\varphi(x+CL),
\]
where \(\varphi\) is the standard normal density and \((t-2k)/\sqrt r\to CL\). The profile is symmetric about \(-CL/2\) and has positive second derivative there, since \(CL>2\). Choose two nearby fixed points on either side with higher values. The nearest integer ranks to these three points produce a strict valley for all sufficiently large \(r\). The graph has \(r+k+1\) vertices, so letting \(C\downarrow2/L\) proves the upper constant.

The [exact controls](verify_independence_polynomial_constant_interval.py) independently check the finite motif and its overlap, 28,672 small weighted-prefix inequalities, and the connected examples at \((r,k,t)=(1024,230,534)\) and \((4096,450,1045)\), with strict peak–valley–peak ranks \((478,497,509)\) and \((1984,2011,2041)\), respectively. They are checks, not inputs to the asymptotic proof.
