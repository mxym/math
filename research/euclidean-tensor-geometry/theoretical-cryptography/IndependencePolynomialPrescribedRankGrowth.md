# The minimum order of a nonunimodal independence polynomial at prescribed rank

Let \(N(r)\) be the smallest number of vertices in a finite simple graph \(G\) with independence number \(r\) and nonunimodal independence polynomial, and \(N_{\mathrm{conn}}(r)\) the same minimum among connected graphs. These minima have the sharp-order scale
\[
 N(r)=r+\Theta(\sqrt r),\qquad N_{\mathrm{conn}}(r)=r+\Theta(\sqrt r).
\]
More precisely, with \(H_2(x)=-x\log_2 x-(1-x)\log_2(1-x)\), let \(\sigma\in(1/2,1)\) be the unique solution to \(H_2(\sigma)=\sigma\). Then
\[
 \frac{2}{\sigma+\log_2(5/4)}
 \ \le\ \liminf_{r\to\infty}\frac{N(r)-r}{\sqrt r}
 \ \le\ \limsup_{r\to\infty}\frac{N_{\mathrm{conn}}(r)-r}{\sqrt r}
 \ \le\ \frac{5}{\tfrac12\log_2 6-\tfrac56}.
\tag{1}
\]
The displayed outer constants are about \(1.82676\) and \(10.88974\), respectively. The connected upper examples may be chosen as cographs. These are bounds on constants, not a determination of an asymptotic constant or of the finite minima.

The question is different from realizing all coefficient permutations as in [Ball–Galvin–Hyry–Weingartner](https://arxiv.org/abs/1901.06579), and from constructing nonunimodal well-covered graphs as in [Levit–Mandrescu](https://arxiv.org/abs/math/0309151); the present upper family is not asserted to be well-covered. Conditioning on a fixed independent set is a useful common starting point, also explicit in [Li–Vallier–Zhang's 2026 forest proof](https://arxiv.org/abs/2610.07943). Here the graph class is arbitrary for the lower bound, with a constraint only on the excess number of vertices. The results are separate from the [previous exact small ranks](IndependencePolynomialOrder16Ranks.md).

## 1. The clique-polynomial mixture and two trim bounds

In the complement \(H=\overline G\), fix a maximum clique \(K\) of order \(r\) and let \(U=V(H)\setminus K\), with \(q=|U|\). For each clique \(S\) of \(H[U]\), including the empty clique, set \(s=|S|\), \(d=|K\cap N_H(S)|\), and \(\delta=r-s-d\ge0\). Its contribution to the clique polynomial is \(x^s(1+x)^d\). The empty clique gives \(B_k=\binom r k\) at rank \(k\). For an in-support coefficient with \(s\le k\) and \(s<r\), writing \((a)_j\) for falling factorials, we have
\[
 \frac{\binom d{k-s}}{\binom rk}
 =\frac{(k)_s}{(r)_s}\frac{(r-k)_\delta}{(r-s)_\delta}
 \le (k/r)^s \left(\frac{r-k}{r-s}\right)^\delta .
\tag{2}
\]
A coefficient off its support is zero. The number of terms of given \(s\) is at most \(\binom q s\). Define the mode parameter \(\mu=s-\delta\), so the center of the term is \((r+\mu)/2\).

Fix \(c<2/(\sigma+\log_2(5/4))\), \(c>0\). We prove unimodality for \(q\le c\sqrt r\) and all sufficiently large \(r\). Choose constant \(d_->c\log_2(5/4)\) and \(d_+>c\sigma\) with \(d_-+d_+<2\), and put \(D=\lfloor d_-\sqrt r\rfloor\), \(J=\lfloor d_+\sqrt r\rfloor\). Retain terms with \(-D\le\mu\le J\). In every fixed-width central window \(k=r/2+O(\sqrt r)\), the discarded coefficient sum is \(B_k e^{-\Omega(\sqrt r)}\), uniformly for \(q\le c\sqrt r\), for the following two reasons.

* If \(\mu<-D\), then \(\delta>s+D\). With \(u=k/r\), \(v=(r-k)/(r-q)\), the bound (2) and \(0<v<1\) give a relative sum at most \(v^D(1+uv)^q\). Now \(u,v=1/2+O(r^{-1/2})\), so the leading base-2 exponent is at most \((-d_-+c\log_2(5/4)+o(1))\sqrt r\).
* If \(\mu>J\), then \(s>J\) and (2) is at most \(u^s\). If this tail is nonempty, \(q\ge J+1=\Omega(\sqrt r)\) and \(s/q\ge d_+/c+o(1)>\sigma\). The entropy bound \(\binom q s\le2^{qH_2(s/q)}\) follows by evaluating a binomial probability at success probability \(s/q\). Thus \(\sum_{s>J}\binom q s u^s\) decays exponentially in \(q\), since \(H_2(x)-x\) is strictly negative uniformly for \(x\) bounded away above \(\sigma\). If \(d_+\ge c\) makes this tail empty or excludes all \(s\) when strict, the same bound is immediate.

The empty term is always retained.

## 2. The central mixture is strictly log-concave

Let \(P_k\) be the retained coefficient sum. For \(k=r/2+O(\sqrt r)\), every retained term has \(d=r-O(\sqrt r)\) and \(j=k-s=r/2+O(\sqrt r)\) interior to its support. Indeed, \(-D\le s-\delta\) gives \(\delta\le s+D\). Write \(z=(2j-d)/\sqrt r\) for a term, and \(R=\binom d{j+1}/\binom d j,\ L=\binom d{j-1}/\binom d j\). Uniformly over the retained terms,
\[
 \begin{aligned}
 R-1&=-2z/\sqrt r+O(r^{-1}),&
 L-1&=2z/\sqrt r+O(r^{-1}),\\
 R+L-2&=\frac{(2j-d)^2-d-2}{(j+1)(d-j+1)}
       =\frac{4}{r}(z^2-1)+O(r^{-3/2}).
 \end{aligned}
\]
These follow directly by writing the two ratios as \((d-j)/(j+1)\) and \(j/(d-j+1)\). Give each retained term weight equal to its fraction of \(P_k\). Multiplying the two averaged ratios therefore yields
\[
 \frac{P_{k-1}P_{k+1}}{P_k^2}
   =1+\frac4r\big(\operatorname{Var}(z)-1\big)+O(r^{-3/2}).
\tag{3}
\]
Here \(z=(2k-r-\mu)/\sqrt r\), of range at most \((D+J)/\sqrt r\). Its variance is at most one quarter the squared range, hence at most \(1-\epsilon\) for a fixed \(\epsilon>0\) by the choice \(d_-+d_+<2\). Since \(P_k\ge B_k\), the trimmed mass in the previous section is exponentially small relative to it. Neighboring main-binomial coefficients are within a constant factor, as are retained ratios. Hence (3) remains strictly less than one for the **full** coefficients. This argument uses the variance of shifted centers; termwise ordinary concavity would need a smaller permitted spread.

## 3. The tails have the required signs

Let \(a=\lfloor(r-D-2)/2\rfloor\) and \(b=\lceil(r+J+1)/2\rceil\). We show that full coefficients increase for steps \(k\to k+1\) with \(k\le a\), and do not increase for steps \(k\ge b\).

For \(1\le k\le r/4\), any term with a negative increment has \(s\le k\) and \(d\le2(k-s)\). For \(s\le k/2\) its deficiency satisfies \(\delta\ge r/2\), and its ratio from (2) is at most \((k/r)^s e^{-k/4}\) (use \(1-x\le e^{-x}\) on the second factor). The sum of all these relative negative contributions is at most \(e^{-k/4+kq/r}\le1\) for large \(r\). The other terms, with \(s>k/2\), are bounded even without the second factor in (2): \(\binom q s(k/r)^s\le (2e q/r)^s\). The resulting relative sum is \(o(1)\). Each loss is at most the term's own coefficient at \(k\), whereas the main binomial increment is at least \(3B_k/2\) for large \(r\). The step at \(k=0\) is immediate.

For \(r/4\le k\le a\), a negative term necessarily has \(\delta\ge s+r-2k\). If \(k\le r/2-r^{3/4}\), the second factor of (2) is at most \((4/5)^{2r^{3/4}}\) for large \(r\); even multiplied by \(2^q\) it is negligible. For the remaining \(k\le a\), one has \(\delta\ge s+D\) and now \(u,v=1/2+O(r^{-1/4})\). The same \(v^D(1+uv)^q\) bound from Section 1 is exponentially small on the \(\sqrt r\) scale. The main increment is at least \(B_k/r\) throughout this middle-left interval. Hence the full increment is positive.

For \(k\ge\lceil(r+q)/2\rceil\) every term is nonincreasing since \(\mu\le q\). In the intervening range \(b\le k<\lceil(r+q)/2\rceil\) a term with positive increment must have \(\mu>J\). Its gain is at most its coefficient at \(k+1\), and the exponentially small right-tail bound applies there, relative to \(B_{k+1}\le B_k\). The main coefficient decreases by at least \(B_k/r\), so the full increment is negative in that range. The central log-concavity in Section 2 applies throughout \(a<k\le b\). There all successive ratios are nonincreasing, connecting the increasing left tail to the nonincreasing right tail without a return to increasing. This proves the lower bound in (1), allowing every fixed \(c\) below the displayed constant.

## 4. A connected upper family, with two separated Gaussian modes

Put \(\beta=\tfrac12\log_2 6-\tfrac56>0\) and fix \(C>1/\beta\). Choose integers \(k\sim C\sqrt r\) and \(t=\lceil k\log_2 6\rceil\) so that \(\lambda=6^k/2^t\to1\). This is possible by using \(k\) from an interval of length \(\lfloor r^{1/4}\rfloor\) starting at \(\lceil C\sqrt r\rceil\): the fractional parts of multiples of the irrational \(\log_2 6\) are dense, and for each fixed accuracy there is a finite initial orbit that is a net, so every sufficiently long translated block hits that accuracy from below at 1. Let \(s=r-t\); for large \(r\), \(s>0\) and \(t\ge k\).

Take \(H\) to be \(K_s\) joined to the disjoint union of \(K_t\) and the complete \(k\)-partite graph with five vertices in each part, plus one isolated vertex. Its clique number is \(r\). Its complement is a connected cograph (the extra vertex becomes universal) of order \(r+5k+1\), whose independence polynomial is
\[
 (1+x)^r+(1+x)^s(1+5x)^k-(1+x)^s+x.
\tag{4}
\]
Normalize its coefficients by \(2^r\). The first term is the mass function of \(\mathrm{Bin}(r,1/2)\), the second is \(\lambda\) times the mass function of the independent sum
\(\mathrm{Bin}(s,1/2)+\mathrm{Bin}(k,5/6)\), and the negative term is \(2^{-t}\) times the mass function of \(\mathrm{Bin}(s,1/2)\). The latter and the isolated-vertex term are negligible at the scale below. The second distribution's mean is lower than the first by
\[
 t/2-5k/6=(\beta C+o(1))\sqrt r .
\]
Let \(\Delta=\beta C>1\). At integer indices \(m=\lfloor r/2+x\sqrt r\rfloor\) with fixed real \(x\), multiplying the normalized coefficients by \(\sqrt r\) gives the pointwise limit
\[
 g(x)=\sqrt{2/\pi}\big(e^{-2x^2}+e^{-2(x+\Delta)^2}\big).
\tag{5}
\]
For the first term this is Stirling's local binomial estimate, uniform on compact standardized intervals. For the second, condition on \(J_0\sim\mathrm{Bin}(k,5/6)\). Its deviation from its mean is at most \(r^{3/8}=o(\sqrt r)\) with probability \(1-o(1)\) by Chebyshev, because \(k=O(\sqrt r)\). On this event use the same uniform estimate for the fair binomial on \(s\sim r\) trials; off the event its scaled mass is uniformly bounded, again by the standard central-binomial Stirling estimate. This proves (5) without a separate local limit hypothesis on the rare summand.

The function \(g\) is symmetric at \(x=-\Delta/2\), with positive second derivative there (each Gaussian contributes a positive factor proportional to \(\Delta^2-1\)). Thus there are fixed points on each side strictly higher than at the midpoint. For all sufficiently large \(r\) the corresponding three coefficients of (4) obey the same strict valley inequalities, so the polynomial is nonunimodal. The overhead is \(5C\sqrt r+o(\sqrt r)\); letting \(C\downarrow1/\beta\) proves the upper bound in (1).

**Exact controls.** `python3 verify_independence_polynomial_rank_growth.py` checks (2), the finite second-difference identity and a concrete connected witness with \(r=4096,\ k=147\), order \(4832\), and a strict valley between the coefficients at \(1992,2022,2032\). These checks are illustrative; the asymptotic theorem uses the analytic proof.
