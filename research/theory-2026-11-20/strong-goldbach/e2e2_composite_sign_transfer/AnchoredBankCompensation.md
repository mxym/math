# A signed compensation for the actual high-bank determinant sector

Use the exact disjoint-bank scores \(F_{1,J},F_{2,J}\) of [the composite-only transfer](Proof.md) on a fixed regular macroscopic box, as in [the adverse high-bank family](HighBankDebt.md). Write \(x=N\), \(L=\log x\), \(d=d_J=.02/(4K^2+4K-1)\), \(K=J+1\), \(D=x^d\), \(W=x^{2.1d}\), \(M=\mathfrak S(N)\mathcal V\), and \(K_j=\lambda-F_{j,J}\). Keep the same literal short labels \(u,v\), long windows, and equation \(ut+vs=N\). The physical \(t\)-overlap length \(\ell_{u,v}\) on the macroscopic box is \(\gg x^{.5125}\).

Restrict the **same opposite leg in both families** to \(s=rZ\) with a true target-unit prime \(r\in(x^{2d},x^{2.1d}]\) and \(P^-(Z)>W\). This fixes a canonical \(r\) if present, and \(s\) is composite with \(K_2(s)=-\log s\). On the \(t\)-leg take the disjoint union of:

* **A.** \(t\) is a \(W\)-rough composite, with no restriction on bank occupancies.
* **B.** The part of \(t\) supported on primes \(\le W\) is a squarefree product \(m=p_1\cdots p_k\) of \(2\le k\le J\) distinct target-unit primes in \((D^{1/2},D]\). Every leg-1 bank has a prime divisor of \(t\).

Let \(\mathcal C_J(N)\) be the sum of the **actual signed** terms \(K_1(t)K_2(s)\), with the usual short weights \(\log u\log v\), on this union. Put
\[
 \lambda_0=\log 2,\qquad
 c_*=\frac{e^{-2\gamma}(.5125)^2}{(2.1)^2}
                 \log\!\left(\frac{21}{20}\right)>0.
\]
Then there is an absolute error sequence \(\delta_J\to0\) (indeed a fundamental-lemma error at parameter \(.014/(2.1d_J)\)) for which
\[
 \limsup_{\substack{x\to\infty\\2\mid x}}
 \left|\frac{d_J^2\mathcal C_J(N)}{M}
        -c_*\left(1+\sum_{k=2}^J\frac{(1-k)\lambda_0^k}{k!}\right)\right|
       \ll d_J+\delta_J .
\tag{1}
\]
In particular the combined contribution is \(\gg d_J^{-2}M\) for all sufficiently large fixed \(J\) and then all large even \(N\). Indeed the bracketed coefficient tends decreasingly to \(2(1-\log 2)>.61\). This pays the entire specified adverse family B using A; it is not a sign for the complement or the full repaired bracket.

## Actual scores and exact tuple expansion

For A the score is \(K_1(t)=-\log t\), because no prime \(\le D\) divides \(t\), while B is genuinely adverse. To see the latter, every product of two of its small labels exceeds \(D\). Thus
\[
 F_D(t)=(1-k)\log t+\sum_{i=1}^k\log p_i<0.
\tag{2}
\]
The complete small-divisor response is zero, as \(2\le k\le J\), so \(F_{1,J}(t)=B_1(t)F_D(t)\). Actual factors above \(W\), including repeated ones and more than one in a bank, do not affect (2). Small repeated factors are excluded in B by its specified squarefree small part, not approximated or erased in the sum.

Expand \(B_1(t)\) over one actual true prime from each original leg-1 bank. For each such bank tuple with product \(b\), write \(t=m b T\). Then \(P^-(T)>W\), **independently of which bank tuple was selected**, because every factor of \(b\) exceeds \(W\) and the entire part of \(t\) supported on primes \(\le W\) is exactly \(m\). Conversely \(T\) rough in this factorization certifies exactly that small part. The small labels are ordered, for example in increasing order, so their count is the unordered \(1/k!\) harmonic count. For a fixed bank tuple the physical \(T\) is unique, and summing over all bank tuples (each with weight \(\prod_iH_i^{-1}\)) yields precisely \(B_1(t)\); there is no canonical-bank approximation. For A write \(t=T\), with \(m=b=1\), and no bank weight. A and B have disjoint physical \(t\)-supports. The earlier two-small adverse witness is inside B, with identical actual tuple contribution conventions, since both its small bands lie above \(D^{1/2}\).

## A common true two-form sieve estimate

Fix the short labels and all selected small, bank, and \(s\) tags. The actual progression \(u m b T+v r Z=N\) has coprime target-unit slopes. Its parameter interval has real length
\[
 Y=\frac{\ell_{u,v}}{v m b r}\gg x^{.016}.
\tag{3}
\]
Indeed \(m b r\le x^{(J+K(K+3)+2.1)d}<x^{.009}\), because for \(K\ge4\),
\(.45(4K^2+4K-1)>K^2+4K+1.1\). This holds at \(4\) and the difference increases thereafter. The same bound is automatic for A.

Sieve \(T,Z\) jointly up to \(W\) at level \(E=x^{.014}\). At primes not in the slopes there are two roots except at target primes, where the roots coincide. At a slope prime the form with zero step is a nonzero constant (the slopes are target units), and the other has one root. The prime \(2\) always has one root since the slopes are odd and \(N\) is even. Thus the absolute dimension-two product axiom and the floor sum \(O(x^{.014}L)\) are exactly as in the adverse-family proof. All selected slope primes in the sieve range are \(\ge D^{1/2}\); for fixed \(J\) there are boundedly many, so their local corrections are \(1+o_J(1)\) **uniformly over the actual tuples**. The target-prime product beyond \(W\) has the same uniform tail \(O(L/(W\log W))\). Therefore the [fundamental lemma, Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=206) gives
\[
 \#\{T,Z\ {\rm in\ the\ true\ row},\ P^-(TZ)>W\}
 = \frac{e^{-2\gamma}Y\,\mathfrak S(N)}{(2.1d\,L)^2}
      (1+O(\delta_J)+o_J(1)),\quad
 \delta_J \ll s_J^{-s_J/2},\quad s_J=\frac{.014}{2.1d_J}.
\tag{4}
\]
The \(O\) constant for the relative sieve error is absolute, and the \(o_J(1)\) absorbs the power-saving floor errors in (3). Equation (4) is two-sided, so multiplication by a signed coefficient below uses its absolute envelope, not a signed inequality in the wrong direction.

In A the count (4) initially includes prime \(t\), which must be removed to evaluate its genuine composite score. For these prime cases use an upper two-form sieve on \(u t+v r Z=N\), sieving both forms up to \(W\) and only the \(t\)-form from \(W\) to \(x^{.001}\). For all sufficiently large fixed \(J\) this last cutoff exceeds \(W\); prime \(t\) is larger than the cutoff. Above \(W\) there is precisely one root since all prime factors of the \(t\)-step \(v r\) are either \(\le W\) or larger than \(x^{.001}\). Thus the local upper product is \(O(\mathfrak S(N)/(d L^2))\) by Mertens on the additional range. The same \(E=x^{.014}\) has sieve ratio \(14\) relative to the larger cutoff, above the absolute dimension-two threshold of Theorem 19.1. Its floors are harmless and its upper constant is independent of fixed \(J\). Multiplying by both long logs and summing the canonical \(r\) and short labels shows that the exclusion costs \(O(M/d_J)\). It is a bound for actual one-prime rows, not an assumption of an asymptotic for them.

## Summed signed normalization

The harmonic mass of \(r\) tends to \(\log(21/20)\). The bank harmonic sums including their normalizers are exactly \(1\). The selected small squarefree mass at rank \(k\) is
\[
 \sum_{\substack{p_1<\cdots<p_k\\D^{1/2}<p_i\le D,\ p_i\nmid N}}
         \frac1{p_1\cdots p_k}
 =\frac{(\log 2)^k}{k!}+o_J(1),
\tag{5}
\]
by prime Mertens (and the neglected label collisions have harmonic weight \(o_J(1)\)). All target-prime exclusions in these polynomial bands have \(o_J(1)\) reciprocal cost. Equations (3)–(5) keep the exact common \(\ell_{u,v}/v\) in both families. The two physical long logs are \(.5125L+O(1)\); the additional term \(\sum\log p_i\) in (2) is bounded by \(k d L\). Its contribution to the \(d_J^2/M\) normalization is \(O(d_J)\), uniformly in \(J\), since the \(k\)-weighted harmonic sum is bounded by the full convergent exponential series. Likewise the relative error in (4) costs only \(O(\delta_J)\) after this normalization, using \(\sum_{k\ge0}(1+k)(\log 2)^k/k!<\infty\). The prime-\(t\) deletion from A costs \(O(d_J)\) after normalization. This proves (1) for the actual signed sum.

The unpriced complement includes smaller-prime bands below \(D^{1/2}\), small square repetitions, higher small rank, other opposite-leg factor profiles, and all other portions needed to control the full determinant. In the present chamber pair products exceed \(D\), which is why the signed exponential is \((1-\lambda_0)e^{\lambda_0}\) and has its sign transition at formal intensity \(1\). Widening the allowed small band below \(D^{1/2}\) admits pairs within the divisor cutoff and changes that formula; no such extrapolation, or binary prime conclusion, is claimed.
