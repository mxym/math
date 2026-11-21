# A fixed-target reverse dispersion block on actual reflected semiprimes

Take the actual fixed even target \(N=2x\), \(L=\log x\), the genuine short prime \(x^{.10}<s<x^{.14}\), \(q=(N-m)/s\), \(m\in[x,3x/2)\), and all unit restrictions of [DoubleSmoothBoundedRankResidual.md](DoubleSmoothBoundedRankResidual.md). Keep its exact \(W_s(q)=K_{P_3}(sq)\) and the reverse coefficient \(B_f(q)\) from [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md). Thus the exact opened row has actual \(q=r k j\) with independent \(\mu(r)\Lambda(k)\Phi(\log r/\log Y)1_{k>Y}/\log q\), \(Y=x^{.070}\), and free positive integer \(j\). On the family below \(r>Y\), so every allowed reverse smoothing has \(\Phi=1\) identically.

Write \(\alpha_s=\log_x s\), \(t_0=103/256\), \(a_0=153/256\), and \(b_0=50/256\). Fix any \(0<\delta<1/100\) and put \(w=\delta/1000\). For each true \(s\), take the **actual reflected semiprimes** \(m=p h\) with genuine primes \(p,h\), and
\[
         |\log_x p-(t_0-\alpha_s)|<w .
\tag{1}
\]
Here \(p\) is visibly the smaller prime; \(h\) has its true central product range and no artificial prime surrogate. One can weight this actual reflected rank-two family by \(-2\log p\), its literal linear half-cut coefficient (away from the half neck), or by any independently allowed product of log-bounded \(p\)-weight and fixed smooth physical tests. The precise weight below is \(-2\log p\).

For either one of the following distinct selections of the two **actual** reverse labels, put \(A=s r k\):
\[
\begin{array}{ll}
 \text{(i)} & |\log_x r-(t_0-\alpha_s-\delta/4)|<w,
             \qquad Y<k\le x^{b_0-3\delta/4},\\
 \text{(ii)} & |\log_x k-(t_0-\alpha_s-\delta/4)|<w,
             \qquad Y<r\le x^{b_0-3\delta/4}.
\end{array}
\tag{2}
\]
Keep the original high \(k>Y\) in both cases. Then for every fixed \(D>0\), uniformly for each \(N\), the actual signed block of this reflected rank-two row satisfies
\[
\sum_{\substack{p h+s r k j=N,\ x\le p h<3x/2\\
           s,p,h\text{ prime},\ (p h,N)=1\\
           s,p,r,k\text{ in (1)--(2)}}}
     (-2\log p)\,\mu(r)\Lambda(k)\,
               \frac{W_s(rkj)}{\log(rkj)}
                            \ll_{D,\delta} xL^{-D}.
\tag{3}
\]
The central choice \(\log_x\min(r,k)\) near the upper bound in (2) reaches \(\log_x A=a_0-\delta+O(w)\). The entire interval of the smaller label in (2) is allowed, not just its endpoint dyad. This is an application of an existing dispersion theorem to exact factors of the actual equation, with genuine cancellation of the signed principal contribution. It is **not** a contiguous statement over all moduli below \(x^{153/256}\), a replacement of the true \(q\)-prime profile by the entire opened row, or a sign bound for its untouched complement.

## 1. Exact physical progression and independent boxes

For fixed \(s,r,k\) with \((A,N)=1\), the exact condition on \(m=p h\) in (3) is \(m\equiv N\pmod A\), with \(m\in[x,3x/2)\) and \((m,N)=1\). The quotient \(j=(N-m)/A\) is then a positive integer automatically; its scale in the selected family is polynomially long. If \((A,N)>1\), the physical unit support is empty. Both \((p,N)=1\) and \((h,N)=1\) can be imposed separately. The test in the displayed sum is
\[
                W_s((N-m)/s)/\log((N-m)/s),
]
well defined also for the real argument of a reduced progression mean. It does not depend on \(r,k\) except through the exact progression in the physical sum.

Here is one way to feed the moving exponent bands (1)--(2) into a theorem requiring independent coefficients. First dyadize \(s\), and subdivide into disjoint fine relative pieces of width \(O(L^{-B})\) for large fixed \(B\), freezing \(\alpha_s\) at the midpoint of each such piece. Retain independent intervals for \(p\), for the large label in (2), and for the other independent labels, and then dyadize as needed. Relative arithmetic boundary errors from (1) reduce to a strip for \(s p\) of relative width \(O(L^{-B})\) near an endpoint. For each \(s\sim S\), its \(p\sim P\) choices in the strip number \(O(P L^{-B}+1)\). For each of these the possible integer \(h\) satisfy \(p h\equiv N\pmod s\); with \(p\ne s\) their count is \(O(x/(SP)+1)\) even when the primality test on \(h\) is discarded. Thus the unweighted physical boundary size is
\[
             O(x L^{-B}+ x/P+ SP L^{-B}+S).
\tag{4}
\]
Any remaining factorization or log weights are absorbed through Cauchy and fixed divisor moments on the physical \(m,N-m\): each physical point has only divisor multiplicity in all its labels. A boundary on \(s r\) or \(s k\) is even more direct: for fixed \(s,v\) with \(v=r\) or \(k\), the physical \(n=N-m\) is a multiple of \(s v\), so the same count (4) now has \(P\) the scale of \(v\). There are no concealed independent q-factor masks. The powers \(SP\), \(SV\) at these boundaries are strictly smaller than \(x\) and every marked variable is polynomially long. In the reduced main, the corresponding strips have a factor \(O(L^{-B}+1/P)\) in the divisor-harmonic sums (use the \(O(x/p+1)\) count of \(h\) for a boundary on \(p\)). All label sums after their \(1/\phi(A)\) weight cost only log powers. Thus freezing has arbitrary logarithmic reserve on both sides. One could equivalently define the theorem on disjoint dyads in \(s\) using the fixed dyad exponent from the start.

The exact central product test \(m\in[x,3x/2)\) is imposed by the analogous log-fine Cartesian mesh in \(p,h\), always using independent prime intervals. The excluded physical edge consists of a union of intervals in \(m\) of total length \(O(xL^{-B})\), whose divisor-weighted sums have the same reserve. For the reduced main, use the divisor envelope times \(\sum_{A\le x}\tau(A)^C/\phi(A)\ll L^{C'}\). Smooth tests in \(m/x\) and the literal W-weight are compatible with this mesh. More explicitly, put \(b=\log((N-m)/x)\in[-\log2,0]\). Then
\[
 \log((N-m)/s)=L-\log s+b,	\quad
 W_s((N-m)/s)=(1-z)(1-2z)^2,\quad z=\frac{\log s}{L+b}.
\]
Finite Taylor expansions in the bounded \(b\) separate these factors into a fixed sum of products of an \(s\)-coefficient and a smooth test in \(m/x\), with arbitrary log reserve at the cost of fixed order. In the latter test one may partial-sum via its variation or freeze on the same physical mesh. All coefficients on the independent boxes are hence 1-bounded after fixed log divisions (\(\Lambda(k)\), \(\log p\), and the separated factors cost only fixed log powers).

## 2. The uniform moving-residue dispersion margins

Apply [Lichtman, arXiv:2309.08522v1, Proposition 5.2 (5.2)](https://arxiv.org/html/2309.08522v1#S5), with actual residue \(a=N=2x\). Its source scale parameter is \(x\) on every box: the two prime labels \(p,h\) have product length comparable to \(x\). For every fixed positive theorem reserve \(\varepsilon\), the true residue is in \(0<|a|<x^{1+\varepsilon}\) for all sufficiently large \(x\). The short sequence is the actual prime \(p\) at exponent \(\beta\) near \(t_0-\alpha\). Its support is \(z_0=x^{1/(\log\log x)^3}\)-rough and it is Siegel–Walfisz with the source auxiliary coprimality: for small moduli this is prime SW on the actual interval, with at most the distinct excluded prime divisors of the auxiliary mask removed; for large moduli the trivial count gives the required log-reserved discrepancy (also for the reduced mean). The same applies with the \(N\)-unit mask. Multiplying by \(\log p/L\) is permitted by partial summation of the SW condition on the independent prefix intervals. The long sequence is the actual prime indicator at \(h\), unit to \(N\), and need not be treated as smooth. All independent modulus weights include the exact \((s r k,N)=1\) mask factor by factor, and do not depend on \(p,h\).

Use the ordered modulus slots \((r,k,s)\) in (i) and \((k,r,s)\) in (ii), with exponents \((v_1,v_2,v_3)\). To verify the numerical conditions take \(\theta=7/32\), \(v_3=\alpha\), \(\beta=t_0-\alpha\), and first take the central upper values \(v_1=\beta-\delta/4\), \(v_2=b_0-3\delta/4\). The four exponent rails of the source become
\[
\begin{split}
 v_1-\beta&=-\delta/4,\\
 2\beta+v_2+2v_3&=1-3\delta/4,\\
 \theta+\beta+v_1+5v_2+2v_3&=2-4\delta,\\
 (1+2\theta)\beta+v_1+(5-2\theta)v_2+(2+2\theta)v_3
       &=7667/4096-(235/64)\delta<1.872 .
\end{split}
\tag{5}
\]
The third line pays the actual constant \(2^\theta\) as an \(o(1)\) in exponent, not a frozen small residue. The coefficients of \(v_2\) in the last three rails are strictly positive, so every lower dyad in the smaller slot is allowed. The aggregate change in any rail from the fixed exponent widths is \(<10w+o(1)\), including dyad factors, endpoint meshes and a frozen \(s\)-exponent. Thus \(\varepsilon=\delta/100\), for example, fits all inequalities with fixed reserve for large \(x\). This supplies the centered actual progression discrepancy to arbitrary log precision after summing the mesh count. No well-factorability is assumed of \(\mu(r)\Lambda(k)\) regarded as a single modulus weight.

This selection approaches the source's natural large-residue frontier at the prescribed orientation: ignoring strict margins, the first rail forces \(v_1\le\beta\); with \(v_3=\alpha\), the second and third then force
\[
 a:=v_1+v_2+\alpha\le 1-(\beta+\alpha),
 \qquad 5 a\le 2-\theta+3(\beta+\alpha).
\]
Indeed if \(u=\beta-v_1\ge0\), the first bound is only strengthened by subtracting \(u\), the second by subtracting \(4u\) on its right. Combining gives \(a\le(5-\theta)/8=153/256\), at \(\beta+\alpha=103/256\). This is the known exponent calculation, not a new analytic distribution level; the point of (5) is the genuine fixed-target two-prime application and its compatible moving independent labels.

## 3. The entire selected principal contribution has zero main

The reduced mean from the theorem has the exact factor \(1/\phi(s r k)\) and exact mask \((m,s r k)=1\). In the actual formula for this mean now unfreeze the original constraints, with the reserve from §1. Fix the actual \(s,m\) and an actual \(\Lambda\)-argument \(k\); \((s k,Nm)=1\) is required. The allowed \(r\) interval is then independent of \(k,m\) except for its explicit unit mask. In (i) it is the \(s\)-dependent polynomially long band; in (ii) it is \(Y<r\le x^{b_0-3\delta/4}\). One may also retain a dyadic interval for \(r\). After taking out \(1/\phi(s k)\) its arithmetic sum is, for every fixed \(D>0\),
\[
  \sum_{r\text{ in its true selected interval},\ (r,Nm)=1}
      \frac{\mu(r)}{\phi(r)}
        \prod_{p'\mid(s k,r)}(1-1/p')=O_D(L^{-D}).
\tag{6}
\]
This uses the factor identity \(\phi(s k)\phi(r)/\phi(s k r)=\prod_{p'\mid(s k,r)}(1-1/p')\), also when \(s\) equals the prime base of \(k\). Expand that product over \(d\mid\operatorname{rad}(s k)\) with coefficient \(\mu(d)/d\), where there are at most four possible \(d\). If \((d,Nm)>1\) its part is already zero. Otherwise write \(r=d v\) with \((v,d N m)=1\) on the nonzero Möbius support. For \(d\le x^{.03}\) the endpoints in \(v\) are polynomially long, because every selected \(r>Y=x^{.070}\). The uniform finite constant moment \(\sum_{v\le T,(v,d N m)=1}\mu(v)/\phi(v)=O_D(L^{-D})\) from [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md), eq. (11), applies on both endpoints. For \(d>x^{.03}\) simply bound \(1/(d\phi(d))\sum_{v\le x}1/\phi(v)=x^{-.06+o(1)}\). This proves (6) whether or not actual prime factors of \(m\) coincide with parts of the original modulus (that issue was retained in the masks). The remaining \(s,k\) masses with their \(\Lambda(k)/\phi(s k)\) weight have only harmonic log cost, and the physical \(m\)-sum is \(O(xL^C)\), even with divisor envelope. Thus the reduced principal part itself is log-small, yielding (3). This last step is why (3) is cancellation of a true signed opened sector, not just a bound for its progression discrepancy.

The rest of the true rank-two profile contains other placements of \(r,k\), including completely unsplit high columns and the larger \(A\)-range. In particular (3) only removes the sectors inside (2) from the actual prime-quotient comparison of [CompensationNeutrality.md](CompensationNeutrality.md); it does not turn that comparison into a whole lower or upper bound. It bypasses the coarsened joint-marginal model by using a fixed-target weighted dispersion estimate at the actual congruence, not by assigning independent near-window counts.

## Comparison with nearby work

The large-residue dispersion theorem and its frontier are [Lichtman's](https://arxiv.org/abs/2309.08522). [Pham's October 2026 v1](https://www.preprints.org/manuscript/202610.3061) treats other fixed-target rough comparisons. The repository's other reverse-quotient estimates address different product tests, reflected factors, or modulus regions. Here the two signed selections concern true reflected semiprimes with the prescribed moving short-prime band; neither the full rank-two comparison nor the complement of these modulus slots is evaluated.
