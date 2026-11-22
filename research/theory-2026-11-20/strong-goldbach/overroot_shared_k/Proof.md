# A genuinely composite, above-root branch of the balanced shared-index covariance

This is an unconditional fixed-target calculation for sufficiently large even targets. This treats a signed sector of the actual two-prime covariance, **not** its entire remaining term. It complements the [balanced columns and selected mixed rows](https://github.com/mxym/math/commit/bafa9b8f) by moving the von Mangoldt expansion to the other physical leg and transferring its divisor modulus through an independent genuine slope factor. Neither the prime–prime correlation at an arbitrary pair of slopes nor binary Goldbach is resolved.

Let \(N=2x\) be prescribed even, \(Y=\sqrt x\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\). Take \(d,e\in[.65Y,.8Y]\), \(k\in[Y,1.1Y]\), with \((dek,N)=1\). Thus \(x< N-dk,N-ek<3x/2\). For a slope \(e\) put
\[
 \beta(e)=\sum_{\substack{p_2p_3\mid e\\
                    x^{.029}\le p_2\le x^{.031}\\
                    x^{.075}\le p_3\le x^{.078}}}1 ,
\]
where both labels are distinct genuine primes. This compact angular rectangle lies inside the earlier Maynard wedge. It is an actual mark **multiplicity** rather than the indicator of the whole wedge. The same \(\beta\) can be used on \(d\). On unit slopes both label primes and the remaining cofactor are units. Repeated label valuations are allowed; no artificial random replacement is made.

Write \(y=N-ek\), \(Y_z(y)=1_{P^-(y)>z}\), \(b(y)=Y_z(y)/V_z\), \(V_z=\prod_{p\le z}(1-1/p)\), and \(a(y)=\log y\,1_{y\ {\rm prime}}\). Set \(R_1=x^{.501}\), \(R_2=x^{.505}\), and
\[
 \begin{split}
 F_R(y)&=Y_z(y)\sum_{\substack{r\mid y\\r\le R}}\mu(r)\log(y/r),\\
 K_R(y)&=Y_z(y)\sum_{\substack{r\mid y\\r>R}}\mu(r)\log(y/r),\\
 J(y)&=F_{R_2}(y)-F_{R_1}(y)=K_{R_1}(y)-K_{R_2}(y).
 \end{split}
\]
The identity \(F_R+K_R=Y_z\Lambda\) is exact; on true primes \(F_R=\log y\), \(K_R=0\), as all our primes lie above \(R\). Every nonzero divisor term in \(J\) is on a composite \(y\), since \(R_1>\sqrt y\) for all sufficiently large \(x\). For squarefree \(y\) one also has, exactly,
\(K_R(y)=Y_z(y)\mu(y)\sum_{s\mid y,\ s<y/R}\mu(s)\log s\).
No sign is asserted for that remaining short cofactor score.

**The signed transfer.** For each \(A>0\) and fixed divisor power \(F\), if \(|u_{d,k}|\le L^F\tau(d)^F\tau(k)^F\tau(N-dk)^F\), then for \(R=R_1,R_2\),
\[
 \sum_{d}\left|\sum_{e,k} \beta(e)u_{d,k}\big(F_R(N-ek)-b(N-ek)\big)\right|
       \ll_{A,F} x^{3/2}L^{-A}.                                     \tag{1}
\]
The displayed box and unit conditions are retained throughout. In particular \(J\) has this saving against the actual other prime row, either actual \(K_R\) row, or an independent coefficient within the envelope. Applying (1) in both directions proves
\[
 \sum_{k,d,e}\beta(d)\beta(e)(a-b)(N-dk)(a-b)(N-ek)
 =
 \sum_{k,d,e}\beta(d)\beta(e)K_{R_2}(N-dk)K_{R_2}(N-ek)
     +O_A(x^{3/2}L^{-A}),                                          \tag{2}
\]
while replacing both \(R_2\)'s by \(R_1\) gives the same estimate. It also proves \(\sum_k|\sum_e\beta(e)J(N-ek)|^2\ll_A x^{3/2}L^{-A}\) on the displayed unit geometry. The diagonal may be removed in all three covariance statements at cost \(O(x^{1+o(1)})\). A prime–rough transfer for an arbitrary **joint** slope mask in the \(e\)-sum is not claimed.

**This deleted signed branch is not a small absolute tail.** Let
\[
 M_N=\sum_{d,e,k}\beta(d)\beta(e)a(N-dk)\,\mathfrak S(Nek)
\]
on the same unit box, and let the ordinary binary Euler product be
\(\mathfrak S(B)=\prod_{p\mid B}(1-1/p)^{-1}\prod_{p\nmid B}(1-(p-1)^{-2})\) for even \(B\).
For the mass of the actual negative divisor terms with \(r\) genuinely prime in \(J\), one has
\[
 \sum_{d,e,k}\beta(d)\beta(e)a(N-dk)Y_z(N-ek)
 \sum_{\substack{R_1<r\le R_2\\r\mid N-ek,\ r\ {\rm prime}}}
                   \log((N-ek)/r)
 =
 \left(e^{-\gamma_E}\int_{.501}^{.505}\frac{1-u}{u}\,du+o(1)\right)\ell^2 M_N .       \tag{3}
\]
All logarithmic precision errors from progression replacement are \(O_A(x^{3/2}L^{-A})\) before normalization. Moreover \(M_N\asymp x^{3/2}\varphi(N)/N\) uniformly. In particular both the negative and the compensating positive composite-divisor masses are at least a fixed positive constant times \(\ell^2 x^{3/2}\varphi(N)/N\), even though their full signed difference is negligible. They are divisor-labelled masses, not disjoint sets of physical \(y\).

## 1. The reduced residue and truly over-root distribution

For each fixed \(d\), open \(e=p_2p_3h\) only through the selected slope multiplicity. Group \(p_3 h k\) in the long convolution slot, retaining the independent prime \(p_2\) in the short slot. A divisor \(q\) of \(N-ek\) on this source is coprime to \(N\), and the class is the **actual** fixed integer \(N\bmod q\). There is no modulus \(dq\) in this transfer. The majorant of the grouped coefficient after a possible \(L^B\) factor is a fixed divisor power, since its reconstruction counts ordered factorizations of \(p_3 h k\). The short coefficient is the indicator of a genuine prime in a subinterval of its dyad with \((p_2,N)=1\).

Use [Fouvry, *Autour du théorème de Bombieri–Vinogradov II*, pp. 617–619, Corollaire 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf). For scales \(X_0=4M_0N_0\), with \(N_0\) the short-slot lower endpoint, the theorem is uniform for the common actual residue \(|a_0|\le X_0\), for arbitrary order-\(K\) long and modulus coefficients, provided the short slot satisfies (1.3) and
\[
  N_0\ge X_0^\delta,\qquad
  Q X_0^\delta\le
     \min(X_0^{1/2}N_0^{1/2},\,X_0^{4/7}N_0^{-6/7}).
\]
Condition (1.3) includes auxiliary coprimality in the short coefficient. For a prime interval it follows from Siegel–Walfisz for arbitrary logarithmic moduli; removing prime factors of the auxiliary integer costs at most its number of distinct prime factors, absorbed by the divisor factor in (1.3). Deleting the \(O(L)\) target factors is also harmless. For moduli above that logarithmic range use \(O(N_0/q+1+N_0/\varphi(q))\), which saves arbitrary fixed logs by choosing the log threshold sufficiently large. The original statement uses a signed arbitrary modulus coefficient, not a factorable coefficient. Selecting it to be the sign of the fixed-residue discrepancy, for real data (or splitting real and imaginary parts), gives the sum of absolute discrepancies. Fixed powers of \(\tau(q)\) may be included directly or by Cauchy against their harmonic moments and the trivial divisor-weighted error bound. The exact principal in modulus \(q\) restricts the original input \(ek\) to \((ek,q)=1\) and divides by \(\varphi(q)\).

To apply the independent box statement, partition \(p_2\) and \(p_3 h\) in intervals of relative width \(L^{-B}\), and dyadically, or log-finely if useful, split \(k\). The product range \(e\in[.65Y,.8Y]\) is independent inside complete boxes; its boundary boxes have \(e\) in intervals of total length \(O(YL^{-B})\), and can be paid by integer counts and fixed divisor moments. The coupled \(\log(N-ek)=\log N+\log(1-ek/N)\) can be frozen on the same relative log-fine product mesh with error \(O(L^{-B})\); \(-\log r\) is outside the convolution and costs \(O(L)\). One can keep \(k\)'s arbitrary row weight inside the grouped coefficient. For each box the short and long lower endpoints can be anchored at the actual lower ends within relative \(1+O(L^{-B})\) of the permitted product. Then \(X_0\ge (2.6-o(1))x>N\), as \(ek\ge .65x\). The short exponent is in \([.029,.031]+o(1)\); both upper rails exceed \(.514+o(1)\). Hence \(Q=x^{.506}\) is allowed with fixed slack. The number of boxes is a fixed log power, absorbed by the arbitrary-log distribution.

If \(u_{d,k}\) includes an actual long \(K_R\), it is bounded by \(L\tau(N-dk)\) apart from the stipulated outer envelopes. To use order-\(K\) after factoring out \(L^B\), truncate the part involving \(N-dk\) at \(L^B\) and keep the genuine \(\tau(k)^F\) factor. The discarded total with either other divisor or rough weight is \(O_A(x^{3/2}L^{-A})\): for each unit \(k\sim Y\), the sum of any fixed powers of \(\tau(N-ek)\), \(\tau(e)\) over \(e\sim Y\) is \(O(YL^{O(1)})\) by Hölder and Shiu's upper bound on the class \(N\bmod k\). The shifted progression has \(O(x)\) ambient length and modulus \(\asymp\sqrt x\), in the fixed-gap Shiu range. For the remaining \(d,k\) apply ordinary divisor moments to \(N-dk\), with the at most \(\tau(dk)\) representations of \(dk\) and outer divisor powers. A fixed higher moment and then large \(B\) pay every desired log saving. The interval boundary deletions above use the same moments and Cauchy on the \(O(xL^{-B}+Y)\) pairs \((e,k)\) with \(e\) near an endpoint. These arguments do not apply Fouvry to arbitrary unbounded long coefficients.

## 2. Rough error and the actual principal

Expand the rough condition by adjacent Bonferroni truncations of order \(s=\lceil C\ell\rceil\). With the divisor \(r\mid y\) already opened for \(F_R\), we first restrict \(r\) to be \(z\)-rough, a necessary condition on the exact rough support. Thus it is coprime to all Bonferroni divisors \(m\). The actual modulus is \(rm\le x^{.505}z^{s+1}\le x^{.506}\) eventually. The squarefree smooth–rough decomposition of it is unique; any trivial relaxation of that multiplicity costs at most a divisor factor. The residue is \(N\bmod rm\) with \((rm,N)=1\) and the principal has the actual \((rm,ek)=1\) mask. These statements also cover opening \(b\) alone with \(r=1\).

For clarity about signed remainders: the elementary pointwise error of either truncated rough polynomial is at most \(\binom{\omega_{\le z}(y)}{s}\) (or the adjacent order). Squaring and grouping the two subsets by their union produces at most \(3^u\) patterns with union size \(s\le u\le2s\). Uniform integer counting then bounds the second moment by
\[
 x\sum_{u=s}^{2s}(3\sum_{p\le z}1/p)^u/u!+x^{o(1)} .
\]
Multiplying by the physical divisor weights \(\tau(y)^F\tau(N-y)^F\) and using Cauchy with ordinary divisor moments proves arbitrary-log total errors on the \(x\)-scale, after choosing \(C\) large enough. This includes the \(r\)-sum, since it has at most \(\tau(y)\) terms, and the \(\log(y/r)\) and \(V_z^{-1}\) factors. For temporarily unbounded other-row divisor weights one first uses the clipping in Section 1. Thus the signed \(\mu(r)\) coefficients have not been put through an invalid unsigned sieve bracket.

For a fixed surviving input \(n=ek\), put \(B=Nn\) (even). The literal rough-principal factor is
\[
 V_B(z)=\prod_{\substack{p\le z\\p\nmid B}}(1-1/(p-1)).
\]
The local prime probability is \(1/(p-1)\) because the convolution principal is unit-average, and primes dividing \(N\) or \(n\) have been omitted in just that principal. As in the physical rough polynomial, completing the truncated model costs arbitrary inverse log powers by its factorial tail. One has
\[
 V_B(z)/V_z=\mathfrak S(B)(1+O(L/z))
\]
uniformly; a large exceptional prime divides \(B\ll x^2\), and the generic prime-square tail converges. The actual principal of \(b\) is therefore \(\mathfrak S(B)+O_A(L^{-A})\).

For \(F_R\) the corresponding multiplier is
\[
 V_B(z)\sum_{\substack{r\le R,\ (r,B)=1\\P^-(r)>z}}
        \frac{\mu(r)}{\varphi(r)}(\log y-\log r).
\]
It equals \(\mathfrak S(B)+O_A(L^{-A})\) as well. Here is the necessary uniform moving-\(z\) check. The Dirichlet series of its harmonic coefficients is
\[
 D_{B,z}(w)=\prod_{p>z,p\nmid B}\left(1-\frac{p^{-w}}{p-1}\right).
\]
Factor \(1/\zeta(1+w)\) and an absolutely convergent Euler ratio, times the factors deleting primes \(\le z\) and those of \(B\). On \(\Re w\ge-c/\log z,\ |\Im w|\le \exp(\sqrt L)\) the latter partial Euler products are \(L^{O(1)}\): for \(p\le z\) use \(p^{c/\log z}\le e^c\), while primes \(>z\) dividing \(B\) contribute \(O(L/z)\). The generic Euler ratio is bounded there by absolute convergence. The standard ζ zero-free region and inverse bound apply in this narrower rectangle, since \(\log z=L/\ell^2\gg\sqrt L\); the pole gives a zero, not an obstruction. Perron at a half-integer cutoff near \(R\), shifted to \(-c/\log z\), with height \(\exp(\sqrt L)\), therefore incurs \(O(L^{O(1)}R^{-c/\log z})+O(L^{O(1)}e^{-c'\sqrt L})\). For the first logarithmic moment of the finite Dirichlet polynomial, use a parameter \(r^{-v}\) with \(|v|\le c/(4\log z)\) and Cauchy to differentiate the same contour bound, retaining half the saving. The truncation error of Perron is harmless because \(|\mu(r)/\varphi(r)|\ll(\log\log(3r))/r\), including near the half-integer endpoint. Thus the zeroth partial harmonic moment is \(O_A(L^{-A})\) and the first with \(-\log r\) is \(D'_{B,z}(0)+O_A(L^{-A})\), since \(R^{-c/\log z}=\exp(-(\log R/L)c\ell^2)\). Directly from the Euler factors,
\[
  D_{B,z}(0)=0,\qquad D'_{B,z}(0)=\mathfrak S(B)/V_B(z).
\]
This proves the asserted \(F_R\) principal, including its exact sign.

Summing the matched principals, the tail estimates and Fouvry errors gives (1). Replacing \(a\) by \(Y_z\Lambda\) costs \(O(x^{1+o(1)})\) in the quadratic sums: proper powers have \(x^{1/2+o(1)}\) possible values of a row, with at most \(\tau(N-y)\) representations, and the other row has \(O(Y)\) entries of subpower weight. Expand \((F_R-b+K_R)\) on each physical side and apply (1) to each term containing \(F_R-b\) on one side; the other side is a permitted coefficient. This gives (2) and the same result at \(R_1\). Using \(J\) on the other side directly gives the asserted square estimate. A repeated prime in a rough \(y\) can also be deleted before using the squarefree complementary identity, if desired: such \(y\) number \(O(x/z+\sqrt x)\), and the same fixed divisor moments and Shiu on the opposite row give a power of \(z^{-1}\) saving, more than every log.

## 3. Positive size of the deleted divisor mass

For the negative prime-labelled part use the same expansion and (absolute) distribution with \(r\) now restricted to primes in \((R_1,R_2]\). Its actual multiplier at each \(n\) is
\[
 V_B(z)\sum_{\substack{R_1<r\le R_2\\r\ {\rm prime},\,r\nmid B}}
          \frac{\log y-\log r}{r-1}.
\]
The finitely many excluded primes cost \(O(L^2/R_1)\); \(\log y=L+O(1)\) uniformly, and Mertens's theorem, or partial summation of PNT, gives \(L\int_{.501}^{.505}(1-u)\,du/u+o(L)\) for the sum. With \(V_z\sim e^{-\gamma_E}/\log z\) and \(V_B(z)\sim V_z\mathfrak S(B)\) uniformly, this gives (3).

In \(M_N\) all \(d,e,k\) are units modulo \(N\), as are both slope labels and each residual factor. The counted true-prime row already forces \((k,N)=1\) for unit \(d\): a prime divisor of \(N\) could only be \(x\), which is outside the strict prime-coordinate interior here. The elementary positive marked slope count on either row rectangle is \(\asymp Y\varphi(N)/N\): count the residual factor after fixing \(p_2,p_3\) by CRT with main \(\varphi(N)/N\), whose error per pair is \(O(\tau(N))\) and saves a power in total, and use the positive reciprocal prime masses of the two fixed exponent bands. The Maynard wedge progression mean of [the earlier proof, §1](https://github.com/mxym/math/commit/bafa9b8f) on \(d\) gives the actual true-prime weight \(\asymp x\varphi(N)/N\) after summing \(\beta(d)\) and \(k\). (A lower bound is already enough here.) Since \(\mathfrak S(Nek)\ge\mathfrak S(N)\asymp N/\varphi(N)\), this gives the lower bound \(M_N\gg x^{3/2}\varphi(N)/N\).

For the matching upper bound expand \(\mathfrak S(Nek)/\mathfrak S(N)=\sum_{r\mid ek,(r,N)=1}b_0(r)\) over odd squarefree \(r\), \(b_0(r)=\prod_{p\mid r}(p-2)^{-1}\). For each \(r\), upper bound its divisor condition by summing all splits \(r=u v\), \(u\mid e,v\mid k\). The \(r>L^D\) tail, dropping primality only in this positive upper bound and using \(\log p\le L\), costs \(O(x^{3/2}L\sum_{r>L^D}\tau(r)b_0(r)/r)\) before multiplying by \(\mathfrak S(N)\); this saves arbitrary logs by choosing \(D\) large enough. For the small splits, the marked unit \(e\)-count with \(u\mid e\) is \(\ll Y\varphi(N)/(Nu)\) with negligible aggregate floor errors, since the polynomial labels exceed \(u\). For \(v\mid k\), the actual prime class on the other row is \(N\bmod dv\), with local main \(|K|d/\varphi(dv)\ll |K|(d/\varphi(d))/\varphi(v)\). Its summed errors are covered by the same Maynard wedge proof with auxiliary \(v\le L^D\). The marked unit mean of \(d/\varphi(d)\) is \(O(Y\varphi(N)/N)\): expand \(d/\varphi(d)=\sum_{s\mid d}\mu^2(s)/\varphi(s)\), truncate at a sufficiently large log-power and count the residual slot as for \(e\); the tail is bounded by \(\sum_{s>L^D}1/(s\varphi(s))\) using bounded mark multiplicity and dropping only the unit condition in that negligible tail. Finally the split Euler cost \(\sum_{u,v,(u,v)=1}b_0(uv)/(u\varphi(v))\) converges, by a local \(1+O(p^{-2})\) bound. The unit factors thus remain exactly two independent slope factors on this scale, and the \(\mathfrak S(N)\) multiplier removes one. This proves the stated upper bound as well.

In particular the fixed-target signed cancellation in \(J\) is at a scale on which naive absolute deletion fails. The surviving \(K_{R_2}\times K_{R_2}\) still has both longer factors, and no bound on its aggregate sign or norm is supplied by this argument.


## Related work and scope

[Pham, *Uniformity, Local Structure and Boundary Correlations in Goldbach Representations*, 30 October 2026, Appendix D](https://www.preprints.org/manuscript/202610.3061) is the source of the same shared short \(k\), the genuine \(AA-AB-BA+BB\) comparison and the outstanding covariance input. Its Appendices I–L study a different sharp boundary formulation, including a Möbius product identity and a restricted rational-target Kloosterman frequency bound. In particular Corollary L.3 does not assert a full sum over its moving cofactors. The calculation here uses a factor of the *opposite physical slope* as the short prime slot in Fouvry's theorem. It removes an actual signed divisor band in the shared-\(k\) statistic without inferring either the full \(AA\) asymptotic or arbitrary-row Type II. Fouvry's distribution result is imported, not improved.

The [symmetric rough determinant](https://github.com/mxym/math/commit/a1209af1e8624ead8f8a9a82da4b97125e2f61df) opened two Möbius factors in the different equation \(mn+tb=N\), with fixed polynomial roughness and cutoff \(x^{.3}\). The [first-crossing calculation](https://github.com/mxym/math/commit/c5efe0d531c57023bed40d461e2ba3272bee70e7) evaluated separate over-root prime-source divisor families by Maynard's theorem rather than the shared-\(k\) covariance above. Recent [Grimmelt–Merikoski–Pandey–Pascadi, 30 October, arXiv:2610.41356](https://arxiv.org/abs/2610.41356) concerns primes and Möbius over \(n^2+h\) for almost all shifts; the variable here is shared between two affine forms at a prescribed \(N\). [Gou–Wang–Xu, November, arXiv:2611.18825](https://arxiv.org/abs/2611.18825) studies conditional parity-weighted primitive-character ratios, not this unconditional mixed progression transfer. None of these comparisons asserts exhaustive priority. There is no positive lower bound for binary Goldbach in this note.
