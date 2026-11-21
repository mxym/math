# A unit-weight harmonic pairing of divergent subquarter shell sums

Fix \(0<v<1/4,\ Q=P^v,\ L=\log P,\ I=[P/3,2P/3],\ X=P/3\); retain the notation of [Quarter two signs](PanQuarterTwoSigns.md). At every dyadic \(L^{-1/3}\le y\le L^{-1/5}\) retain the roughness condition \(P^-(r)>z=Q^{2y}\), where \(r=P-p\), and require \(1-u\in[y,2y)\), \(u=\log M/\log Q\). Let \(W_{1,y}\) count unit singleton marks \(M=\ell\mid r\) and \(W_{2,y}\) count unit pairs \(M=\ell_1\ell_2\mid r\), subject to
\[
 \frac{\log\ell_1}{\log M}\in(a,b),\qquad
 a=(1+2e)^{-1},\quad b=1/3 .
\]
The first prime in each pair is strictly smaller. Each configuration has weight exactly 1; a physical \(r\) may carry boundedly many configurations, uniformly across all selected shells since \(\ell_i\gg Q^{a/2}\) and each \(M\) determines its shell. There is no normalization using any observed arithmetic sum.

For any subcollection \(\mathcal Y\) of these shells and any fixed \(A>0\),
\[
 \sum_{p\in I\,{\rm prime},\,p\nmid P}(\log p) B(r)
       \sum_{y\in\mathcal Y}\big(W_{1,y}(r)+W_{2,y}(r)\big)
   =O_{v,A}(P L^{-A}).
\]
This holds also after requiring \(r\) squarefree. For the full collection, each of the two summands separately has magnitude \(\gg_v XS(P)\log\log P\), with opposite signs. This is actual signed cancellation on a bounded nonnegative mask of the *whole physical coefficient* \(B(r)\) at this subquarter cutoff, in contrast to the original-cutoff [divisor-cube result](PanCriticalDivisorCubeCompensation.md), where the mask is on individual short-divisor terms.

**Proof.** In §1 of the cited subquarter proof use the ordinary PNT-strength Mertens estimate \(\sum_{p\le T}1/p=\log\log T+c+O_D((\log T)^{-D})\) for every \(D\), so that its cumulative error for the rough Möbius measure is now \(O_D(U(\log z)^{-D}+UL/z)\) with \(U=\log Q/\log z\ll L^{1/3}\), \(\log z\gg_v L^{2/3}\). This is smaller than \(L^{-A}\) for every \(A\), uniformly. Here \(U\gg L^{1/5}\) also, so for a proper \(e_0\mid M\) the rescaled endpoint satisfies \(\log(Q/e_0)/\log z\gg U\) for both types, including the new pair shapes since the smaller fraction is \(>a\). In the notation \(T_{e_0}\) of §2 there, integration by parts gives \(T_{e_0}=e^\gamma/U+O_A(L^{-A})\), not just \(O(1/U)\): use \(t\rho(t)-\int_0^t\rho\) and the factorial bound on the Dickman tail. The constant-log term involving \(\log e_0\) multiplies the superlog-small endpoint \(\rho(t)+O_A(L^{-A})\). For \(e_0=M\) only the bare component occurs and \(T_M=-u\) exactly. The fundamental-lemma error \(O(Us^{-s/2})\) from the earlier proof is likewise superlog-small since \(s\asymp_v U\). Consequently the whole signed bracket for each \(M\) is
\[
   -\mu(M)(u+e^\gamma/U)+O_{v,A}(L^{-A}).
\]
The multiplicity proof, true fixed-residue maximal BV and sieve product \(V(z)\) are unchanged; improvements to the displayed uniform analytic error need no stronger distribution theorem. In particular before replacing \(V(z)\) by any continuum approximation, it is the **same exact local product** for both label types at each \(y\), since all labels exceed \(z\).

On this compact exponent range the harmonic pair measure is, pointwise in \(u\),
\[
 \frac{dx_1\,dx_2}{x_1x_2}=\frac{du}{u}\frac{dt}{t(1-t)},\qquad
 x_i=\log\ell_i/\log Q,\ t=x_1/u,\qquad
 \int_a^b\frac{dt}{t(1-t)}
   =\log\frac{b/(1-b)}{a/(1-a)}=1.
\]
It is exactly transported to the singleton measure \(du/u\), so the common signed bracket cancels after summing the two types. For arithmetic prime sums the harmonic variables have weights \(1/(\ell-1)\); replacing these by \(1/\ell\) or deleting primes dividing \(P\) costs \(P^{-c_v+o(1)}\). On the compact rectangle, subdivide into exponent cells of width \(L^{-D}\), keeping those inside the piecewise-linear conditions \(u\in[1-2y,1-y]\), \(a u<x_1<b u\). The finitely many boundary strips have harmonic area \(O(L^{-D})\) by Mertens, conditioning on a variable with nonzero coefficient in the boundary hyperplane. PNT with arbitrary log saving on the polynomially sized primes yields the same arbitrary accuracy for the retained rectangular sum and the smooth linear test \(u+e^\gamma/U\). Increase \(D\) and the underlying precision to pay the polynomial number of mesh cells and any factors \(V(z)\log Q\ll L\), as well as the \(O(\log L)\) possible shells. This establishes the uniform claim even for a selected subcollection. Each separate main has opposite sign and size \(\asymp XS(P)\) per shell by \(H_y\asymp y,\ V(z)\asymp S(P)/\log z\). The earlier bounded-multiplicity Cauchy–Schwarz square-removal costs \(O_A(PL^{-A})\) as before. No small signed total on this selected mask implies a lower bound on the unmasked Goldbach count.

### Related work

[Arneth's September v1](https://zenodo.org/records/23016171) gives a periodic comparison-weight cancellation but distinguishes it from the uncontrolled full physical prime-weighted discrepancy. [Pham's October v1](https://www.preprints.org/manuscript/202610.3061) instead studies a different sharp signed boundary component with partial controls. The present pairing uses a positive bounded label weight on the actual whole coefficient at the strictly subquarter cut; neither cancellation transfers to the whole unmasked problem.
