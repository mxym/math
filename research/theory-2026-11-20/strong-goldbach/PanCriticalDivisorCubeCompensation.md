# Compensating signed divisor cubes at the original square-root Pan split

Fix a sufficiently large even \(P\), \(L=\log P\), \(I=[P/3,2P/3]\), \(X=P/3\), the **original** \(Q_0=P^{1/2}L^{-20}\), and \(K=P^{.01}\). Use \(S(P)=2C_2\prod_{\ell\mid P,\,\ell>2}(\ell-1)/(\ell-2)\). On a true prime input \(p\in I\), \(a(p)=-\log p\). On a complementary \(r=P-p\) having at least two distinct prime factors,
\[
 a(r)=B(r):=-\sum_{d\mid r,\ d\le Q_0}\mu(d)\log d.
\]
We omit \(p\mid P\), an immaterial exceptional set; then both \(p,r\) are units at primes dividing \(P\), including for the asymmetric coefficient. This note estimates a **bounded nonnegative mask on the actual \((r,d)\) terms in this short-divisor expansion**. It does not replace \(B(r)\) by the estimated sector for arbitrary physical \(r\). No represented-target or Goldbach conclusion is asserted.

## 1. The configurations and their exact signs

Let \(h=15\) or \(16\), \(a=.505,\ b=.5051\). Mark squarefree \(q=\prod_{i=1}^h\ell_i\), \((q,P)=1\), \(u=\log q/L\in(a,b)\), with distinct ascending primes. Their shape variables \(t_i=\log\ell_i/\log q\) are in a fixed positive-volume cell \(\mathcal C_h\) of the simplex \(\sum t_i=1\) near \(1/h\), with separate label intervals. For definiteness choose centers \(c_{h,i}=1/h+(i-(h+1)/2)/10000\) and \(\mathcal C_h(w)=\{|t_i-c_{h,i}|<w\ \forall i\}\), \(0<w\le10^{-5}\). All prime exponents \(\log\ell_i/L\) are strictly between .030 and .036. Set
\[
 J_h=\int_{\mathcal C_h}\frac{dt_1\cdots dt_{h-1}}{t_1\cdots t_h}>0,\qquad H_h=J_h\log(b/a).
\]
One may choose the two widths to give \(J_{15}=J_{16}\): these integrals are continuous in \(w\), positive for \(w>0\), and tend to zero at zero, so choose half the smaller of the two values at \(10^{-5}\) and use the intermediate value theorem. No width or weight is selected using any prime data. Keep this choice when comparing the two signs.

For each marked \(q\mid r\), take all short divisors of the form \(d=e k\) with \(e\mid q,\ k\mid r,\ k\le K\). Since \(k<\min_{i}\ell_i\), it is coprime to \(q\), and \(e=(d,q)\) when \(\mu(d)\ne0\). Every proper \(e\mid q\) has \(e k<P^{.5051-.030+.010}<Q_0\), whereas \(qk>P^{.505}>Q_0\). Thus the sole missing vertex in the \(e\)-cube is \(q\). For each fixed \(k\), exactly
\[
 -\sum_{e\mid q,\ ek\le Q_0}\mu(ek)\log(ek)
     =\mu(q)\mu(k)\log(q k) .
 \tag{1}
\]
Indeed the complete alternating sum kills a constant and every linear log term when \(h\ge2\). Summing (1) over all marked \(q\mid r,\ k\mid r,\ k\in\mathcal K\subset[1,K]\) defines \(B_{h,\mathcal K}(r)\). For a fixed physical \((r,d)\), each \(q\) determines at most one \(k\). Since \(r\le P\) has at most 33 distinct primes above \(P^{.030}\), the multiplicity of every original divisor term is bounded by an absolute constant (for both \(h\)'s). A fixed rescaling therefore gives a true subweight \(\le1\) without changing any sign or size order. It is **not** claimed to be an indicator depending on \(r\) alone.

For \(T_h(\mathcal K)=\sum_{p\in I,\,p\ {\rm prime},\,p\nmid P}(\log p)B_{h,\mathcal K}(P-p)\), every actual joint divisibility has modulus \(qk\in(P^{.505},P^{.5151}]\), strictly supercritical by a **fixed power**, even for \(k=1\). With \(O_A=O_{A,\mathcal C_h}\), one has
\[
\begin{split}
 T_h(\{1\})&=(-1)^h X L\,J_h(b-a)+O_A(PL^{-A}),\\
 T_h([1,K])&=(-1)^{h+1}X S(P)H_h+O_A(PL^{-A}).
\end{split}\tag{2}
\]
Consequently the \(k>1\) terms compensate each parity's order \(P\log P\) term, leaving an explicitly **oppositely signed** order-\(PS(P)\) residue. With equal cell volumes, adding the two \(h\)'s cancels that residue also, to \(O_A(PL^{-A})\) for every \(A\). In the physical Pan sum \(a(p)a(r)\) one reverses the displayed signs due to \(a(p)=-\log p\).

There is certified mass well inside the upper end, not merely an upper bound on moduli. For any fixed \(0<g<j\le.01\), in \(\mathcal K=[P^g,P^j]\) one has \(T_h(\mathcal K)=O_A(PL^{-A})\), while the prime-only \(k\) in that same interval give
\[
 T_h(\mathcal K\cap\mathbb P)
  =(-1)^{h+1} XL J_h
       \big[(b-a)\log(j/g)+(j-g)\log(b/a)\big]+O_A(PL^{-A}).
 \tag{3}
\]
Thus composite \(k\) compensate the nonzero prime-only signed bulk within that very interval. For \(g=.009,\ j=.01\), **all** these moduli are in \((P^{.514},P^{.5151}]\).

## 2. The supercritical prime replacement is a signed theorem, not absolute BV

Use [Lichtman, *Primes in arithmetic progressions to large moduli, and Goldbach beyond the square-root barrier*, Theorem 1.7, equation (1.7)](https://arxiv.org/pdf/2309.08522). It applies to triply well-factorable 1-bounded convolution weights in the large residue range \(0<|A|<x^{1+\epsilon}\), at levels \(x^{153/256-\epsilon}\) using \(\theta=7/32\), with arbitrary logarithmic saving. We take \(A=P,\ x\asymp P\) (endpoints and partial summation within \(I\)). It is essential not to use an absolute error sum over all moduli near \(P^{.515}\); the imported theorem bounds **signed** sums with the verified weight.

Here are details verifying that its restrictive weight hypothesis applies. Partition the coordinate exponents \(x_i=\log\ell_i/L\in[.030,.036]\) into independent intervals of length \(\le\Delta=L^{-B_0}\). The log shape conditions and \(a<\sum x_i<b\) are a fixed finite system of linear inequalities in the \(x_i\)'s. Keep the rectangular boxes inside the region; the missed boxes are within \(O_h(\Delta)\) of its finitely many hyperplanes. Their product harmonic prime mass is \(O_h(\Delta)+O_{h,D}(L^{-D})\) for every fixed \(D\): hold all but a coordinate having a nonzero coefficient fixed, and apply the ordinary PNT Mertens estimate to that coordinate over an exponent interval of length \(O(\Delta)\), uniformly on this compact subset of positive exponents. The other coordinates have bounded prime harmonic mass. On the true boundary configurations, each \(qk\le 2P^{.5151}\) has at most \(O(P/(qk))\) integers of \(I\) in the required residue class. Even dropping primality there and all coefficient signs, \(\log p\log(qk)\le L^2\) and \(\sum_{k\le K}1/k\ll L\); the loss is \(O(P L^3(\Delta+O_D(L^{-D})))\). The same crude bound, with at most an extra polylog factor from \(qk/\phi(qk)\), handles the modeled boundary. No assumption on equidistribution in individual omitted moduli is made.

In each retained box every prime label lies in a **disjoint** size interval. In fact the relative centers are separated by \(10^{-4}\), their radii are at most \(10^{-5}\), and \(b-a=10^{-4}\), so even allowing \(u\) to vary the absolute exponent bands stay separated: \(a(10^{-4}-2\cdot10^{-5})>(b-a)\max_i(c_{h,i}+10^{-5})\). All prime factors of \(k\le P^{.01}\) are below all such intervals. Hence the factors \(\ell_1,\ldots,\ell_h,k\) of any integer in their convolution are **uniquely recovered**, even after grouping an arbitrary subset of labels together. Any product of a subset of their individual 1-bounded sequence factors, under Dirichlet convolution, is consequently still 1-bounded. The \(k\)-coefficient \(\mu(k)1_{\mathcal K}(k)\) may use any of the specified masks; units relative to \(P\) can be imposed separately in each factor. Split \(\log(qk)=\sum_i\log\ell_i+\log k\) into \(h+1\) terms, each scaled by \(L\) to keep every factor bounded by 1.

For **every** requested triple of capacities with product \(x^{153/256-\epsilon}\), \(\epsilon\) sufficiently small (or any fixed admissible level near \(P^{.59}\)), divide their logarithms by \(L\). Their sum is \(>.590\) for all large \(P\). The total log upper sizes of the box factors are \(<.516\) (the enlargement of the product window is \(O_h(\Delta)\)); each is \(\le.036+o(1)\). Pack the factors in any fixed order, closing a bin when its next factor would overflow. Each of the first two bins can lose at most \(.036+o(1)\) of its capacity, including if it was too small to take its first factor. As \(.516+2(.036)<.590\), the last bin can fit everything remaining. Empty groups give the unit sequence. The uniqueness just proved makes this a factorization into three 1-bounded sequences at **every** split, not merely one convenient split. This is precisely the required triple well-factorability.

There are \(O_h(L^{hB_0})\) fine boxes, a fixed polylog for the chosen precision. Take \(B_0\) and then the saving exponent in Lichtman's theorem large enough. The choice of \(A=P\) obeys the height restriction uniformly when \(x\in I\). Partial summation in the prime input converts the theorem for \(\pi\) to its log-weighted counterpart. The prime principal total on \(I\) is \(X+O_D(PL^{-D})\) by the ordinary PNT, with only a polylog cost in absolute main coefficients. The discarded central \(p\mid P\) cost at most \(P^{o(1)}\) in the physical sums via divisor bounds, and \((qk,P)=1\) must hold in every other counted term. We have obtained the exact useful replacement
\[
 T_h(\mathcal K)=(-1)^h X
    \sum_{\substack{q\ {\rm marked}\\(q,P)=1}}\frac1{\phi(q)}
    \sum_{\substack{k\in\mathcal K\\(k,P)=1}}
        \frac{\mu(k)\log(qk)}{\phi(k)}
       +O_A(PL^{-A}).                                                  \tag{4}
\]
No \(k\)-coprimality with \(q\) has been dropped: it is automatic by the size separation. This proof works with the exact sharp \(\mathcal K\) endpoints, since they are restrictions of a single independent sequence.

## 3. Evaluation and harmonic transport

Uniformly in the even target, for \(T=P^\delta\) with any fixed \(\delta>0\),
\[
 \sum_{k\le T,(k,P)=1}\frac{\mu(k)}{\phi(k)}=O_D(L^{-D}),\qquad
 \sum_{k\le T,(k,P)=1}\frac{\mu(k)\log k}{\phi(k)}
       =-S(P)+O_D(L^{-D}).
\]
The Euler product comparison with \(\zeta(1+s)^{-1}\), including its tilted uniform target-prime tail and elementary PNT partial summation, is given in [Global rough transfer §1 (2)](PanGlobalRoughTransfer.md). Taking differences at \(P^g,P^j\) gives zero in both sums to the same precision. For prime-only \(k\) the corresponding unsigned sums are \(\log(j/g)+O_D(L^{-D})\) and \((j-g)L+O_D(L^{-D})\) by PNT and the negligible reciprocal mass of divisors of \(P\) in this large-prime band.

Finally multivariate prime harmonic summation gives, to error \(O_D(L^{-D})\) for any \(D\),
\[
 \sum_{q\,{\rm marked}}\frac1{\phi(q)}=\int_{\mathcal C_h}\frac{dt_1\cdots dt_{h-1}}{\prod_i t_i}\int_a^b\frac{du}{u}=H_h,\qquad
 \sum_{q\,{\rm marked}}\frac{\log q}{L\phi(q)}=J_h(b-a).
\]
Indeed the product measure in the \(x_i\)'s is \(\prod dx_i/x_i=(du/u)\prod_i t_i^{-1}dt_1\cdots dt_{h-1}\). The same rectangular approximation and hyperplane boundary estimate as in §2 justify using the ordinary PNT with any required log precision. Omitting \(\ell_i\mid P\) or replacing \(1/(\ell_i-1)\) by \(1/\ell_i\) costs \(P^{-.030+o(1)}\). Formulae (2)–(3) follow from (4). The equal-volume choice matches the signed intensities as a function of \(u\), not by fitting an observed prime correlation.

**Limit.** This is compensation of a signed, explicitly truncated \((q,k,e)\) sector of the *original* cutoff at each individual \(P\), including nontrivial polynomially supercritical moduli; it is not a bound on all divisors \(d\mid r\) for these \(r\). External \(k>K\), configurations without the marked \(q\), and the Goldbach count remain outside (4). The weights may count a divisor term a bounded number of times as specified above. The factorable distribution input and large-residue exponent are Lichtman's; the present use is the signed incomplete Boolean-cube extraction and equal harmonic transport. No priority claim for general factorable-modulus cancellation is made.

## Related work and scope

[Arneth's October work](https://zenodo.org/records/23504447) considers fixed-target signed Möbius–prime reassembly; [Pham's October v1](https://www.preprints.org/manuscript/202610.3061) studies mixed rough and signed boundary components; the [Li–Liu formalization's distribution chapter](https://subfish-zhou.github.io/goldbach-lean/blueprint/chap-foundations.html) distinguishes its Pan-convolution and Fouvry factorable inputs. Here the exact extraction serves a different, bounded divisor-term mask, with a macroscopic residue and provably triply well-factorable coefficient at the polynomially supercritical moduli. It supplies no assertion about an arbitrary outside mask or the total residual.
