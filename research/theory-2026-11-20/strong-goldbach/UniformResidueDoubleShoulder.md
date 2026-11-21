# A genuine super-square-root reflected shoulder via Maynard's uniform-residue Type II estimate

Use the actual expanded double row in [ReverseVaughanDoubleResidual.md](ReverseVaughanDoubleResidual.md), with the fixed cuts \(U=x^{.454},V=x^{.004},Q=x^{.466},U_q=x^{.070},V_q=x^{.010},E=x^{.080}\). In particular the physical equation is
\[
                d\ell h+s r k j=N,\qquad s r k j\in I,\quad (s r k j,N)=1 ,
\]
\(s\sim S=x^\alpha\), \(.10\le\alpha\le.14\), is an actual prime, and the signed weight is
\[
 \mu(d)\Lambda(\ell)\mu(r)\Lambda(k)\,
       \kappa_s W_s(rkj)/\log(rkj).
\tag{1}
\]
The following is a direct true-prime/true-Möbius application of [Maynard, *Primes in arithmetic progressions to large moduli III*, Proposition 5.3](https://ora.ox.ac.uk/objects/uuid%3Ada3b7279-d413-4ab1-962e-afa5d67507c2/files/s6w924c97m), not the more restrictive true-prime theorem and not its fixed small-residue counterpart.

Take any dyads for the actual labels \(s,r,k,j,d,\ell\); additional ordinary intervals on these labels or on \(A=s r k\) are allowed. Let the dyadic exponents of \(d,\ell\) be \(u,v\), so the reflected product \(a=d\ell\) has exponent \(c=u+v\). Assume \(c>1/2\), and suppose a subset of \(\{s,r,k,j\}\) has product exponent \(\beta\) satisfying the three strict inequalities
\[
        7u+12v<4,\qquad
        u+2(c-1/2)<\beta,\qquad \beta<1-u.
\tag{2}
\]
Assume a fixed positive margin in each inequality. For definiteness the subset contains at least one of the labels \(r,k,j\) of a fixed polynomial length; the last two inequalities force this automatically in our band. Then the entire signed sum (1) on these boxes is \(O_D(x(\log x)^{-D})\) for every \(D>0\), uniformly in \(N\) and arbitrary log-bounded \(\kappa_s\). The genuine \(\mu(r)\), \(\Lambda(k)\) may independently be replaced by their exact centered versions \(\mu(r)-P_B(r)\), \(\Lambda(k)-H_B(k)\) from [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md), at the same estimate.

This is a broader two-way support criterion (a genuine modulus factorization \(d,\ell\) and a genuine quotient-side convolution group); it is not a restored distribution theorem over arbitrary \(a\). For example, with an independent fixed small width \(10^{-4}\) about each of
\[
  u=.470,\quad v=.054,\quad \log_x r=.525,\quad \log_x k=.080
\tag{3}
\]
the group \(r\) alone has exponent \(\beta\) near .525, and the full physical \(j\) stays at its automatic central scale. All (2) hold, with the original \(A=s r k\) at exponents roughly \(.705\) through \(.745\). Specifically the three respective center margins are \(.062,.007,.005\), unaffected by the indicated small widths; \(\alpha\) need not be fixed in the band for these margins. This lies far outside the previous near-diagonal reciprocal seam or convenient \(A\)-column families. There are also genuinely unstructured \(A\sim x^{.525}\) examples, choosing the group \(s r k\) and free complement \(j\), provided the independent factor scales realize that product; no finer factorization of \(r\) is necessary. Only the relevant box, not the whole reflected range at fixed \(A\), is asserted here.

## 1. True grouped convolution and SW

Keep the literal \(N\)-unit support by requiring each label \(s,r,k,j\) to be coprime to \(N\). Every eligible modulus \(d\ell\mid N-srkj\) is coprime to \(N\), so \(N\bmod d\ell\) is reduced. The independent \(r>U_q,k>V_q\) imply \(r k>E\) with our fixed \(E\); in particular no \(d\)-dyad-dependent reverse cutoff is being suppressed. All late cuts on \(d,\ell,d\ell\) can be retained as outer cuts on the two source modulus factors.

On the physical band, write \(n=s r k j\in I\). For the original \(1/\log(r k j)\) use its finite geometric expansion in \(\log(n/x)/\log(x/s)\), uniformly log-small to any prescribed reserve. The result is a finite sum of products of a log-power bounded \(s\)-weight and a smooth function of \(n/x\); the same applies to the exact \(W_s\) as in the previous notes. The physical error is bounded by arbitrary log savings times the global divisor moments of the actual \(n,N-n\). For the sharp product interval \(n\in I\) and the smooth test, use the relative log meshes and physical divisor moment edge argument in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md): fine rectangular boxes of the four \(n\)-factors, a bounded number of \(n\)-edge strips of size \(O(xL^{-F})\), and only a log-power number of true independent boxes. A factor of small physical size can simply be cut into singletons when the mesh resolution requires it; the number of subintervals is still log-power bounded. A sharp interval on \(A=s r k\) is handled by retaining only fine boxes wholly on the chosen side of each boundary. The discarded or added points have \(|s e/A_0-1|\ll L^{-F}\) for one endpoint \(A_0\), where \(e=rk\). For fixed \(e\asymp A_0/S\), the \(s\)-interval in this strip has \(O(SL^{-F}+1)\) integers and the possible physical \(j\) have \(O(x/A_0)\) values. Summing over \(e\) gives \(O(x(L^{-F}+1/S))\) contaminated \(n\) before weighting, enough by the same divisor moments. Principal terms on these edges are similarly bounded by harmonic divisor weights. Thus sharp \(A\) cuts are enforced without twisting the sequence declared SW; inside the accepted boxes all original label intervals remain independent.

In an accepted rectangular box, group the chosen subset into \(\alpha_b\) at the source convention \(b\sim x^\beta\), and the complementary labels into \(\gamma_a\) at length \(\asymp x^{1-\beta}\). Dyadize those grouped products as needed. Both are divisor-bounded after dividing by a fixed log power, since they sum only a fixed number of actual factorizations. The genuine \(r\)-coefficient \(\mu\), the \(k\)-coefficient \(\Lambda\), and the free \(j\)-coefficient each satisfy the source SW condition (4.1) on polynomially long dyadic scales, including independent auxiliary coprimality. For \(\Lambda\) this is ordinary SW with the removed prime powers belonging to primes in the auxiliary mask, at a cost \(O(\tau(d_0)L^C)\). The free case is inclusion--exclusion over divisors of the mask and ordinary AP counting. For \(\mu\) expand the auxiliary mask first. Its divisor \(f>Y^{1/4}\) costs \(O(\tau(d_0)(Y^{3/4}+1))\) at factor length \(Y\). For smaller squarefree \(f\), use \(\mu(fw)=\mu(f)\mu(w)1_{(w,f)=1}\) and the standard coprime \(\mu\chi\) SW with its short mask \(f\), as detailed in §2.3 of [WholeReverseColumns.md](WholeReverseColumns.md) without needing a rough cutoff here. The physical \(N\)-unit mask can be combined with this procedure without a \(\tau(N)\) loss: after the auxiliary \(f\)-split, \((w,N f)=1\) is a mask of polynomial size, and the uniform coprime SW follows by its exact smooth-divisor convolution and Rankin tail, as in §1 of [ReverseVaughanDoubleResidual.md](ReverseVaughanDoubleResidual.md). At large moduli, beyond a suitable log power, trivial reduced progression counts suffice for these 1- or log-bounded primitive factors.

The same SW property holds for either indicated centered factor on any polynomially long interval. Indeed unfold \(P_B\) or \(H_B\) with \(t\ll Y/B\), where \(B=x^{1/2+\delta_0}\) and \(\delta_0>0\) is fixed. For fixed \(t\) the long free \(b\) has an ordinary interval and a reduced class (or there is no term). With the unit masks use exact inclusion--exclusion; the total maximal SW discrepancy of this long free coefficient is
\[
 O\left(L^C \tau(N)\tau(d_0)\sum_{t\ll Y/B}\tau(t)^C\right)
 \ll \tau(d_0) Y x^{-c_1}
\]
for some fixed \(c_1>0\); a free \(\log b\) costs a log by partial summation. This bound in fact works for any progression modulus, by the per-interval floor error and reduced class averaging. The use of \(\tau(N)=x^{o(1)}\) is paid by the genuine power reserve \(1/B\). If \(Y<B/2\), the marked pieces are absent. Outer masks and independent dyadic intervals introduce no other loss.

For the selected group \(\alpha_b\), fix its other labels and apply one of these SW estimates to a polynomial-length \(r,k\), or \(j\) inside it, with the reduced residue adjusted by the product of labels already fixed. If that product is nonunit, both actual and reduced mean terms are zero. The interval constraints on its selected factor, including a grouped dyad, are ordinary intervals. Summing the fixed labels costs only their product of lengths and fixed log powers. This verifies grouped SW at \(x^\beta\), with the required auxiliary factor. It makes no SW assumption on arbitrary \(\kappa_s\), and does not require SW of the complementary group.

## 2. Literal use of the common-residue theorem

In Proposition 5.3 take
\[
 Q_1\asymp x^u\ \text{on }d,\quad Q_2\asymp x^v\ \text{on }\ell,\quad
 Q_1Q_2=x^{1/2+\delta'},\quad N_{\rm source}\asymp x^\beta.
\]
The four physical label dyads have product \(\asymp x\) on a nonempty central box, and the source \(N_{\rm source}M_{\rm source}\asymp x\) holds. A small fixed analytic \(\varepsilon\) fits the inequalities of the source because of (2); fixed-factor dyadic endpoint errors are \(o(1)\) in exponent and do not consume the margin. The proposition gives an absolute sum over \(d,\ell\), taking a common residue modulo \(d\) before the \(\ell\)-sum and allowing reduced residues modulo \(d\ell\) above it. We choose the common class \(N\bmod d\) and the actual residue \(N\bmod d\ell\) throughout. The source does not need any upper-size relation between the integer representative \(N=2x\) and the length of a single primitive factor. No \((d,\ell)=1\) assumption is used; they are the literal two modulus slots. Their independent absolute coefficient cost \(|\mu(d)\Lambda(\ell)|\le L\) is absorbed by its arbitrary log reserve. The result is the centered discrepancy for the actual convolution \(s r k j\), even when the original \(A=s r k\) is much larger than the reflected product.

For the resulting principal part fix the physical \(n=s r k j\) and then \(\ell=p^k\) with \((\ell,Nn)=1\). Over the surviving \(d\)-interval on its polynomial scale sum \(\mu(d)/\phi(d\ell)\) with \((d,Nn)=1\). The local overlap formula
\[
      \frac{\phi(d)\phi(\ell)}{\phi(d\ell)}
             =1-\frac1p 1_{p\mid d}
\]
reduces it to the two masked coprime harmonic Möbius tails with masks \(Nn\), \(Nnp\), as in [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md). They are arbitrary-log small uniformly. The remaining \(\ell\) weights sum harmonically, and the physical label masses have total \(O(xL^C)\) by divisor moments. Thus the principal part itself vanishes. This proves the asserted signed estimate, not just a bound for the discrepancy from an unevaluated mean.

The broad surviving region still includes literal boxes with no subset group of the required scale. For instance around \(s=.12,\ r=.28,\ k=.27,\ j=.33\), the groups nearest \(.52\) are built from \(.28+.27=.55\) or \(.12+.33=.45\), both outside \((.518,.530)\) at reflected \((u,v)=(.470,.054)\). The complement is not solved. The new estimates concern actual doubly signed terms, not a bound for the complete low semiprime weight or binary Goldbach.

The [AMRAL Goldbach series index](https://amral.evemisslab.com/en/links/#goldbach) describes a related Maynard III range audit for its switched Chen-type rows, and explicitly leaves a residual dispersion region. Its two detailed pages could not be retrieved for this comparison. [Chan's November preprint, Proposition 3.2](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also applies residue-uniform estimates with different sieve supports. The stated inequalities here are for the actual two-factor modulus of the reflected double Vaughan row and a subset of its original quotient variables; no absolute priority or claim about those other residuals is made.
