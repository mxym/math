# True LCM sharing and cross-colour zeros do not improve the leading square constant under unsigned support certification

Follow-up to [the P3 geometric safe-shape obstruction](PrimeOppositeP3SafeShapeBarrier.md). Written research note, 2026-11-24. This extends the earlier result from a sufficient exponent-sum rectangle test to a true arithmetic LCM test on arbitrary divisor-downward monomial supports. It is not a P3 estimate and does not rule out signed cancellations among bad terms.

## Statement

Work at \(N=2^k\), \(L=\log N\), a true odd marked prime \(q\) with \(t=\log q/L\in[.20,.23]+o(1)\), and cofactor sieving cutoff \(z=N^\mu\), \(.05\le\mu\le.07\) fixed. Put
\[
 \mathcal D_t=\{(u,v)\ge0:u+v\le .5-t
                \ \text{or}\ u+3t+\tfrac52v\le1\}.
\]
These are the enlarged affine and Poisson–Weil sufficient regions without shaves. Consider any normalized real Selberg square \(F^2\) in true labelled divisibility variables \(r\mid N-qj,\ s\mid j\), with \(F(0)=1\) at the fully sifted state and an allowed squarefree, divisor-downward monomial family \(\Lambda_{N,q}\). Here “downward” means that deleting any prime from either label leaves the pair in the allowed family, not that \(\Lambda_{N,q}\) is cut out by an angular shape. The family can vary arbitrarily with \(q,N\). The p-label may use any primes except \(q\); the j-label is limited to true sieve primes \(\ell<z\), excluding \(q\). At 2 keep only the common parity test. Consider exact-arithmetic certification that each *compatible* generator pair has its true LCM exponents inside \(\mathcal D_t\). Compatible means the two colours do not assign an odd prime to both integers, which would be exactly impossible because \(p+qj=N\). Shared primes of the same colour are allowed and give exactly the corresponding LCM saving. A raw monomial with an internal colour conflict is identically zero and may be removed. Assume all relevant exponent coordinates lie in a fixed box \([0,C]^2\); for the exact certification this is automatic because each compatible monomial self-pairs at its own exponents.

This certification cannot lower the leading normalized coefficient below \(1/(4I_{\mathrm{aff}}(t,\mu))\), where
\[
 I_{\mathrm{aff}}(t,\mu)=\int_0^\infty ((.5-t)/2-y)_+\rho(y/\mu)\,dy.
\]
The same holds if the compatible, individually unsafe pairs have vanishing *normalized harmonic product mass*, precisely as measured below, rather than none. In particular any fixed leading gain forces a positive limiting mass of disjoint, CRT-compatible, individually unsafe pairs. It would require signed control of a genuinely non-negligible set, not merely improving estimates for a few overlapping exceptional products.

## Proof

Put \(Z=L/(\log L)^2\), \(c_Z=\prod_{\ell\le Z}(1-1/\ell)\). In the complete local CRT model, condition on avoiding both roots at all primes \(\le Z\); for a lower bound on the best possible square main term this is legitimate because the square is nonnegative. Its probability is \(V_0=(S_N+o(1))c_Z^2\). On this event, raw monomials using a prime \(\ell\le Z\) vanish. Restrict the allowed family to the remaining terms, all primes \(>Z\). This keeps the family divisor-downward and the polynomial normalized. Remove the inert p-variable at \(q\) if present; its event is identically zero. The j cutoff never reaches \(q\). These removals respect true affine congruences before any asymptotic approximation.

For an index \(a=(r,s)\) in the remaining family, let \(w(a)=\prod_{\ell\mid rs}(\ell-1)^{-1}\). The squarefree pair has \(r,s\) coprime because of the genuine colour-conflict rule. Define a finite, not necessarily probability, measure
\[
 \nu_{N,q}=\frac1{c_Z^2L^2}
             \sum_{(r,s)\in\Lambda_{N,q}\,:\,P^-(rs)>Z}
             w(r,s)\,\delta_{(\log r/L,\log s/L)}.
\]
The convention allows \(rs=1\). The normalized harmonic product mass refers to the analogous sum over ordered pairs, divided by \((c_Z^2 L^2)^2\). The unfiltered measure, dropping coprimality and working in \([0,C]^2\), is the product of the unrestricted squarefree prime-restricted \(w\) measure and the \(N^\mu\)-smooth version; its weak limit is
\[
    d\gamma(x,y)=dx\,\rho(y/\mu)\,dy .
\]
This is the harmonic convolution and fixed-size inclusion-exclusion calculation in §4 of [the tilted Selberg proof](DyadicTiltedTwoFormShortCutoff.md): uniformly the unrestricted mass up to \(N^x\) is \(c_Z Lx+O((\log Z)^{O(1)})\); deleting primes \(\ge N^\mu\) and using harmonic Mertens on their fixed exponent intervals gives the Dickman cumulative law. Omitting or allowing the inert prime \(q\) in this **comparison** measure has \(o(1)\) normalized effect. The measures are uniformly bounded, and any subsequential weak limit \(\nu\) has \(\nu\le\gamma\) (compare each finite continuous nonnegative test). This step allows arbitrary irregular or q-dependent supports.

Most importantly, *all shared primes between two raw monomials together* give \(o(1)\) normalized pair mass. To see this, for each fixed \(\ell>Z\), drop all restrictions except squarefreeness and exponents \(\le C\). The mass \(\sum_a w(a)\) of monomials containing \(\ell\) in either colour is bounded by \(O_C(L^2/(\ell-1))\), by deleting \(\ell\), bounding the two remaining harmonic sums by \(O_C(L)\) each, and summing the two colour choices. The unrestricted bound \(O_C(L)\) also follows immediately from \(\prod_{p\le N^C}(1+1/(p-1))\ll_C L\). Therefore the upper after normalization is
\[
 \sum_{\ell>Z}\left(\frac{O_C(L^2/(\ell-1))}{c_Z^2 L^2}\right)^2
 \ll_C (\log Z)^4\!\sum_{\ell>Z}(\ell-1)^{-2}=o(1).
\]
In particular, deleting all such pairs loses vanishing mass uniformly even for adversarially chosen supports. A disjoint pair has no cross-colour obstruction and its actual LCM exponents are its coordinatewise sum.

Take an arbitrary subsequence, pass further to \(t\to t_*\) and \(\nu_{N,q}\Rightarrow\nu\). If \(a,b\in\operatorname{supp}\nu\) had \(a+b\notin\mathcal D_{t_*}\), take open neighborhoods \(U,V\) so small that all their sums stay outside \(\mathcal D_{t}\) for all sufficiently late indices. This is possible because both linear inequalities defining the complement are then strict. Portmanteau gives positive liminf for both masses. Their harmonic product has positive liminf as well; the preceding overlap bound leaves a positive mass of disjoint, truly compatible, unsafe pairs, contrary to the certificate even in its vanishing-exception version. Thus
\[
   \operatorname{supp}\nu+\operatorname{supp}\nu\subset\mathcal D_{t_*}.
\]
The coordinatewise downward hull \(\mathcal A\) of this compact support is closed, bounded, and retains the same sum property because \(\mathcal D_{t_*}\) is downward. Since \(\nu\le\gamma\), the geometric safe-shape theorem yields
\[
  \nu([0,C]^2)\le\gamma(\mathcal A)\le I_{\mathrm{aff}}(t_*,\mu).
\]
This bounds the limsup normalized harmonic mass and does not require any angular limit of the supports themselves. The conclusion with a fixed strict gain has a uniform positive-mass contrapositive by the same compactness argument: along any sequence with such gain and vanishing mass of disjoint unsafe pairs it would produce the asserted contradiction.

To identify the coefficient, retain the conditioned model and express the raw polynomial in the normalized centred indicator product basis. Divisor-downward closure means the basis change remains within the given family. At a large prime \(\ell>Z\) the local two-colour covariance matrix has diagonal 1 and off-diagonal \(-1/(\ell-1)\), because the two actual roots are mutually exclusive. Distinct unlabelled prime supports give orthogonal blocks. The covariance blocks of the allowed colour assignments are principal submatrices of tensor products of these local matrices. All their eigenvalues are \(1+o(1)\) uniformly: for a support of product \(\le N^{2C}\), the reciprocal sum of its primes above \(Z\) is \(o(1)\) by splitting at \(L(\log L)^2\) and using harmonic Mertens on the shorter low range, then counting the possible prime factors above the split. As in the tilted proof, writing \(g_a\) for the value of the normalized centred basis vector at the all-zero-hit input, one has \(g_a^2=w(a)\). The Cauchy lower bound for every conditioned normalized polynomial is therefore
\[
 \mathbf E_{\mathrm{CRT}}F^2
    \ge \frac{(1-o(1))V_0}
              {\sum_{a\in\Lambda_{N,q}, P^-(rs)>Z}g_a^2}
    \ge\frac{(1-o(1))S_N}{L^2 I_{\mathrm{aff}}(t,\mu)} .
\]
The same density normalization as in the affine/tilted note yields the claimed normalized constant \(1/(4I_{\mathrm{aff}})\). The absolute Poisson remainder is not being estimated anew. This is a theorem about an obstruction to this particular evaluation strategy; it is not a lower bound for true joint prime counts.

For a genuine escape within a single signed square, one must control the aggregate residue of a positive harmonic product mass of disjoint terms beyond the currently proved remainder regions, allow aggregate cancellation before support certification, or leave the divisor-downward square scheme. No conclusion is drawn for a polynomial whose unsafe expanded coefficients collectively cancel, or for a new analytic treatment of those remainders.