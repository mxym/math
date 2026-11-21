# Signed high \(h\)-Vaughan cancellation on a genuine rank-five tube

Keep the literal fixed-even-target equation
\[
                  n=sq=s r_1r_2r_3r_4r_5,\qquad
                  N-n=p h,\qquad N=2x,
\]
where \(s,r_1,\ldots,r_5,p\) are all true primes, \(n\in(x/2,x]\),
\((n,N)=1\), and \(h\) is the integer reflected quotient in the
Vaughan expansion. Put \(L=\log x\), \(\alpha=\log_xs\),
\(c=(1-\alpha)/2\), \(0<\eta<.002\) fixed, and use the actual balanced
outer \(p\)-band
\[
                          |\log_xp-(c-\eta)|<w=\eta/1000.
\]
The proof acts on actual adverse rank-five \(q\), not on a smooth-number
substitute. It uses Jain's recent preprint proposition as stated.
The new part is a **continuous joint tube** of modulus and source
factorizations in the genuinely high \(h\) branch. It does not claim
an arbitrary-modulus level on any one fixed factor profile.

Write \(\xi=\log_x(p d k)\) for the **literal** modulus exponent, with
\(.600\le\xi\le.623\). The short coefficient \(d\) is signed Möbius,
and \(k\) carries genuine \(\Lambda(k)\), with
\[
          x^{.012}<k<x^{.018},\qquad U_h=x^{.140+\eta},
                                       \quad V_h=x^{.003}.
\]
The true high product has \(d>U_h,k>V_h,d k\mid h\).
For the source shape let
\[
 u=(4\xi-1.75)/3,\qquad
 \ell=\xi+\lambda-u,\qquad b=1-\xi-\lambda,
\]
where \(\lambda>0\) is fixed below.
Use \(s\) at exponent center .12000, \(r_1\) at \(u-.12000\),
\(r_2,r_3\) at \(\ell/2-.0001,\ell/2+.0001\),
and \(r_4,r_5\) at \(b/2-.0002,b/2+.0002\).
Let \(\Psi_\xi(s,\mathbf r)\) be the product of six fixed smooth
nonnegative bumps in the differences of the actual label exponents
from those centers, each supported at radius \(\rho=\lambda/1000\)
and equal to 1 at radius \(\rho/2\). Each has variation depending
only on the fixed choices. The four large q labels have
disjoint exponent supports; \(s\) can overlap \(r_1\)'s
band, but the labelled \(s,r_1\) decomposition of their
product has multiplicity at most 2. The sum of the six
center exponents is exactly 1.

Consider the exact signed quantity
\[
 {\cal B}_N =
 \sum_{\substack{N-s r_1\cdots r_5=p d k j\\
        d>U_h,\ x^{.012}<k<x^{.018}\\
        .600\le\log_x(p d k)\le.623}}
        W_s(q)\frac{\log p}{\log((N-n)/p)}
                    \Psi_\xi(s,\mathbf r)\,\mu(d)\Lambda(k).
\tag{1}
\]
Here \(j\ge1\) is entirely free apart from the physical equation;
\(q=\prod_i r_i\), and all the earlier true prime, profile and central
constraints are kept. One may include fixed nonnegative smooth central
or label tests, or change the separated factors in the display, as
long as they have bounded log-power variation. The statement for
the exact Goldbach polynomial \(W_s\) in the display needs no sign
approximation of its weights.

**Result.** For each fixed \(A\), (1) is \(O_{A,\eta,\lambda}(xL^{-A})\)
uniformly in \(N\). This is genuinely beyond the earlier contiguous
\(h\)-Type-I cutoff in
[TrueRankFiveReflectedTypeI.md](TrueRankFiveReflectedTypeI.md):
on this tube, \(d k \ge x^{.1599+\eta}\), whereas that fixed-shape
cutoff was \(x^{.1532+\eta}\). The joint support is a real
higher branch of \(\mu_{>U_h}*\Lambda_{>V_h}*1\).
For the positive absolute counterpart of (1), a subfamily with
\(d,k\) both true primes already gives \(\gg_{\eta,\lambda}w x\)
for all sufficiently large fixed even targets. This is a genuine
signed cancellation, not small support. It does not control the
complement of the tube or the upper, balanced \(h\)-Type-II range.

The incoming q has all pairs of prime factors at exponent
\(\le.40001\) and all triples at exponent \(\ge.47999\);
its smallest prime is at exponent \(>.096\).
Its earlier \(\mu\)-only \(q\)-center from
[BalancedSemiprimeEvenRankNeck.md](BalancedSemiprimeEvenRankNeck.md)
is exactly \(-6\) on this geometry. Moreover
\(\log_x d\in[.142+\eta-w-\rho/2,\ .171+\eta+w+\rho/2]\),
so \(d>U_h\) holds with reserve and \(d k>D_*\) as asserted.
These comparisons are at true physical labels, not just at a
single nominal center.

## 1. The sixth-factor product input and its moving modulus

Use [Jain, Hexagon 2611.00530v1, Proposition 2,
primary PDF pp. 5–6](https://hexagonmath.org/pdf/2611.00530v1),
in its literal arbitrary independent triple-convolution form.
This is not Theorem 1 for smooth integers, nor the separate
arXiv Proposition 3 used for the earlier contiguous result.
Its three independent source groups in the present case are
\[
                  N_{\rm len}=s r_1,\qquad L_{\rm len}=r_2 r_3,
                         \qquad M_{\rm len}=r_4 r_5.
\]
Use the actual residue \(a_1=N=2x,a_2=1\), with source scale
\(X'=M_{\rm len}N_{\rm len}L_{\rm len}\asymp x\) on each input
box. Their exponents are \(u,\ell,b\) above. All complete input
slot coefficients are 1-bounded after fixed normalization and
bounded labelled multiplicity.

Write \(C_*>1\) for the unspecified absolute constant in the
source and set \(\lambda=\min(10^{-5},10^{-4}/(C_*+1))\).
The exact rails are as in
[IndependentCarrierHighModulusStrips.md](IndependentCarrierHighModulusStrips.md#1-source-constants-and-factor-lengths).
With \(\kappa=\lambda/8\), their key margins at the centers are
\[
\begin{array}{ll}
 b-\ell=(1.25-2\xi)/3-2\lambda,&
 \xi-(2u+3\ell-1)=(1.25-2\xi)/3-3\lambda,\\
 -(u+1/2-2\ell)=1.25-2\xi+2\lambda,&
 1/2-2u\ge .005333\ldots .
\end{array}
\]
The first two exceed .00130, and the third is at least .004.
The extra source cost \(C_*(u+\ell-\xi)=C_*\lambda\le10^{-4}\)
fits the complementary margin. Also \(u+\ell-\xi=\lambda\),
\(u+\ell=.62301\) or less, \(u>.21\), and \(\xi-b\ge .2\).
The true box widths and \(O(1/L)\) changes of scale preserve all
strict rails, including \(O(C_*\rho)\) in the last one.
The actual \(N=2x\) is permitted by the source's
\(|a_1|\le(X')^{1+\delta_{\rm prop}}\).

Although the shape depends on the candidate \(pdk\), it is not
inserted as a coupled source coefficient. Divide the modulus \(r=pdk\)
into dyads, then into relative \(O(L^{-K_0})\) boxes inside each;
for each choose its center \(\xi_0\) and the six independent bump
weights at \(\xi_0\). The parameter drift satisfies
\(|\xi-\xi_0|\ll L^{-K_0-1}\); by the smooth bumps this causes
\(O_\lambda(L^{-K_0})\) pointwise error on an outer enlargement
of the support of the same width. On real summands \(pdk\mid N-n\),
hence the full box errors, multiplied by original divisor/log weights,
are \(O_{\lambda,A}(xL^{-A})\) by ordinary global divisor moments;
each n has only bounded possible genuine labelled factorizations.
For reduced means one uses the harmonic sums over \(pdk\), also
costing fixed log powers. Thus there is no arithmetic floor loss
from a moving sharp source-factor wall. The \(s,p\) moving
band and central edges are separated exactly as in the Type I note:
on actual tuples count first \(n=sq\equiv N\bmod p\)
and then thin p-intervals; use a maximal n-prefix at each modulus
for the central edge. All selections comparing real \(p,s\) are
resolved before freezing the independent grouped coefficients.

The source subtracts low conductors. Choose \(D=L^B\) with
\(B\) arbitrarily large, and use the source bound on the
high-conductor component with the independent product boxes.
For each remaining nonprincipal character, fix the other actual
prime labels and use ordinary Siegel–Walfisz on, e.g., \(r_2\)
at exponent \(>.18\), including allowed smooth weights or
prefixes. Its inducing primitive character has conductor \(\le D\),
and its imprimitive unit exclusions remove only \(O(1)\) primes
at that scale. The factorwise N-unit mask has the same property.
There are \(O(D^2)\) possible characters for a given induction
modulus, and the dyadic reciprocal-\(\phi\) sum is \(O(1)\).
Taking the SW log reserve large proves arbitrary log
discrepancy with the **true reduced main**
\(\sum_{(n,r)=1} \Psi_{\xi}(s,\mathbf r)/\phi(r)\).
Use the original literal physical weights on the principal after
undoing the boxes, with the same controlled errors.

For (1), \(r=p e,\ e=d k\) contains at most one prime in the
specified p-band because \(p^2>r\), and \(e<p\).
The remaining signed coefficient of \(e\) is log-bounded via
\(\sum_{k\mid e}\Lambda(k)=\log e\); its tests of d and k are
inside that coefficient after fixing the genuine source and p
boxes. Thus the available absolute discrepancy at modulus r
suffices, with no claim of distribution for a correlated
arbitrary \(h\) weight.

## 2. Exact signed principal versus a large positive absolute portion

At fixed genuine \(n,p,k\) keep the masks on d and k as supplied by
the reduced mean. In particular \(E=Npn\) is the exact fixed
mask for d; the true \(p\) is prime to \(Nn\) on the support
and is larger than every \(n\) prime factor, and \(p\nmid e\).
With \(k=\ell_0^j\) as usual, the exact harmonic factor is
\[
 \frac1{\phi(p d k)}=
     \frac{1-\ell_0^{-1}1_{\ell_0\mid d}}
          {(p-1)\phi(d)\phi(k)} .
\tag{2}
\]
For fixed \(n,p,k\), the d-dependence in \(\Psi_\xi\) is a smooth
function of \(\log_x d\), with uniformly bounded total variation
at fixed \(\lambda\). The physical conditions on d, including
the \(.600,.623\) edges, are ordinary sharp interval tests.
Its lower endpoint is polynomial by the displayed \(d\)
range. The constant finite \(\mu/\phi\) prefix moment of
[UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md)
therefore gives \(O_A(L^{-A})\) with this tested weight.
For the local overlap in (2) write \(d=\ell_0 d'\).
Nonzero \(\mu(d)\) forces \((d',\ell_0)=1\);
the new interval of d' is still at scale
at least \(x^{.123}\) for sufficiently large \(x\).
The same coprime \(\mu/\phi\) moment applies with the
enlarged exact mask, including the sign of \(\mu(\ell_0 d')\).
The remaining \(\Lambda(k)/\phi(k)\) sums, p harmonic and label
weights cost only fixed log powers. This evaluates the entire
literal signed principal at arbitrary log accuracy. It proves (1).

To check that the tube is active on actual arithmetic support,
pick \(\xi_0=.610\) in its interior. Restrict the true \(s,r_i\)
to much narrower fixed exponent intervals at its centers,
and choose the last genuine prime in a fixed-ratio interval
making \(n\in(.7x,.8x)\). Ordinary prime PNT and the fixed
positive harmonic intervals prove that this supplies
\(\gg_\lambda x/L\) labelled n. Keep the genuine p-band,
of harmonic order w. Independently choose \(k\) a genuine prime
with exponent in \((.014,.016)\); its \(\Lambda(k)/\phi(k)\)
mass has order L. For each fixed such \(n,p,k\), choose
\(d\) a genuine prime in the allowed \(\xi\)-interval
of a sufficiently small fixed positive width about \(\xi_0\),
so every actual bump equals 1 there. Its harmonic mass is
bounded below by a positive constant depending on \(\lambda\).
All unit exclusions on these prime labels remove at most a
fixed number and do not affect the leading lower. The exact
congruence transfer of §1 applies to this nonnegative subfamily
as well: its modulus coefficient is still log-bounded, with
the prime \(d\) test now inside it. Its reduced mean is
\(\gg_{\eta,\lambda} w x\), and by the same dispersion so is
its actual sum for all sufficiently large even N.
On this subfamily the signed Möbius factor is exactly \(-1\);
the cancellation in (1) therefore requires other genuine
physical \(d\) factorizations. It does not merely suppress
a reference approximation that had no actual tuples.

The tube selection is essential. Its source exponents vary with
the modulus before separation; it is not an assertion for
all moduli of a fixed rank-five shape up to \(x^{.623}\).
Its high branch still has a free integer \(j\). The untouched
balanced \(h\)-Type-II correlations, plus the rest of the
high branch, can have either sign. No fixed-target estimate
for the whole prime-h population, nor strong Goldbach,
is inferred.

**Dated source and scope.** The [November 16 Hexagon v1 preprint](https://hexagonmath.org/2611.00530v1), Proposition 2, supplies the distribution input; this is an application of that proposition as stated, not an independent proof of it. The higher switched product levels here use a different varying source profile and the explicit Vaughan thresholds in this note, not an enlargement of the preceding fixed-shape theorem. Related [five-factor cutoff work by Arneth, September 28](https://zenodo.org/records/23016346) does not provide the signed arithmetic transfer for this joint tube.
