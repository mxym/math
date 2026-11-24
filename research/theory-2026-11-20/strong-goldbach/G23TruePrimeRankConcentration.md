# Actual G23 prime-variance concentration on the typical rough k rank

Written research note, 2026-11-24. No replacement of genuine primes or marks. Write \(P=2^j\), \(L=\log P\), \(z=\exp(L^{.24})\), \(\kappa_z=\prod_{\ell\le z}(1-1/\ell)\asymp L^{-.24}\). \(B_C\) is the actual weighted prime-reflection vector of the [true prime-reflection layer](G23TruePrimeReflectionLayer.md), \(A_C=H_C-B_C\) the actual rough signed Liouville vector, and \(\Pi\) the angular-bin projection on the exact moving interior from the [actual angular projection note](G23ActualAngularProjectionCompensation.md). All norms below have weight \(kR_z(k)\); \(B_\perp=(1-\Pi)B_C\) may be restricted to that interior, or defined globally with the projection set to zero on the negligible two physical prime-energy edges.

**Result.** For every fixed \(\epsilon>0\), both the actual prime vector and its residual satisfy
\[
 \sum_{\substack{k\\|\Omega(k)-.76\log L|>\epsilon\log L}}
  kR_z(k)\bigl(|B_C(k)|^2+|B_\perp(k)|^2\bigr)
   =o(P^2\kappa_z/L^3).
\]
The proof is for each sufficiently large power of 2, not an average over P and not only a projection statement. It does not give a lower bound for residual energy or claim concentration of the full Liouville norm or its matched mixed inner product on the same thin rank interval.

## Common arithmetic and squareful/primitive deletion

Partition k into dyadic physical blocks \(k\asymp K\), \(U=P/K\); on actual pairs \(p,p'\asymp_J U\), both \(\log U\) and \(\log K\) are bounded below by a fixed positive multiple of L and above by \(O(L)\), and \(K\gg_J U\) by the true slope upper bound. There are \(O(L)\) blocks. The prime-square diagonal has total \(O(P^{2-\sigma})\) from the true prime-layer note. A rough k divisible by a prime square has \(O(K/z)\) possibilities in a block by summing \(O(K/\ell^2)\) over \(\ell>z\). Its total supreme weighted row bound, even with integer slope pairs, is \(O(P^2/z)\) per block. Therefore it suffices to treat squarefree k; in particular \(\Omega=\omega\).

Another independently negligible portion is any offdiagonal row with \((k,pp'(p-p'))>1\). If a prime \(\ell\mid k,p-p'\), then \(\ell>z\) and the nonzero difference forces \(\ell\ll_J U\). There are \(O(U^2/\ell)\) integer slope pairs and \(O(K/\ell)\) integer k, including the floors since \(K\gg U\); after the weight K and summing \(\ell\) this is \(O(P^2/z)\) per block. For \(p\mid k\) or \(p'\mid k\) the same trivial count gives \(O(P^2/U)\) per block, using \(p\asymp_J U\) and \(K\gg U\). These absolute deletions hold for both actual prime square and actual mixed rows. For the mixed row, the two reflected arguments are automatically coprime: their gcd divides \(p-p'\) on target units, while the first argument is a true prime \(\asymp P\). Thus the prime-square variance can equivalently be tested on primitive offdiagonal triples, with its exact angular projection norm subtracted, up to little-oh of the true prime scale.

We use the elementary Selberg square and the genuine singular-factor prime-slope average of G23TruePrimeReflectionLayer.md. For fixed distinct slopes, when a short divisor d of k is selected, switch to the literal progression \(k=dt\) of length \(O_J(K/d)\). Primes \(\ell\le W\) not dividing d (sieve cutoff \(W<P^\sigma\)) have the exact affine roots in t. At \(\ell\mid d\), both reflected affine values are the nonzero constant P modulo \(\ell\); d is odd and \(\ell>z\). Disappearing roots change Euler factors by at most \(\prod_{\ell\mid d}(1+O(1/\ell))=1+o(1)\), uniformly since \(\sum_{\ell\mid d}1/\ell\ll L/z\). At 2 all applicable roots coincide, and local inadmissibility at 3 is truly empty and may be deleted. Remaining collision factors are bounded by \(S(|p-p'|)=\prod_{\ell\mid p-p',\ell\ge5}(1+C/\ell)\). The true prime pair sum of S is \(O_{J,\sigma}(U^2/L^2)\), using Brun–Titchmarsh in reduced progressions for its small-divisor expansion and the elementary reciprocal tail for larger divisors, as in that note. Sieve divisor level R and sufficiently small W with \(\log W\le c_0\log R\) give upper main term of length times the local Euler survival product (denominator Markov proof). The full CRT floor is \(R^4 L^{O(1)}\) in each fixed tuple: at most \(R^2\) ordered weight pairs, \(\nu([a,b])\le[a,b]\le R^2\), coefficients bounded by inverse Euler product, at most a fixed power of L in all the surviving patterns below.

## Low rank

Let \(r=\lfloor c\log L\rfloor\) for fixed \(0<c<.76\). In each squarefree k of rank \(\le r\), take its actual largest prime t and write \(k=dt\). Then \(d\le (C_J K)^{1-1/r}\), \(d\) is squarefree and z-rough, and \(\omega(d)\le r-1\). Allow all such d in the upper bound. Since the largest t is \(\gg K^{1/r}\), choose \(R=P^{1/(64r)}\) and \(W=P^{c_*/r}\) with sufficiently small fixed \(c_*>0\); all tested true primes (t and both reflections) exceed W. Also \(W>z\) for large P. On the t lattice sieve the three prime forms \(t,P-pdt,P-p'dt\) throughout W. At ordinary \(\ell\) there are three roots, with the exact bounded collision factor already stated, so the true count at fixed \(p,p',d\) is
\[
 \ll \frac{K}{d}\frac{r^3}{L^3}S(|p-p'|)+P^{1/(16r)}L^{O(1)} .
\]
The main uses Mertens at the true \(\log W=c_*L/r\), not at L. If \(\mathscr H_r\) denotes the sum of \(1/d\) over the allowed d, then
\[
 \mathscr H_r\le\sum_{i=0}^{r-1}\frac{M_z^i}{i!},\qquad
 M_z=\sum_{z<\ell\le C_JP}\ell^{-1}=(.76+o(1))\log L.
\]
Here the unordered divisor is squarefree, so the factorial is legitimate. Stirling and \(c<.76\) give \(\mathscr H_r\le L^{F(c)+o(1)}\), \(F(c)=c(1+\log(.76/c))<.76\). Multiplying by K for the weight and summing genuine slopes gives per block \(O(P^2 r^3\mathscr H_r/L^5)\). Floors cost at most \(P^2 K^{-1/r}P^{1/(16r)}L^{O(1)}\), since there are \(O(K^{1-1/r})\) D-integers and \(KU=P\); \(K\gg P^{1/2}\) turns this into \(P^2\exp(-c'L/r)\) times log powers. Across \(O(L)\) blocks the total main divided by \(P^2\kappa_z/L^3\) is \(O(r^3\mathscr H_r/(L\kappa_z))=o(1)\).

For the projected B component, known exact angular-bin first moments imply \(0\le\Pi B_C(k)\ll P/(kL^2)\) on the bins, zero off them; use \(B_C\le B_1\). The true low-rank k count in one block is \(\ll K(r/L)\mathscr H_r\): for each d the prime t is at scale \(K/d\ge K^{1/r}/O(1)\) and ordinary PNT upper gives \(\ll Kr/(dL)\). Thus over the full low tail
\(\sum R_z(k)/k\ll r\mathscr H_r\), apart from a squareful contribution \(O(L/z)\), and the projected prime energy is \(\ll P^2r\mathscr H_r/L^4=o(P^2\kappa_z/L^3)\). The inequality \(|B_\perp|^2\le2|B_C|^2+2|\Pi B_C|^2\) now gives the stated residual result.

## High rank

Fix \(c_+>.76\), and let \(s_0=\lceil c_+\log L\rceil\). Choose a fixed \(a>0\) with \(a<\min(c_+/8,(c_+-.76)/2)\), \(r=\lfloor a\log L\rfloor\). If squarefree \(k\asymp K\) has \(s=\omega(k)\ge s_0\), the log of the product of a uniformly chosen r-subset of its true prime factors has expectation \(r\log k/s\le \frac18\log(C_JK)\). Markov proves that at least half of its \(\binom{s}{r}\) subsets have product \(d\le(C_JK)^{1/4}\). Thus weight each true selected d by \(2/\binom{s_0}{r}\), which pointwise majorizes the high-rank indicator. There is no multiplicity assumption on real prime pairs.

Now fix one such d with exactly r distinct factors all >z, switch \(k=dt\), and retain \(R_z(t)=1\) exactly as a sieve condition, since d already rough. Use fixed small polynomial cutoff with \(R=P^{1/100}\) as in the prime-layer note; this applies one rough-u root for t up to z and two prime-form roots through W. In particular \(\kappa_z\) is retained, not lost by opening the divisor. The fixed pair count is \(\ll (K/d)\kappa_z S/L^2+P^{.04+o(1)}\). With the slope average, weight K, and subset divisor normalization above, the high-tail prime energy is bounded by the natural prime scale times
\[
 O\left(\frac{M_z^r/r!}{\binom{s_0}{r}}\right)
 \le O\left(\left(\frac{M_z}{s_0-r+1}\right)^r\right)
 \ll L^{-\eta}
\]
for a fixed \(\eta>0\) because \(c_+-a>.76\). The total floors cost \(\ll P^2 K^{-3/4}P^{.04+o(1)}\) per block, from at most \(O(K^{1/4})\) d-integers, even ignoring the favorable normalization. For projected prime energy, the same subset certificate and integer one-root upper for rough t yield high-rank k count in each block \(\ll K\kappa_z L^{-\eta}+P^{.04+o(1)}K^{1/4}\). Combining the uniform projected bound with these counts gives projected high-rank energy \(o(P^2\kappa_z/L^3)\).

## Scope of the mixed bound

The low-rank proof applied to one true prime reflection and one y-rough reflection changes the three-prime factor $(r/L)^3$ to \(V_y(P)(r/L)^2\), where \(V_y(P)\asymp L^{-\delta}\) for powers of 2. After slope and dyadic summation the upper relative to the prime scale is \(O(V_y r^2\mathscr H_r/\kappa_z)\), which need not go to zero. There is no claim that low-rank k can be deleted from the genuine signed matching inner product. For high k rank the analogous true one-prime/rough sieve yields the natural mixed unsigned scale \(P^2\kappa_z V_y/L^2\) times the subset ratio. It is little-oh of prime scale only for a large enough rank threshold, e.g. \(c_+=9,a=1\) makes \(\eta>1\). Neither the low nor high prime square bound estimates the remaining genuine primitive variance at the typical rank or gives a cancellation statement for its signed mixed pairing.
