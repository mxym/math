# A growing small-cofactor rectangle in the actual double Möbius expansion

Let \(B,D>0\) and a compact interval \(J\subset(0,1)\) of positive length be fixed. Put \(L=\log N\), and prescribe any sufficiently large integer \(N\) with \(\operatorname{rad}(N)\leq L^B\). Uniformly for real \(1\leq H\leq L^D\), there exists \(\eta>0\), depending on the fixed parameters, such that
\[
 \sum_{1\leq a,b\leq H}(\log a)(\log b)\,
 \left|\sum_{\substack{a m+b n=N\\ a m\in NJ}}\mu(m)\mu(n)\right|
       \ll_{B,D,J} N L^{-\eta}.
 \tag{1}
\]
No target-unit restriction is needed in (1). If it is imposed, by retaining only \((am,N)=1\) in the inner sum, the right side can be improved to \(\varphi(N)L^{-\eta}\). The implied constants and the threshold can be ineffective. The absolute value is over each genuine affine Möbius sum, not over the individual integer rows.

To identify the rectangle precisely, the elementary Dirichlet identity \(\Lambda(x)=\sum_{a m=x}(\log a)\mu(m)\) implies the **literal** finite equality
\[
 \sum_{x\in NJ}\Lambda(x)\Lambda(N-x)
   =\sum_{a,b\geq1}(\log a)(\log b)
          \sum_{\substack{a m+b n=N\\ a m\in NJ}}\mu(m)\mu(n).
 \tag{2}
\]
Thus (1) pays the simultaneous \(a,b\leq L^D\) rectangle of (2) at \(o(N)\), even with arbitrary bounded extra coefficients on its outer cells. It does not evaluate the other cells, supply a main term for (2), or prove a prime-pair lower bound. The \(a,b\) range is a growing power of **\(\log N\)**, not of \(N\).

The argument improves two separate pieces of the companion [affine reflected proof](Proof.md): a moving middle-prime interval on the genuine logarithmic derivative, and a bounded first-success replacement of the weight-removal variance. The full-target mean-square comparison is still the [projected JLL comparison](../target_slope_switch/Proof.md) with the one-prime-slot and rational-phase support revisions of §1 of the companion. We give the needed quantitative checks rather than substitute a moving parameter into a fixed-parameter statement.

## 1. Moving packet length without a moving graph parameter

Use the notation of §1 of the companion, with target \(P\), \(L=\log P\) (we will also apply this at \(P=N/d\)). It suffices that both numeric factor scales \(M_1,M_2\) satisfy
\[
  \log M_i\geq \tfrac14 L^{.99},\qquad
  M_1M_2\asymp_J P .
  \tag{3}
\]
The one literal prime slot, all units modulo \(P\), and avoidance of the chosen operator bank remain exact. Additional prime omissions in the \(f=\mu\) or \(\lambda\) slot may be any set of primes below \(\exp(2L^{.2})\), as before. For these packets (4) of the companion still gives \(O(P L^{-F})\) for every requested fixed \(F\). In particular \(A_0,K\) and all log frequency cutoffs remain fixed as \(P\to\infty\).

**Minor frame averaging.** The first-coordinate and second-coordinate physical frame scales are \(U=C M_1,\ V=M_2\), where \(C\) is the shared-label product scale times the selected tag scale. Reorder the two factor slots so that \(M_1\leq M_2\). Then \(\log C=O_K(L^{.21})\), \(U/V\leq C\), and \(\log U,\log V\geq \tfrac14 L^{.99}\) eventually. This beats both the path size and the small label moduli. To see the numerical error explicitly, in §2 of the projected comparison the total arithmetic count per rectangular cube and fixed tuple of projective lines modulo a product \(S\) of path labels has an error bounded by
\[
  O_{B,K}\!\left(\exp(O_K(L^{.70}))\,L^{O_B(1)}
                         (U^{3/2}+V+U)\right).
  \tag{4}
\]
Here \(S\) is squarefree, \(\log S=O_K(L^{.70})\); the deliberately loose exponential also absorbs the fixed small target-unit primes. The underlying Kloosterman bound does not require either coordinate scale to be a fixed power of \(P\), as follows.

For a fixed physical first coordinate \(u\asymp U\) all endpoint frames have \(w=[-P\bar v]_u\). The indicated projective lines impose a divisibility condition on \(u\), and \(w\equiv h u\bmod S_1\) with \((S_1,u)=1\), exactly as in §2 of the projected comparison. Open \((v,P)=1\) by squarefree \(d\mid\operatorname{rad}(P)\). Writing \(v=dv'\) gives \(v'w\equiv-P/d\bmod u\) with a unit on the right. There are at most \(\operatorname{rad}(P)\leq L^B\) such \(d\). Complete periods in \(v'\) give the totient main term; their counting errors are \(O((1+V/(d u))\tau(u))\) by opening \((w,u)=1\) in its single progression. The remaining interval has length at most \(u\). Complete both interval sums modulo \(u\) to estimate this remainder. The \(w\) interval is a progression of unit step \(S_1\) modulo \(u\), and for either normalized Fourier transform
\[
   \sum_{\substack{h\bmod u,\ h\ne0\\r\mid h}}|\widehat w(h)|
        \ll \frac{\log(2u)}r,\qquad r\mid u .
\]
This follows from the finite geometric sum; multiplication of frequencies by a unit permutes the nonzero multiples of \(r\). The zero frequencies give the stated main term. For the other frequencies the Weil bound is at most \(\tau(u)\sqrt{u\,(h_1,h_2,u)}\). Sum the gcd factor by positive divisor majorants \(\sum_{r\mid(h_1,h_2,u)}\sqrt r\); both axes are included with one Fourier factor at zero bounded by one. This makes the remainder at most \(O(\sqrt u\,\tau(u)^2(\log(2u))^2)\) for each \(u,d\). Summing in \(u\) uses \(\sum_{u\leq16U}\tau(u)^2\ll U(\log(2U))^3\), not a worst-case \(P^{o(1)}\) that might overwhelm (3). The complete-period errors sum to \(O(L^{O(1)}(U+V))\) per \(d\). For the remaining totient-factor average in \(u\), the divisor expansion of \(\varphi(u)/u\) and opening \((u,S_1P)=1\) cost at most \(O(L\,2^{\omega(S_1\operatorname{rad}(P))})\), times \(O(V)\); the infinite tail of the main \(j^{-1}[j,S_0]^{-1}\) is \(O(1/U)\) after summing \(j>16U\). This proves (4) with the same main density as before.

After division by \(UV\), the contribution of \((U^{3/2}+V+U)\) is \(O(\exp(-cL^{.99}))\): for example \(\sqrt U/V\leq \sqrt C/\sqrt V\). The unit-start density in the main term is still \(\prod_{p\mid P}(p-1)/(p+1)\leq1\). Summing over all line tuples in a path costs at most \(\exp(O_K(L^{.70}))\), and JLL (5.22) allows the total absolute path coefficients \(\exp(O_K(L^{.73}))\). Take mesh \(\Delta=1/\lceil\exp(L^{.8})\rceil\). The number of cubes is \(O(\Delta^{-3})=\exp(O(L^{.8}))\), while the continuous boundary error per path is \(\Delta\exp(O_K(L^{.21}))\) by JLL Lemma 6.2 (the sheared physical boundaries still have bounded degree). Therefore the aggregate arithmetic-to-real error is \(\exp(-c'L^{.8})\). This is more than enough for the \(L^{-ET}\) moment with \(T\asymp L^{1/2}\), including the corresponding one-edge comparison in the separation error. The bad repeated-label pieces are the same divisor-square moment on products of central size \(\asymp P\) and the same negligible label coincidence probabilities. The real-frame moment in [JLL Proposition 5.7 and §6.4](https://arxiv.org/html/2611.12467v2) chooses \(A_0,K_0\) from the desired real-moment exponent \(E\), not from a fixed mathematical lower exponent for the factor lengths. Its frame boxes are exactly the same after the shear. The other uses of factor length in the projected minor proof are the primitive endpoint and box containment checks; these follow more strongly from (3) over all \(\exp(O_K(L^{.21}))\) labels. This proves the claimed moving-scale minor comparison without replacing \(K\) or the graph depth by a moving function.

**Major Gram and the long signed slot.** The distinct-character Gram bound uses the explicit Iwaniec short-character-sum estimate as stated in [Goldmakher, *Character Sums to Smooth Moduli are Small*, Theorem 4.1](https://doi.org/10.4153/CJM-2010-047-9) ([text](https://arxiv.org/pdf/0712.1574)), citing Iwaniec Lemma 6. At length scale \(x\) and inducing conductor \(q\) it bounds a short-interval sum by
\[
 x\exp\left(C_1 z\log^2(C_2 z)
       -\frac{\log x}{C_3 z^2\log(C_4 z)}\right),\qquad
 z=\frac{\log(3q)}{\log x},
 \tag{5}
\]
valid for \(\operatorname{rad}(q)^{100}<x<9q^2\), upper endpoint less than \(2x\). After the same imprimitive-prime inclusion–exclusion as in the small-radical major proof, \(x\geq\exp(cL^{.99})\) since all omitted divisors divide \(\operatorname{rad}(Pd)\leq L^{B+A_0}\) for an arc denominator \(d\leq L^{A_0}\). If \(q<\sqrt{x}/3\), complete periods give \(O(q)\). Otherwise (5) applies, with \(z=O(L^{.01})\), so it gives a relative \(\exp(-c L^{.97}/\log L)\) off-diagonal bound after the possible fixed log losses. The exceptional sets on each of the two sides still have cardinality \(\exp(O_K(L^{.9}\log L))\): their high moment uses \(j=\lfloor\log(D'/2)/\log(2Y)\rfloor=O(L^{.9})\) on the two actual colored tag polynomials of length \(Y\), in the actual character modulus \(D'\geq P\). Products of \(j\) tags below \(D'\) have at most \((j!)^K\) decompositions. This estimate holds for both coefficient choices after the rational residue splits and real weights. The Gram bound thus dominates the union of the two exceptional sets. Its Bessel argument remains valid on the prime slot with arbitrary bounded weights and interval and residue restrictions, since the Gram is measured on the full integer interval.

In the other slot we still use \(1/L(s,\chi^*)\), or \(L(2s,(\chi^*)^2)/L(s,\chi^*)\). The companion's small-radical zero-free shift of size \(\asymp L^{-3/4}/(\log L)^2\) at any fixed polylogarithmic height gives a factor \(\exp(-cL^{.24}/(\log L)^2)\) at the shortest Perron length, even after the nonunit residue division and the factor \(a\leq L^D\). Convolving off all omitted small Euler factors still has reciprocal mass \(O(L^{.2})\) and negligible Rankin tail: compare to all \(\exp(2L^{.2})\)-smooth factors, at length \(\exp(cL^{.99})\). The arithmetic \(d=d_0d_1\) splitting in (5) of the companion uses only fixed log costs; it gives \(1/\varphi(P)\) in the Fourier expansion and keeps all inducing conductors dividing \(P d\). Small moduli, the possible real zero at conductor at most \(4L^{B+A_0}\), and the exact support \(\operatorname{rad}(P)\leq L^B\) have the same treatment as there. Hence the marked projected major estimate retains arbitrary fixed logarithmic saving, uniformly under (3).

## 2. Bounded first-active removal

Fix either the affine unit sample \(\mathscr X\) of the companion, with central \(x=a m,\ P-x=b n\), or its bilateral rough sample at \(a=b=1\) with \(P\) even and rough cutoff \(\exp(L^\gamma)\) for fixed \(0<\gamma<3/20\) as in [the rough companion](BilateralRough.md). Write \(M_{\mathscr X}\) for its CRT mass (\(\varphi(P)|J|/(ab)\) or \(|J|P D_w(P)\), respectively). Separate \(s\) banks as in the companion. For unrough data put \(\gamma=0\) solely in choosing these banks. Set \(\alpha_*=\max(.1,\gamma)\), \(h_*=.15-\alpha_*>0\), \(c_*=h_*/(100\log 4)\), and take
\[
   s=\left\lfloor\frac{c_*\log L}{K+1}\right\rfloor .
\]
For example center the \(K\) exponent neighborhoods at \(\alpha_*+h_*/4+(1/20+h_*/2)(\nu-1/2)/K\), give each half-width \(h_*/(20K)\), and within each choose exponent increments \(\log 4/\log L\). These neighborhoods are inside \((\alpha_*,.2)\) and the gaps within every family exceed \(1/(20K)\). The choice permits all \(s\) families and ensures \(2^{(K+1)s}\leq L\) independently of \(K\). Thus the logarithmic sums over the bank family subsets never determine the needed \(K\) recursively.

For bank \(j\), define the **bounded** event
\[
 U_j(x)=1_{\text{no prime of }\mathcal B_j\text{ divides }x}
      \prod_{\nu=1}^{K}
       1_{\ \omega_{j,\nu}(P-x)\geq1}.
\]
Here \(\omega_{j,\nu}(y)\) counts the actual distinct prime divisors of \(y\) within color \(\nu\) of bank \(j\). The identity
\[
 1-\prod_{j=1}^s(1-U_j(x))
   =\sum_{j=1}^s U_j(x)\prod_{i<j}(1-U_i(x))
 \tag{6}
\]
uses at most \(2^s\) nonempty-product terms on expanding its right side. In the local CRT model conditional on the base sample, the \(U_j\) events are independent. Their single probabilities are exactly
\[
  \prod_{r\in\mathcal B_j}(1-1/r)
  \prod_{\nu=1}^{K}
    \left(1-\prod_{r\in\mathcal B_{j,\nu}}
                        (1-1/(r-1))\right).
\]
Indeed, \(P\) is a unit at all bank primes; once zero is excluded at \(x\bmod r\), its reflected obligation uses one of the remaining \(r-1\) classes. The mass assumptions give the fixed lower bound \(c_K=e^{-K}(1-e^{-1/4})^K>0\) for large \(P\). 

For the actual missing-bank count, expand \(\prod(1-U_j)\) first in subsets of banks and within each selected bank expand “each color hit” into subsets of colors with no hit. This has at most \(2^{(K+1)s}\leq L\) terms. Every resulting term consists of literal exclusions of at most two residue classes at any bank prime and, in the rough case, at each roughness prime. The exact base affine rail and target-unit conditions are unchanged. Apply CRT and upper/lower Bonferroni as in the companions, now across all selected banks at once. Their total forbidden reciprocal mass is \(O(Ks+\log L)=O(\log L)\), and with depth \(\lfloor L^{.1}\rfloor\) the tail is smaller than every fixed negative log power. There are \(\exp(O_K(L^{.3}))\) floor errors before the additional \(\leq L\) expansion cost (including any fixed polylogarithmic target-unit inclusion–exclusion). Arithmetic-to-model errors are \(O_A(P L^{-A})\) to any prescribed fixed power. Thus
\[
   \sum_{x\in\mathscr X}\prod_j(1-U_j(x))
   \ll M_{\mathscr X} L^{-\kappa_K}+O_A(P L^{-A}),
   \qquad \kappa_K=\frac{c_*c_K}{2(K+1)}>0 .
 \tag{7}
\]
Constants in the exponent are intentionally conservative, using the floor in \(s\). Unlike root mean square removal, (7) gives a fixed positive log power.

Each nonempty term on the right of (6) is handled by the packet estimate. Designate its last bank \(j\) and expand only the \(j\)-th hit condition as a sum over actual tagged divisors \(u\in\mathcal A_j,\ u\mid P-x\), with weight \(1/\prod_\nu\omega_{j,\nu}(P-x)\) on nonempty rows. After writing \(P-x=u h\), and ignoring the negligible square events \(r^2\mid P-x\) at bank primes \(r\), the reciprocal becomes exactly
\[
  \frac{1}{\prod_\nu(1+\omega_{j,\nu}(h))}.
\]
For every other bank of the term, its hit condition on \(u h\) is precisely its hit condition on \(h\), since bank primes are disjoint. Their source avoidance conditions all stay separable in the two source factors; their union omits only primes below \(\exp(2L^{.2})\), allowed in the long signed-slot estimate of §1. The \(j\)-th bank itself is still fully avoided at the source, as required for the primitive linear algebra. Consequently the product of hit indicators and the reciprocal form a single bounded \(h\)-coefficient. The residual signs \(\mu,\lambda,\mu^2,1\) and extra fixed prime exclusions are removed or kept exactly as in §3 of the companion, with \(b\mid h\) for an affine rail and no tag prime dividing \(b\). In the rough case \(u\) is entirely above the cutoff \(w\). On marked-square rows the original and replaced weights are \(O_K(L^K)\) per source integer; their total \(O(P\exp(-cL^{.1}))\) population before weighting makes this replacement harmless even after the \(\leq L\) expansions. No square condition has to be imposed on the mean-square kernel itself.

For a signed source \(f(m)\), use its actual log-derivative truncation (6) in the companion with \(\varepsilon=L^{-1/100}\), keeping only genuine primes \(p\in[P^\varepsilon,P^{1-\varepsilon}]\). The prime slot and other source slot then satisfy (3); compactness of \(J\) and polylogarithmic affine slopes ensure this also at both endpoints of the range. All unit and extra masks are the same as before. The elementary small-prime and prime-power truncation errors in §2 of the companion remain \(O((\varepsilon+L^{-1})M_{\mathscr X})+O(P^{1/2+o(1)})\), using \(\sum_{p\leq P^\varepsilon}\log p/p\ll\varepsilon L+1\) and the literal affine progression count with its unchanged floor error. For the large-prime range write \(m=pv\), \(v\leq P^\varepsilon=\exp(L^{.99})\). All endpoints \(P/(a v)\) are still at least \(P^{1/2}\) eventually, so Siegel–Walfisz and the same \(bP\)-coprime harmonic estimate in that proof apply uniformly. Its product restriction only requires every prime of \(bP\) to lie below \(P^\varepsilon\), true here. In the bilateral rough sample use instead the actual prime BV argument and the identity \(E_wV_w=D_w(P)\) of §2 of the rough companion; again \(P^\varepsilon>w\) and BV is at endpoint at least \(P^{1/2}\). Its relative \(O(\varepsilon M_{\mathscr X})\) still holds on the rare sample itself. Logs in the denominator of the truncated derivative cost \(O(1/L)\) and its absolute row weight stays bounded by one. Boundary mesh errors remain arbitrarily log-saved: discard intervals of width \(P L^{-F_1}\), count the original rows there, and use either the absolute normalized log-derivative sum \(\sum_{p\mid m}\log p/\log m\leq1\), or the weaker \(O(L^{.01})\) bound on the number of retained prime factors. In particular no fixed-\(\varepsilon\) constant is needed for the mesh.

Choose the packet log saving after \(B,D,J\), enough to pay the fixed endpoint meshes and the \(\leq L\) bank expansion while remaining \(o(M_{\mathscr X}L^{-1})\). Then choose the corresponding fixed \(K\), and only afterwards take large \(P\). Equations (6), (7) and the uniformly bounded row weights pay the missed banks. The moving log-derivative tails give \(O(M_{\mathscr X}L^{-1/100})\). We obtain for some fixed \(\kappa>0\) (the minimum of the endpoint and bank exponents suffices after shrinking it once)
\[
  \left|\sum_{\mathscr X} f(m)g(n)\,
               1_{(m,T)=1}^{i}1_{(n,T)=1}^{j}\right|
   \ll_{B,D,J} M_{\mathscr X} L^{-\kappa}
 \tag{8}
\]
in the affine unit case, uniformly \(a,b,\operatorname{rad}(T)\leq L^D\), exactly with the slope and unit hypotheses of (3) of the companion and \(f,g\) as there. The same power-log improvement applies to the centered signed correlation (7) of the rough companion, with its rare sample and fixed \(\gamma\), if wanted. These are signed true arithmetic sums, not a positivity estimate for binary prime atoms.

## 3. Paying the full rectangle, including nonunits

In the target-unit rectangle, a nonempty cell \(a m+b n=N,\ (am,N)=1\) forces \((ab,N)=1\) and \((a,b)=1\). Equation (8) is then at most \(C\varphi(N)L^{-\kappa}/(ab)\) for \(\mu\) on both sides. Summing \((\log a)(\log b)/(ab)\) for \(a,b\leq H\) costs at most \(O((1+\log H)^4)\).

For the full rectangle fix \(a,b\) and partition by \(d=(a m,N)\). If \(N'=N/d\), put \(t=a m/d\), so \((t,N')=1\) and \((N'-t,N')=1\). Set
\[
   a'=\frac a{(a,d)},\quad b'=\frac b{(b,d)},\qquad
   e_a=\frac d{(a,d)},\quad e_b=\frac d{(b,d)} .
\]
Then \(a'\mid t\), \(b'\mid N'-t\) and the two original Möbius arguments are
\[
   m=e_a(t/a'),\qquad n=e_b((N'-t)/b').
\]
A nonempty stratum forces \((a'b',N')=1\), and hence \((a',b')=1\) by their affine equation. If \(e_a\) or \(e_b\) is not squarefree the contribution vanishes. Otherwise separate \(\mu(e_a)\), \(\mu(e_b)\) and impose their coprimality masks on the two new arguments. Both mask radicals divide \(\operatorname{rad}(d)\). For \(d\leq\sqrt N\), \(\log N'\asymp L\), while \(\operatorname{rad}(N'),\operatorname{rad}(d)\leq L^B\) and \(a',b'\leq L^D\). Fixed exponent enlargements in (8) absorb these constants uniformly. Thus the absolute bound for this stratum is \(C\varphi(N')L^{-\kappa}/(a'b')\). Strata \(d>\sqrt N\) are bounded crudely by \(O(H^2(1+\log H)^2\sqrt N\,\tau(N))=N^{1/2+o(1)}\) even after summing all outer cells.

The extra weights \((a,d)(b,d)\) do not cost powers of \(H\). Expand \((a,d)=\sum_{r\mid a,\ r\mid d}\varphi(r)\) and use the elementary identity
\[
   \frac1N\sum_{\substack{d\mid N\\R\mid d}}\varphi(N/d)
   =\begin{cases}1/R,&R\mid N,\\0,&R\nmid N.\end{cases}
\]
With \(R=[r,s]\), and \(\sum_{a\le H,r\mid a}(\log a)/a\ll (1+\log H)^2/r\), this gives
\[
\begin{split}
 &\frac1N\sum_{d\mid N}\varphi(N/d)
       \sum_{a,b\le H}\frac{(\log a)(\log b)}{ab}(a,d)(b,d)\\
 &\hspace{1cm}\ll (1+\log H)^4
       \sum_{r,s\leq H}\frac{\varphi(r)\varphi(s)}{rs[r,s]}
       \ll (1+\log H)^7 .
\end{split}
\]
The last step uses \(\sum_{r,s\le H}1/[r,s]\ll(1+\log H)^3\), obtained by setting \(r=g r',s=g s'\) with \(g=(r,s)\) and summing the three harmonic factors. We took absolute values of the stratum sums, so the conclusion also bounds the absolute sum over affine cells as claimed. Since \(1+\log H=O_D(1+\log L)\), these seven logarithms of the logarithm cost less than any fixed positive power of \(L\); take for example \(\eta=\kappa/2\). This proves (1).

## Scope and nearby work

The [September ordinary two-point manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) allows constants depending on fixed affine forms, and by its statement alone does not cover the intercept \(N\) or these simultaneously moving cells. The relevant reported October full-interval Liouville and rough parity results, and the distinction from the ordinary Möbius scope, are discussed in the two companions. [Tian–Yang §4](https://arxiv.org/abs/2611.10499) separates the ordinary Möbius pointwise issue from their different unitary Möbius sign theorem. [Arneth's October discussion](https://doi.org/10.5281/zenodo.23504447) treats related Möbius–prime decomposition and dispersion without closing the whole fixed-target parity term. These are scope comparisons, not a priority claim for (1). The present estimate concerns the concrete simultaneous short-\(\log\) rectangle of (2) at prescribed small-radical targets. There are still large cofactor cells in the genuine binary expression; no signed conclusion about their aggregate or binary Goldbach follows.
