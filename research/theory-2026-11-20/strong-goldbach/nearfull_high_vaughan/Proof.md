# Near-full giant remainder with two genuinely high von Mangoldt slots

Fix \(C>1\), a compact central interval \(J_0\Subset(0,1)\), and \(J\subset J_0\). Let \(N\) be a prescribed even target, \(L=\log N\), \(\ell=\log L\), \(S=\exp(\ell^4)\), \(B=N/S\), and
\[
 I=[N/S^C,B],\qquad U=\exp(\ell^3),\quad z=\exp(\ell^2),
 \quad W=\sqrt N/S^{C+10}.
\]
Use \(y=N-x\), \(T_y=y/B\), and \(Q_y(m)=\sum_{d\mid m,\ d<T_y}\mu(d)\). Define \(C_I\) as the true giant remainder in [ReverseTypeI.md](../reverse_giant_typeI/ReverseTypeI.md) with this literal \(I\). Endpoints in \(I\) are inclusive and the \(Q_y\) cutoff is strict.

**All-even calibration.** With actual \(x=a f g,\ y=m c h k=N-x\), the identity
\[
 C_I=
 \sum_{\substack{x\in NJ,\ c h k\in I\\ (xy,N)=1,\ P^-(a f g c h k)>z\\
                  a,c>U,\ f,h>W}}
   \mu(a)\Lambda(f)\mu(c)\Lambda(h)Q_y(m)+O_A(NL^{-A})              \tag{1}
\]
holds for every fixed \(A>0\). Here \(m\) is unrestricted except for the literal quotient and unit conditions. Both high labels can be taken to be genuine primes; their proper powers contribute a power-small error.

**Signed small-radical deletion.** For each fixed \(B_0>0\) there exists a fixed \(\delta>0\) such that at every target with \(\operatorname{rad}(N)\le L^{B_0}\), the entire actual part of (1) with
\[
                         a(mc)\ge N\exp(-L^\delta)                 \tag{2}
\]
is \(o(N)\). In particular this pays all its supercritical raw product. The true high-cut complement \(a(mc)<N\exp(-L^\delta)\) remains signed and open. This is not a credit against the distinct low-\(\Lambda\)-cutoff raw identity.

## 1. Two short-prefix harmonics

We use the uniform rough signed harmonic of [the complementary raw proof](../raw_complementary_vaughan/Proof.md) at lower endpoint \(U=\exp(\ell^3)\). The same proof gives uniform arbitrary-log small tails of
\(\mu(n)/\varphi(Fn)\), or of \(\mu(n)\log n/\varphi(Fn)\), over \(n>U\) with \(P^-(n)>z\) and an additional unit mask \(H\le N^{O(1)}\), after taking out \(1/\varphi(F)\). At unexcluded primes the local coefficient is \(1\) if the prime divides \(F\), and \(q/(q-1)\) otherwise, so relative to \(\zeta^{-1}\) the new absolute Euler factor is uniformly bounded at \(\sigma=1-\log\ell/(2\ell^2)>.9\) except for the already treated excluded inverse factors. The extra \(\log n\) only costs polynomial factors when integrating the Rankin/Mertens tails. The unweighted complete harmonic is zero. The derivative of its Dirichlet series gives the first signed log moment at \(s=1\).

For any polynomial-sized unit mask \(H\), we also have
\[
  \sum_{m\in K,\ (m,H)=1} \frac{Q_T(m)F(m)}{m}=O_A(L^{-A})         \tag{3}
\]
on dyads \(m\asymp M\gg S,\ m\ge T\), \(T\asymp S\), and any real subinterval \(K\) with log-bounded supremum and variation of \(F\). The notation allows \(M\ge cS\) for fixed \(c>0\) and the masks may include \(N\). Open \(d<T,\ m=dn\). For \(d>\sqrt S\) fix \(n\) and use masked \(\mu(d)/d\) tail with \(F(dn)\), then sum \(n\) harmonically. For \(d\le\sqrt S\), the count of \(H\)-units \(n\) in any subinterval of length scale \(X\asymp M/d\) is its ordinary real density \(\varphi(H)/H\) plus \(O(X^\sigma\prod_{q\mid H}(1+q^{-\sigma}))\), at \(\sigma=1-1/(10\ell)\). This follows by opening squarefree divisors of the radical of \(H\), bounding floors and the uncounted main tail by Rankin. The Euler factor is \(\ell^{O(1)}\): split at \(L^2\), use bounded powers \(q^{1-\sigma}\) below the split and at most \(O(L)\) larger prime divisors. Partial summation gives arbitrary-log error since \(X\gg\sqrt S\). The main is independent of \(d\) except the factor \(1/d\); summing \(\mu(d)/d\) over \(d\le\sqrt S,\ (d,H)=1\) gives arbitrary-log saving by the uniform masked Mertens tail, whose series is \(\zeta^{-1}\) times the excluded-prime inverses at the same \(\sigma\). This proves (3) with no false \(\tau(H)\) loss at the subpower length.

A second harmonic uses
\[
 h_N(m)=1_{(m,N)=1}\prod_{q\mid m}\frac{q-1}{q-2}
\]
(on the unit support the prime 2 cannot occur). Uniformly for \(T\asymp S,\ X\asymp S^C\),
\[
 \sum_{m\le X}\frac{Q_T(m)h_N(m)}m=1+O_A(L^{-A}).                 \tag{4}
\]
To prove it fix a squarefree unit \(d<T\). The series of \(h_N(dn)/h_N(d)\) is \(\zeta(s)H_{N,d}(s)\), where
\[
 H_{N,d}(s)=\prod_{q\mid N}(1-q^{-s})
            \prod_{q\nmid Nd}(1+q^{-s}/(q-2)).
\]
The second product runs over odd primes. The absolute coefficient norm at \(1-1/(10\ell)\) is \(\ell^{O(1)}\) uniformly, by the same split for target primes and absolute convergence elsewhere. Ordinary harmonic summation in the convolution gives
\[
 \sum_{n\le X/d}\frac{h_N(dn)}{h_N(d)n}
 =H_{N,d}(1)\bigl(\log(X/d)+\gamma_{\rm E}\bigr)
   +H_{N,d}'(1)+O_A(L^{-A})
\]
uniformly, since \(X/d\gg S^{C-1}\). For example bound the \(O(1/Y)\) harmonic-floor term for \(Y=X/(dj)\), and the absolute series tail \(j>X/d\), by the same Rankin factor with a polynomial \(\log X\) cost. The exact residue after putting back \(h_N(d)/d\) is
\[
 \frac{h_N(d)}{d}H_{N,d}(1)
     =\frac1{\mathfrak S(N)\varphi(d)} .
\]
Removing the factors at \(q\mid d\) from \(H_{N,1}\) changes its log derivative at 1 by \(\sum_{q\mid d}\log q/(q-1)^2\). In the signed \(d\)-sum the constant terms vanish by masked Mertens, the \(-\log d\) term gives exactly \(\mathfrak S(N)\), and the extra log derivative is negligible. For the last assertion, split its prime sum at \(\sqrt T\). The smaller primes leave the signed \(d/q\)-harmonic beyond \(\sqrt T\) with an extra unit mask, while the larger-prime absolute harmonic is \(O(L^C/\sqrt T)\) by the reciprocal square in the coefficient. The absolute \(d\)-weights cost only log powers. This proves (4). Since \(Q_T(m)=0\) for \(1<m<T\) and \(Q_T(1)=1\), the sum on the literal \(T\le m\le X\) is \(O_A(L^{-A})\), including its actual term at \(m=T\) if \(T\) is integral.

## 2. All-even calibration by the two genuine Type I terms and their intersection

At the true \(r=y/m\) and \(x\) insert the actual unit and \(z\)-rough masks and use \(\Lambda\) for the genuine primes. Proper \(x\)-powers cost \(N^{1/2+o(1)}\) by the physical divisor envelope. The proper powers \(r\ge N/S^C\) have reciprocal sum \(N^{-1/2+o(1)}\), by elementary counting and partial summation, hence cost \(N^{1/2+o(1)}\) by counting actual multiples of \(r\) in \(y\). Original prime divisors of the target can be removed at a power-small cost; \(x,r\) here are much too long to require any prime-distribution correction at nonunit residues.

Write \(P=I_x+II_x,\ R=I_r+II_r\) for the rough forms of Vaughan's identity on the two legs, with independent cutoffs \(U\) for \(\mu\) and \(W\) for \(\Lambda\) on both. The small \(\Lambda_{\le W}\) term is absent on their actual ranges. At every physical row use
\[
    P R=P I_r+I_x R-I_x I_r+II_x II_r.                             \tag{5}
\]
This avoids asserting any new prime estimate against a synthetic opposite Type II source.

For \(P I_r\), use the literal proof of the reverse Type I removal: each actual modulus \(m c h e\), with \(c\le U,\ h\le W\) (or \(h=1\) in the free log term) and \(e\) a true roughness label, is at most
\[
 S^C U W\, V_0^{o(1)}\ll \sqrt N/S^9,\qquad V_0=U.
\]
The labels have size and count \(U^{o(1)}\) by the already verified factorial truncation. This is inside true prime B--V with maximal prefixes. The real condition \(d<T_y\) after opening \(d\mid m\) remains an endpoint, and the absolute multiplicities of the actual moduli are bounded by fixed divisor powers. Their floors and proper-power removals have the same power/subpower reserve. On the modeled side (3) of ReverseTypeI cancels the true \(m\)-harmonic with \(\varphi(m c h e)^{-1}\), even with the moving \(T_y\) and \(\log(y/(mc))\); the remaining \(c,h,e\) are summed reciprocally. Thus \(P I_r=O_A(NL^{-A})\) in the weighted total.

For \(I_x R\), fix the true \(m\le S^C\) and apply actual prime B--V on \(r\) at length \(N/m\). After the rough opening the modulus \(a f e\) is at most \(UW U^{o(1)}\ll \sqrt{N/m}/S^8\). It is a unit and coprime to \(m\), since the progression \(m r\equiv N\bmod a f e\) is literal on units. All variable endpoints, including \(m r>Bd\), are allowed by maximal prefixes. For a given modulus the actual assignments of \(a,f,e\) have fixed divisor-power multiplicity and coefficients \(O(L)\); retain the same weighted B--V clipping as in ReverseTypeI. Summing the remaining \(m,d\) costs only the absolute harmonic \(\sum_{m\le S^C}\tau(m)/m\), with the factor \(N/m\) from the scale already included in that harmonic. One can use \(\Lambda\) in the progression estimate and subtract its proper powers by the same global physical count, or spend the \(S^8\) modulus reserve against their elementary per-\(m\) count.

The \(e\)-series completes to
\(\prod_{q\le z,\ q\nmid Nm}(1-1/(q-1))\), since \(a,f\) are \(z\)-rough; its factorial error is arbitrarily log-small. The negative short \(a,f\) term of \(I_x\) has no free log, so the fixed \(f\) signed \(\mu(a)/\varphi(af)\) harmonic, \(a\le U\) and unit at \(Nm\), is arbitrary-log small as above. In the first Type I term the exact finite harmonic is
\[
   \sum_{a\le U,\ (a,Nm)=1,\ P^-(a)>z}
      \frac{\mu(a)}{\varphi(a)}\log(x/a).
\]
Its zeroth signed complete harmonic vanishes and its log moment is its Euler derivative; truncating at \(U\) has arbitrary-log accuracy uniformly for \(x\in NJ\). The derivative has factor \((1-1/q)^{-1}\) at primes \(q\le z\) or \(q\mid Nm\), and \(q(q-2)/(q-1)^2\) elsewhere. Multiplication by the \(e\)-product gives **exactly** \(\mathfrak S(N)h_N(m)\) on the unit support. Changing variables from \(r\) to \(x=N-mr\) has Jacobian \(1/m\). At every \(x\) the true \(m\)-window is \([T_y,yS^C/N]\); (4) minus its sole \(m=1\) atom kills this model. Hence \(I_x R=O_A(NL^{-A})\).

The overlap \(I_x I_r\) is an integer calculation, not a prime input. Open both short roughness factors with true products \(e_1,e_2\) as before; at compatible target-unit products \(A=a f e_1,\ D=m c h e_2\), \((A,D)=1\) is forced and two free integer coordinates give one CRT class of density \(\varphi(N)/(N A D)\) in \(x\). The literal unit mask is counted as in [DoubleRough, §2, Case 1](../reverse_giant_typeI/DoubleRough.md). Its total integer-floor cost, including both label counts and divisor weights, is
\(S^C U^2 W^2 U^{o(1)} L^{O(1)}\ll N/S^9\).
Omitted roughness labels are handled by the actual factorial bounds and the same floor reserve. At fixed \(x,a,f,c,h,e_1,e_2\) the \(m\)-sum in this main term is the actual \(Q_y(m)/m\), with mask \((m,N A)=1\) and \(\log(y/(mc))\) when the right term uses a free log. Its \(m\)-dependent gates are only the same literal interval. Apply (3). This also kills the log-times-log principal; a zeroth \(\mu(a)/a\) cancellation alone would not kill that term. The remaining absolute harmonic sums cost log powers. This proves (1) by (5). Proper \(f,h>W\) powers have reciprocal sum \(N^{-1/4+o(1)}\); actual multiples and the fixed divisor envelope pay their removal, including inside any subsequently stated raw cut.

## 3. Geometry, smoothing, and parameter order for the signed deletion

In (2), since \(f,h>W\), each of \(a,mc\) is at most \(N/W=\sqrt N S^{C+10}\). Hence both are in \([\sqrt N e^{-2L^\delta},\sqrt N e^{2L^\delta}]\) for large \(N\), and \(g,k\le e^{4L^\delta}\). We use \(\delta<.01\), to be fixed below. In particular \(g,k,m\) are smaller than the least projected bank prime (\(\ge e^{cL^{.1}}\)), while \(f,h\) are genuine primes much larger than the bank. Both \(a\) and \(c\) have fixed polynomial lengths in all pieces, as \(m\le S^C\).

Freeze \(T_y\) and both literal \(m\)-endpoints on relative \(y\)-mesh \(L^{-F}\) with the actual multiple-count proof used in [the reciprocal seam](../reverse_giant_typeI/GiantReciprocalSeam.md). The changed rows have \(m\mid y\) or \(d\mid y\), with \(m\le S^C,d<T_y\ll S\); their global thin-strip count is \(O(N L^{1-F}+S^C)\). Smooth the central cuts in thinner collars. All errors are arbitrary-log small by the fixed divisor envelope. The joint condition (2) itself can be retained with a log-relative mesh of \(a\), freezing \(mc\ge N e^{-L^\delta}/a\) within each cell. The changed region then has \(mc\) in a relative \(O(L^{-F})\) shell at the predicted boundary for that \(a\)-cell. This boundary is not estimated by incorrectly counting \(a(mc)\) as a divisor of \(y\). For fixed \(m,g,k\) it is a union of independent \(a,c\) rectangles, with \(c\)-width \(O(L^{-F})\) relative to its scale. Treat \(f,h\) as free integers for this absolute error and bound their weights by \(L^2\), then apply the elementary-main-plus-Bettin--Chandee reciprocal calculation on base products \(ag,m c k\) (near square root, by the subpower ranges). The nonzero contribution has a fixed power saving per cell and fixed \(m,g,k\), stable under their total subpower and log counts. The zero term's \(c\)-harmonic is \(O(L^{-F}+N^{-1/2+o(1)})\) after fixing \(a\), while the other reciprocal sums cost at most a fixed power of \(L\). This pays the joint boundary. Smoothing each remaining \(mc\) interval for separation costs arbitrary-log error by actual multiples \(mc\mid y\), using the true divisor envelope and the log number of boundaries; one may instead use the same positive lattice calculation. We now have independent intervals in \(a\) and fixed \(m\), and smooth \(mc\) interval tests on dyads. The finite smooth \(mc\) and \(x\) test expansions by Mellin have log-power costs fixed before assigning the projected comparison precision.

Choose the requisite fixed precision in the projected comparison for these applications, absorbing fixed divisor, smooth, and packet powers of \(L\). Choose its fixed number \(K\) of colors next and \(s\asymp_K\log L\) disjoint admissible families in the usual bank range. All lost exponent budgets for mesh counts, log powers of harmonic \(g,k\), and Boolean expansions can be fixed uniformly already for \(0<\delta<.01\). Let \(\kappa>0\) be the resulting exponent of model failure, as computed below, and only then take \(\delta<\min(.01,\kappa/10)\).

## 4. Literal covered cancellation

In family \(j\) write \(A_j(a)\) for avoidance of the entire bank by the genuine \(a\) and \(H_j(c)\) for all \(K\) colors hit by the genuine \(c\). The cover is \(C(a,c)=1-\prod_j(1-A_j(a)H_j(c))\); it is tested on the actual two integer factors, not independently resampled. Expand the first-success earlier failures by
\[
 \prod_{i<j}(1-A_i(a)H_i(c))
   =\sum_{E\subset\{1,\ldots,j-1\}}(-1)^{|E|}
                  \prod_{i\in E}A_i(a)\prod_{i\in E}H_i(c).
\]
The number of terms is log-power bounded. When chosen family \(j\) succeeds, extract \(u\mid c\), one genuine prime per color, and write \(c=u c'\). Away from bank-square incidence, the literal reciprocal allocation is \(\prod_\nu(1+\omega_{j,\nu}(c'))^{-1}\); all earlier-family masks on \(c\) are unchanged and \(\mu(c)=(-1)^K\mu(c')\). Actual bank-square incidence costs arbitrary logs before separation, by \(q^2\mid y\), \(q\ge e^{cL^{.1}}\), and fixed divisor moments, including the allocated weights whose total at each hit is bounded by one. Bank removal does not change the rough mask at \(z\).

Group the left source as \(D=a g\) and the genuine prime \(f\). Its \(D\)-weight is a divisor-bounded convolution over the **actual subpower** \(g\)'s and the long signed \(\mu(a)\) with the inherited bank omissions; its \(f\)-weight is the true \(\log f\) on primes. All target units remain. The two actual left factors avoid all chosen bank primes because \(a\) avoids them, \(g<\min\mathcal{B}\), and \(f\) is a much larger prime. The physical determinant endpoints in the [one-prime extension of the reflected comparison](../small_radical_reflected_chowla/Proof.md), §1, are primitive: their gcd divides the projected quotient of determinant of size \(O(Y)\), is coprime to the target and labels, and one coordinate in that gcd has the genuine prime \(f\) (or the prime from the other endpoint) of polynomial size. Thus the effective upper \(Y=e^{O_K(L^{.2})}\) makes this gcd one. The displayed statement there uses a fixed short multiplier in the signed slot, but grouping ours is valid directly as follows.

First clip the \(D\)-coefficient to \(\tau(D)\le L^M\) for a sufficiently large fixed \(M\). The removed physical rows are arbitrary-log small by \(\tau(D)\le\tau(x)\) and high fixed divisor moments on \(x,y\); simultaneous allocation by \(u\) costs at most one. In the long signed character bound the clip costs \(D_{\rm scale}L^{-A}\) by the usual divisor moments on the \(D\) interval, so at the major kernel it suffices to use the uncut convolution. At each fixed actual \(g\), all uniform character-prefix estimates are on the genuine long \(a\) of polynomial length, with all extra omission primes at most \(\exp(2L^{.2})\), except target primes of polylog radical. All \(g\) and \(a\) were \(z\)-rough, hence no additional primes at rational-arc denominators \(d\le L^{A_0}\) divide \(D\). Thus the same long \(\mu\)-twist in the genuine conductor dividing \(Nd\), with its rough/bank/target omissions, supplies arbitrary-log bound at length \(D_{\rm scale}/g\); summing only over the reciprocal \(g\)-harmonic supplies the grouped bound. The compact product separation and any fixed polylog twists cost log powers. Use fixed-ratio packets small enough that any touching the smooth central support has its full product range strictly between fixed positive multiples of \(N\) and strictly below \(N\). In the full projected major, off the exceptional high-tag sets use Parseval as before, and on them use the signed \(D\)-bound and restricted Bessel on the genuine prime \(f\)-coefficient. The minor comparison uses the clipped polylog coefficient, primitive endpoints and exact avoidance, with no requirement of additional roughness above the bank when one slot is genuinely prime.

On the other side, after extracting \(u\) the residual argument is \(n=m c'h k\), on the exact equation \(D f+u n=N\). Its physical factorization assets, \(Q_T(m)\), \(\mu(c')\), genuine \(\log h\) on primes, and all first-success rank masks are divisor-bounded by \(L^{C'}\tau(n)^{C'}\). Thus its square norm on \(n\ll N/Y\) for \(u\asymp Y\) is \(O((N/Y)L^{O(1)})\). Coupled \(mc=m u c'\) smooth tests separate by Mellin: the \(u^{it}\) factor is a product of modulus-one factors on its genuine prime labels, and the \(m c'\) factor stays in the residual. The projected minor comparison permits these multiplicative tag phases: JLL v2 Lemma 6.11 permits bounded independent prime multipliers in the entering slots and their reverse, or absorb \(u^{it}\) into the starting fibre coefficient, where it depends only on the unordered prime product and does not break its constancy. The full projected major uses the same high tag moments and is uniform for these bounded label factors. Use fixed-ratio smooth tag shells (with a partition of unity) and keep all discarded log-frequency tails inside the polynomial divisor envelope. Cauchy on the actual residual then makes the covered part \(O_A(NL^{-A})\) for the initially required fixed precision (choosing the bank color count for that precision). No arithmetic information about unmarked phases of \(h\) is used.

## 5. The missed rows: a simultaneous two-prime upper at the actual flux

On the complement discard the \(\mu\) signs, bound \(|Q_y(m)|\le\tau(m)\), and dominate the two true log weights by \(L^2\). Enlarge to the full independent ranges
\(m\le S^C,\ g,k\le e^{4L^\delta},\
a,mc\in[\sqrt N e^{-2L^\delta},\sqrt N e^{2L^\delta}]\).
Keep actual outer target units, but do not need roughness or the old \(I\)-gate in this upper bound. At fixed \(m,g,k\), write \(D=a g,\ E=m c k\). On every originally retained row \((D E,N)=1\) and \((D,E)=1\) since \(D f+E h=N\). Keep this base outer compatibility, and allow all positive \(f,h\) in the new smooth central interval, not only those in the original \(W\) gate.

Sieve the genuine primes \(f,h>W\) jointly by a universal upper Rosser--Iwaniec \(\beta\)-sieve on \(f h\), with support \(d\le N^{.0001}\), primes \(q\le N^{.000001}\) (fixed large sieve ratio). Its coefficients are independent of the varying \(D,E\), of absolute value at most one, and give a nonnegative majorant. See the standard upper-weight fundamental lemma as specified in [Kurlberg et al., §2.1](https://kurlberg.github.io/eprints/2dscar.pdf). Expand each squarefree \(d\mid f h\) into \(d_f\mid f,\ d_h\mid h,\ [d_f,d_h]=d\), with coefficient \((-1)^{\omega((d_f,d_h))}\); this is the exact inclusion--exclusion at a prime dividing both. Put \(j=(d_f,d_h)\). Compatibility is \(j\mid N\), \((D,d_h)=1\), \((E,d_f)=1\), and the base gcd. This follows prime by prime from the outer target units: a factor from \(D\) and \(d_h\), or from \(E\) and \(d_f\), cannot divide \(N\), while a shared \(d_f,d_h\) prime must divide \(N\). Divide both products and target by \(j\). After the independent cross masks the two products \(D d_f/j,E d_h/j\) are coprime precisely under the already required base gcd; the converse follows from the same local cases. Here \(j\le \operatorname{rad}(N)\le L^{B_0}\). The reciprocal (Poisson plus Bettin--Chandee) estimate applies to these enlarged products on dyads, all in \([N^{.49},N^{.51}]\) with exponents differing from \(.5\) by at most \(.0001+o(1)\). Its signed nonzero bound has a uniform power margin \(>.015\), and the total number of \((d_f,d_h)\) is at most \(N^{.0002}\). The \(m,g,k\) counts are subpower, and the failure weight separates exactly by expanding \(\prod_j(1-A_j(a)H_j(c))\) into log-power many products of independent \(a\)- and \(c\)-functions. Thus the aggregate nonzero spectral cost is power-small, even after the old \(L^2\tau(m)\) envelope. Here the primality majorant is used only for an **absolute positive** upper, not inside the signed covered calculation.

For the zero term reassemble this same sieve at fixed base \(D,E\). On their compatible progression the actual number \(\rho(q)\) of roots for \(f h=0\pmod q\) is \(1\) if \(q\mid N D E\), otherwise \(2\). At \(q\mid N\) both roots coincide because \(D,E\) are units; at \(q\mid D\) or \(q\mid E\) exactly one form is a nonzero constant, by the same target unit condition. In particular \(\rho(2)=1\), since the target is even. At each \(d\) the split density is exactly \(\rho(d)/d\): the pair \(d_f,d_h\) contributes \(j/(d_f d_h)\) when compatible, with the above inclusion--exclusion sign. The positive upper-sieve model therefore is
\[
   \ll \frac{N}{D E}\prod_{q\le N^{.000001}}\left(1-\frac{\rho(q)}q\right)
   \ll \frac{N}{D E L^2}\,(\log L)^{O(1)} .
\]
Indeed the root count is uniformly of sieve dimension at most 2 with the usual prime Mertens bound, and the product differs from the model \(\rho(2)=1,\rho(q)=2\ (q>2)\) only by a bounded power of \(\log L\) uniformly for \(NDE\le N^{O(1)}\). The model is nonnegative, as it is the CRT expectation of the nonnegative sieve majorant. It is therefore legitimate to drop the base compatibility and the units on \(a,c,m,g,k\) in the *upper bound* after taking this positive estimate. Both prime log weights are now paid by the genuine simultaneous \(L^{-2}\). Neither was lost in an unsigned one-leg harmonic.

At fixed \(m\) the independent log-harmonic intervals of \(a\) and \(c\) in this positive upper have total log widths \(O(L^\delta)\) each. Their bank failures satisfy
\[
 \sum_{a,c}\frac{1-C(a,c)}{a c}
       \ll L^{2\delta} L^{-\kappa}+O_A(L^{-A}).
\]
To check it, use the same finite Boolean expansions and open actual avoidance of the subpower bank primes by ordinary CRT Bonferroni counts for \(a,c\) separately. At the omitted degree \(L^{.1}\), the label count and maximum product are \(\exp(O(L^{.3}))\), far below the polynomial \(a,c\) scales, with factorially small reciprocal errors. Partial summation gives the harmonic masses even on shorter real intervals, with arbitrary absolute log accuracy. The model at each prime on each of \(a,c\) is the exact divisor density \(1/q\), independent across the two variables. At each family the avoidance of its entire left bank has probability bounded below by a positive constant depending on fixed \(K\); each of the \(K\) right colors has an independently positive hit probability. Thus each joint success model is bounded below uniformly, families are disjoint, and \(s\asymp_K\log L\) gives the above fixed \(\kappa>0\). No independence of actual simultaneous prime pairs was assumed to derive this bound.

Finally \(\sum_{m\le S^C}\tau(m)/m\ll(\log S)^2\), and \(\sum_{g,k\le e^{4L^\delta}}1/(g k)\ll L^{2\delta}\). The total missed contribution is \(O(N(\log L)^{O(1)}L^{4\delta-\kappa})+o(N)=o(N)\) at the stipulated parameter order. Together with covered cancellation and the literal boundary errors this proves the deletion (2). Do not combine it with the earlier low-\(\Lambda\)-cut proof as if the underlying Type II terms agreed.
