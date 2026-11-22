# The genuine prime-cofactor exterior at subpower quotients

Use [PolynomialNative.md](PolynomialNative.md) at an actual even
\(N\) with \(\operatorname{rad}(N)\le L^{B_0}\), \(B_0\) fixed,
and fixed positive polynomial cutoffs for its four factors.
Take \(I\subset[N/S^{C_0},N/S]\) for fixed \(C_0>1\); this
is inside its fixed-gap range for sufficiently large \(N\).
Keep both \(A,C\) **genuine primes** in addition to \(f,h\),
and retain their original weights: only \(f,h\) have
logarithmic prime weights. All other literal native
conditions remain. Take any interval \([M_-,M_+]\) on the
actual \(m\)-coordinate and write \(V_m=1+\log(M_+/M_-)\).
One may intersect it beforehand with the necessary
\(c S\le m\le C S^{C_0}\) from the original \(I,J_0\);
constants in these two bounds depend only on the fixed
compact support.

On any disjoint union of qualifying dyadic boxes as in
[PolynomialNativePrimeCohort.md](PolynomialNativePrimeCohort.md)
(fixed two-free exterior margin \(\delta>0\)), the signed
score satisfies
\[
   O\big(N\mathfrak S(N) V_m(\log\ell)^c\ell^{-\kappa/2}\big)
       +O(NL^{-1})                                                \tag{1}
\]
for some fixed \(c,\kappa>0\). Here
\[
 \mathfrak S(N)=2\prod_{p>2}\left(1-\frac1{(p-1)^2}\right)
               \prod_{p\mid N,\ p>2}\frac{p-1}{p-2}
\]
is the actual even-target singular factor. In particular
\(V_m\le\ell^{\kappa/4}\) gives \(o(N\mathfrak S(N))\) on
the entire indicated **untagged** genuine prime-cofactor
exterior. The whole subpower band can have log width
\(\asymp\ell^4\), and is not claimed. Nor does this
evaluate other native ranks, nonexterior boxes, arbitrary
radicals, or a binary prime count. No credits are added
across overlapping estimates.

The physical \(m\) must be an outer coordinate in every
qualifying box: leaving it free would require the outer
product \(u C h\le N^{1-\delta}\), where \(u\) is the
other left prime. But \(C h=y/m=N^{1-o(1)}\) on these
actual rows and \(u\) has a fixed positive polynomial
lower exponent. Thus the two free coordinates are
genuine primes in the positive calculation.

## 1. Tiny lower banks and the ordinary upper plant

Use the [tiny projected comparison](../nearfull_high_vaughan/TinyTagProjection.md),
with \(K\) fixed after the required logarithmic precision.
Choose \(s_0\asymp_K\log\ell\) disjoint lower \(K\)-color
families with uniformly separated exponent windows
\(1<\theta_-\le\theta_\nu\le\theta_+<2\).
They can be obtained by equally shifting an inner fixed
\(K\)-grid by steps \(2\log 2/\log\ell\), taking at most
\((\log\ell)/(100K)\) shifts and fixed spare gaps at the
ends. Thus each color's prime interval in \(\log p\)
is disjoint from all the other such intervals,
the within-family gaps stay fixed, and the prime harmonic
law in \(1\bmod 4\) supplies masses in \([1/4,1/2]\).
All these lower primes are target units for large \(N\),
since even their minimum exceeds every fixed power of \(L\).
They lie **below** \(z=\exp(\ell^2)\), as well as below \(T_y\).

Use the unchanged ordinary upper plant \(B_2\) of
[PolynomialNativePlantedPairs.md](PolynomialNativePlantedPairs.md)
with exponents in \((.15,.2)\) of \(L\).
These upper primes exceed every allowed \(m\).
In the first replacement use \(R_z\), the normalized
\(z\)-rough integer model, in place of that proof's \(R_1\),
and plant exactly one upper prime per color in \(A\) to
exponent one. The normalization is the same
\(D_{B_2}\prod_\nu V_{2,\nu}\) in the denominator;
the prime alphabets for the plant and \(R_z\) are disjoint.
The second replacement uses the old \(R_2\), rough beyond
the ordinary upper tags. The exact character means and
prime replacements of that proof apply: the unit/arc
primes are below \(z\), all model openings have
subpower label counts, and all four prime slots and
all grouped source scales are polynomial. Unweighted
prime \(A,C\) are still modeled with the individual
\(1/\log A,1/\log C\) factors.

Cover the original \(m\) by its first lower family
with a hit in every color, retaining all earlier failures.
Extract the literal lower tag \(w\mid m\) with the usual
normalized hit allocation and remove bank square rows by
actual \(p^2\mid y\). Writing \(m=w m'\), the true coefficient
is
\[
   Q_T(wm')=\sum_{s\mid w}\mu(s)
               \sum_{\substack{d\mid m'\\ds<T}}\mu(d)
                                                                 \tag{2}
\]
on these square-free-as-to-\(w\) rows. Use the actual fine
\(y\)-mesh (with log-power precision in \(L\)) for the
\(m\)-endpoint and \(T_y\) cutoffs. A moved \(m\)-endpoint
has \(m\mid y\); a moved score divisor has \(d\mid y\).
Thus the absolute errors have the same actual-multiple
bounds as in the planted proof, with \(S^{C_0}\) in place
of the previous polynomial \(m\)-count. At fixed \(T\)
smooth the one \(ds<T\) cutoff in (2) in a relative
\(L^{-F}\) collar. A changed \(ds\) is a literal divisor
of \(y\) near \(T\asymp S\), with unweighted count
\(O(N(L^{-F}+1/S))\) at a single mesh cell. Choose this
\(F\) after the fixed cell count, before selecting \(K\);
crossed divisor moments pay the resulting total.
The Mellin split is one-dimensional, preserves the
strict cutoff outside the paid collar, and gives bounded
entering-label phases on \(s\). The frozen physical
\(m=w m'\) interval is likewise separated by one
dimension after smoothing actual \(m\mid y\) collars.
Restore bank-square rows in the opened model without any
tag-dependent gcd mask; all such artificial terms still
have \(w\mid m\mid y\) and \(p^2\mid y\), and the same fixed
divisor envelope.

Now use the tiny projected comparison on \(x=A f\),
first replacing \(A\) and then \(f\), as in the planted proof.
Both source factors are \(z\)-rough even after the
models, since the upper planted primes exceed \(z\).
The two tiny bank Mellin phases (from \(s\) and \(w\))
together are a product of bounded label multipliers.
Prior lower failures are unchanged under the selected
extraction. Sum back the actual m-tag allocations after
these replacements (with square/collar errors already paid).
For the second projection use the ordinary planted
upper tag on \(A\), and replace \(C,h\) from the source
\(y=(m C)h\) exactly as in the planted proof. The actual
\(m\) is automatically free of all upper-bank primes.
The nonunit small-arc split of the grouped \(m C\) and
the sum at fixed \(m\) by its reciprocal divisor harmonic
therefore apply unchanged. All residual second moments
remain \(O((N/Y)L^{O(1)})\), since they count literal
factorizations, including (2)'s true residual divisors.
The analytic comparison errors are arbitrary-log small.
Only the fully integer-model principal with the true
lower-bank \(m\) masks needs the next observation.

## 2. Signed \(m\)-harmonic under tiny divisibility masks

After the two projections use the same ordinary exterior
CRT as in [PolynomialNativePlantedPairs.md, §3](PolynomialNativePlantedPairs.md).
Here \(m\) is outer. At fixed real \(x\) and all other
outer variables and opened labels, the required signed
principal is \(Q_T(m)F(m)/m\) on a real \(m\)-interval
in \(cS\le m\le C S^{C_0}\), with polynomial unit mask
\((m,H)=1\), a fixed log-bounded supremum and variation
of \(F\), and the precise lower-bank hits and earlier
failures. The only \(m\)-dependent coprimality is against
the target and the fixed opposing product. There is no
same-side coprimality condition inserted.

Expand the bank Booleans into avoidance patterns
and then into actual squarefree labels \(b\mid m\)
with successive Bonferroni degrees
\(r\asymp_D \ell/\log(2\ell)\). The total mass \(W\)
of bank prime reciprocals is \(O(\log\ell)\).
All retained and first omitted labels have size
\(\exp(O_D(\ell^{1+\theta_+}/\log(2\ell)))=S^{o(1)}\);
the count of assignments is bounded by the same
form, with changed constants. The bank Boolean count is
at most \((2^K+1)^{s_0}\le \ell^{O(1)}\) with exponent fixed
independently of \(K\). For the positive omitted-degree
error on a true \(m\)-dyad \(M\le m\le2M\), use the exact
no-floor bound
\[
     \sum_{\substack{M\le m\le2M\\ d\mid m}}\frac1m\le\frac2d .
\]
It follows by counting all positive multiples up to \(2M\).
Thus \(\sum(\sum_{t\mid m,t\le C S}1)^2/m\) is at most
\(2\sum_{d,e\le C S}1/[d,e]=\ell^{O(1)}\), even when
\(M\asymp S\). The square harmonic of the positive
omitted count is at most twice \(\sum_{b,c}1/[b,c]\)
over degree-\(r\) labels. Grouping their union by
\(j\in[r,2r]\) bounds this by
\(O(\sum_{j=r}^{2r}(4W)^j/j!)\).
Cauchy and a sufficiently large constant in \(r\)
give arbitrary-log small omission against \(|Q_T|\),
without a floor of size \(S^2/M\).

At fixed retained \(b\), if \((b,H)>1\) there is no
term. Otherwise write \(m=b n\); the exact formula,
even if \((b,n)>1\), is
\[
   Q_T(bn)=\sum_{s\mid b}\mu(s)
        \sum_{\substack{d\mid n,\ (d,b)=1\\d<T/s}}\mu(d).
\]
All primes of \(b\) already occur in \(m\), which gives
this squarefree decomposition. The \(n\)-scale and the
cutoff \(T/s\) both exceed \(S^{.8}\) for large \(N\).
For \(d>S^{1/4}\) fix \(n/d\) and use the uniform
masked signed \(\mu(d)/d\) tail. For \(d\le S^{1/4}\),
after opening the divisor count the \(H\)-units in the
remaining integer using the Rankin unit-floor bound
at \(\sigma=1-1/(10\ell)\), not \(\tau(H)\) at this
subpower length. Its length scale still exceeds
\(S^{.5}\). The real main then contains the complete
masked short \(\mu(d)/d\) up to \(S^{1/4}\), which is
arbitrarily log-small by the proof of
[PolynomialNative.md, (3)](PolynomialNative.md),
with mask \(b H\). These estimates hold for any real
subinterval of the dyad; they do not presume
\(n\ge T/s\). Recover the factor \(1/b\) and sum the
\(s\)-labels and the outer \(b\)'s by
\(\sum_b\tau(b)/b\le\prod_{p\text{ in banks}}(1+2/p)
=\ell^{O(1)}\).
Every principal term on the covered part is thus
arbitrary-log small. The exterior integer floors
have the same fixed power reserve as before. This
establishes \(O_D(N L^{-D})\) for the signed sum on
the union of actual successful lower banks.

## 3. Moving exact cutoff and genuine prime upper on the missed rows

Let \(\mathcal F(m)\) indicate that all tiny lower
families fail. Their independent divisor model, with
actual hit probabilities \(1/p\), has mass
\(O(\ell^{-\kappa})\) for some fixed \(\kappa>0\):
each color has fixed positive mass, each family has
a fixed positive chance to succeed, and there are
\(\asymp_K\log\ell\) disjoint families.
The same upper holds for the literal reciprocal
\(m\)-harmonic, with factor \(V_m\) and arbitrary
errors \(O_D(L^{-D})\) *relative to the model count
accuracy*, by the preceding Boolean and Bonferroni
opening. For this unsigned count open \(b\mid m\),
count \(\log(M_+/M_-)/b+O(1/M_-)\), and include the
omission error via its factorial first moment. All label
counts are \(S^{o(1)}\), so the true integer floor is
power-small in \(S\). It is enough to use
\[
          \sum_{M_-\le m\le M_+}\mathcal F(m)/m
                    \ll V_m\ell^{-\kappa}+O(L^{-2}).               \tag{3}
\]

For the **positive** upper use a separate coarse
\(y\)-partition into \(O(1/\Delta)\) cells of length at
most \(\Delta N\), \(\Delta=\ell^{-E_0}\) with \(E_0\)
a sufficiently large fixed number. Short terminal
cells may use an upper length \(\Delta N\).
At fixed \(m,u,v\) the two outer true prime factors
\(u,v\) are independent after enlarging to their full
polynomial ranges. The two free true prime factors
in a given \(y\)-cell lie on affine forms with parameter
length at most \(X=\Delta N/(muv)\), up to a fixed
constant. This **cell's** upper length satisfies
\(X\gg \Delta N^\delta\) on the actual exterior choices.
Apply the positive dimension-two upper sieve with
a fixed polynomial depth and level, chosen smaller than
this scale and below the least true prime scale.
The local number of roots is 1 at \(p\mid Nmuv\),
2 elsewhere, including 1 at 2; coprimality of the two
actual outer products and their target units justify these
counts. Formulae remain the same on the shortened
parameter interval, and the sieve floor
\(N^{o(1)}\) times its level has a fixed power reserve
relative to \(X\). Multiplying by both original
prime logs, the **positive** score without \(Q\)
per tuple and cell is bounded by
\[
      O\left(\frac{\Delta N\,\mathfrak S(N)\,(\log\ell)^c}
                        {muv}\right).
\]
The target-root inflation has been kept as the exact
\(\mathfrak S(N)\): at extra primes dividing \(muv\)
its ratio is \(\prod_{p\mid muv,p>2}(p-1)/(p-2)\).
The true \(u,v\) are single polynomial-sized primes, and
the \(m\)-ratio is \(O(m/\varphi(m))=O(\log\ell)\) since
\(m\ll S^{C_0}\). The two outer prime reciprocals each
cost \(O(1)\) over their entire polynomial ranges.
All six possible choices of input/free coordinates
can be enlarged for this positive upper without a cost
for every dyadic box; as noted, only choices with \(m\)
outer occur here.

In this cell choose \(T_j=y_j/B\) at its midpoint.
The change in \(Q_y(m)\) from \(Q_{T_j}(m)\) is bounded
by the number of actual divisors of \(m\) in
\(|d-T_j|\ll\Delta S\). For every such \(d\),
\(\sum_{M_-\le m\le M_+,d\mid m}1/m\ll V_m/d\):
write \(m=d n\), count the ordinary harmonic interval,
and if it begins below 1 simply start at 1.
Consequently the added \(m\)-harmonic is
\(O(V_m(\Delta+1/S))\). The cell factor \(\Delta N\)
in the genuine sieve upper is retained in this error.
Summing all cells thus costs only
\(O(N\mathfrak S(N)(\log\ell)^c V_m(\Delta+1/S))\).

Finally use [de la Bretèche–Dress–Tenenbaum, *Remarques
sur une somme liée à la fonction de Möbius*, equation (1.5)](https://tenenb.perso.math.cnrs.fr/PPP/Sxz.pdf),
the uniform **sharp** truncation bound
\(\sum_{n\le X}|\sum_{d\mid n,d\le z_0}\mu(d)|^2\ll X\)
for all \(X,z_0\ge1\). For the strict \(T_j\) take
\(z_0=\lceil T_j\rceil-1\). Harmonic dyads give
\(\sum_{M_-\le m\le M_+} Q_{T_j}(m)^2/m\ll V_m\)
uniformly in \(j\). Target exclusions can be dropped
only in this **positive** norm bound; no assertion
of a conditional second moment on a rare target-unit
subset is used. Cauchy with (3) gives
\(O(V_m\ell^{-\kappa/2})\) for
\(\sum |Q_{T_j}(m)|\mathcal F(m)/m\).
Multiply by the genuine per-cell bound with its
factor \(\Delta\), then sum \(O(1/\Delta)\) cells.
Taking \(E_0\) large absorbs the moving-cutoff error.
Together with the entire tiny-bank covered part
this proves (1).
