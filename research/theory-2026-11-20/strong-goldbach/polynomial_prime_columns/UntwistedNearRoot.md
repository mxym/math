# Untwisted near-root deletion in the actual giant-prime remainder

Let \(J_0\Subset(0,1)\) be fixed, \(p\in NJ\), \(J\subseteq J_0\)
any subinterval, \(p\) a genuine prime, \(y=N-p\), \(L=\log N\),
\(\ell=\log L\), \(S=\exp(\ell^4)\), and
\(M=|J_0|N\mathfrak S(N)\). Take fixed \(C_0,C_1>0\) and let
\(\mathcal I_N=[\sqrt N\,S^{-C_0},\sqrt N\,S^{C_1}]\).
Every actual divisor prime \(r\in\mathcal I_N\) retained below may
also be restricted by the original lower/upper cutoffs. Put \(m=y/r\)
and
\[
 T_y=y/B',\qquad
 Q_y(m)=\sum_{\substack{d\mid m\\d<T_y}}\mu(d),
 \qquad B'\asymp N/S \ \text{independent of }y .
\]
The proof also covers \(T_y=S\) fixed (row-relative \(B'=y/S\)).
Use the literal strict inequality \(d<T_y\); no endpoints are ignored.
Only in the absolute low-rank bound (1) can \(T_y\) be arbitrary,
because the pointwise bound used there is independent of the cutoff.

The main result concerns the actual remainder of the
[giant prime-divisor reduction](../giant_prime_divisor_remainder/Proof.md).
For every fixed \(B>0\), at each sufficiently large even \(N\) with
\(\operatorname{rad}(N)\le L^B\), and for **any** subset \(\mathcal R\)
of the true primes in \(\mathcal I_N\), we prove
\[
 \sum_{\substack{p\in NJ,\ p\ {\rm prime}\\
                     r\mid y,\ r\in\mathcal R}}
      (\log p)(\log r)Q_y(y/r)=o(N)
 \tag{5}
\]
uniformly in \(J\subseteq J_0\), \(\mathcal R\), and the stated fixed
comparability constants of \(B'\). There is no rank, parity,
squarefreeness or roughness restriction in (5). It is a signed
deletion in this specific near-root window, not an absolute bound.

In the original remainder take \(C_0\ge2\), so that its lower
threshold \(U=\sqrt N/(S L^C)\) lies in \(\mathcal I_N\) for
all large \(N\), for any fixed \(C\) used in that reduction.
The only surviving primitive prime marks of the original
remainder are then \(r>\sqrt N S^{C_1}\). Their total is not
controlled here. In addition we prove an absolute deletion on
a growing low-rank sector at **every** even \(N\), and a signed
over-root mixed-column extension used to illuminate the distinction
between the original sum and its parity-twisted version. In
particular no unsigned over-root Bombieri--Vinogradov theorem
is asserted.

## 1. Unconditional absolute deletion of a growing-rank near-root sector

For all even \(N\), uniformly in \(J\subseteq J_0\),
\[
 \sum_{\substack{p\in NJ,\ p\ {\rm prime}\\
       r\mid y,\ r\in\mathcal I_N,\ r\ {\rm prime}\\
       \Omega(m)\le \lfloor\ell/3\rfloor}}
   (\log p)(\log r)\,|Q_y(m)|
   \ll_{J_0,C_0,C_1} N\mathfrak S(N)L^{-c}\ell^7,
 \qquad c=\frac{2-\log 6}{3}>0 .
 \tag{1}
\]
Here \(\Omega\) includes multiplicities. There is no roughness mask.
Both actual orientations of \(r\) are allowed (at most two because
\(r>N^{.49}\) eventually).

Discard \(p\mid N\), a bounded set in \(NJ_0\), at cost
\(L^2 2^{\ell/3}N^{o(1)}\); thereafter \((N,y)=1\).
Suppose \(\Omega(m)=k\le K=\lfloor\ell/3\rfloor\) and peel its
largest actual prime \(q\). If \(q^2\mid m\), then \(q^2\mid y\)
and \(q\ge m^{1/k}\ge\exp(.45L/K)\) for sufficiently large \(N\)
(the central constants and \(S^{C_1}\) are harmless).
Open that genuine square and count at most
\(\sum_{q\ge\exp(.45L/K)}N/q^2\ll N\exp(-.45L/K)\) integers.
Multiplying by \(L^2 2^K\) and the at most two \(r\) orientations
preserves a saving stronger than every fixed negative log power.
No unrestricted \(\tau(y)\) estimate is needed in this deletion.

For the remaining rows fix \(r\) and \(h=m/q\), with
\(\Omega(h)=k-1\). Set \(Y=N/(rh)\). Whenever the physical row is
possible, \(q\asymp_{J_0}Y\) and \(Y\gg_{J_0}\exp(.45L/k)\).
Drop order and additional cuts for an upper count, keeping the two
genuine prime forms \(q,N-rh q\) in the central interval.
Use a dimension-at-most-two upper sieve in the \(q\) variable at
a small fixed power of \(Y\), well below both actual prime sizes.
At a prime \(\lambda\nmid rhN\) there are two distinct roots;
at \(\lambda\mid N\) the roots coincide; at
\(\lambda\mid rh\) only \(q=0\) is a root, since \((rh,N)=1\).
At \(2\) there is one root, as \(N\) is even and \(rh\) is odd.
Thus the resulting upper count is
\[
 \ll_{J_0} Y\,\mathfrak S(N)\,
           \prod_{\substack{\lambda\mid rh\\\lambda>2}}
                    \frac{\lambda-1}{\lambda-2}
                      /(\log Y)^2 .
 \tag{2}
\]
The CRT floors with a sieve support of a small fixed power of \(Y\)
are \(O(Y^{1/3})\), say, including divisor powers; since \(Y\) grows
at least as \(\exp(.44L/k)\), this is absorbed uniformly at the
claimed main scale. The partial Euler correction from excluding
target primes beyond the sieve limit does not enlarge the bound.
The product over \(rh\) in (2) is \(O(\ell)\): compare its factors
with \((1-1/\lambda)^{-1}\), whose quotient Euler product converges
absolutely, split at \(L^2\), use Mertens below and
\(\sum_{\lambda\mid rh,\lambda>L^2}1/\lambda\ll 1/L\).
These estimates apply even for repeated small factors in \(h\).

Bound \(|Q_y(m)|\le\tau(m)\le2^k\), and use both weights
\(\log p,\log r\le L\). Formula (2) therefore costs at most
\[
 C k^2\ell\, N\mathfrak S(N)\frac{2^k}{rh}.
\]
Actual prime reciprocal mass on \(\mathcal I_N\) is
\(O_{C_0,C_1}(\ell^4/L)\) by summing its \(O(\ell^4)\) constant-ratio
dyads and the prime upper bound in each; no short interval PNT needed.
For the other factor put \(z=1/3\). Complete multiplicities are
included by the positive Euler product:
\[
 \sum_{1\le k\le K}2^k\sum_{\substack{h\le N\\\Omega(h)=k-1}}\frac1h
 \le 2(2/z)^K \prod_{\lambda\le N}(1-z/\lambda)^{-1}
 \ll L^{(1+\log6)/3}.
\]
Combine this with \(K^2\ell\ll\ell^3\) and the \(r\)-harmonic to
obtain (1). The high-rank part and all marks outside
\(\mathcal I_N\) remain unrestricted.

## 2. Signed over-root extension of the genuine mixed column

For this section and §§3–4 assume \(\operatorname{rad}(N)\le L^B\)
with fixed \(B\). Let \(0<\alpha<\beta<1\), and let
\(\mathcal B\subset[N^\alpha,N^\beta]\) be any set of integers \(b\)
coprime to \(N\). The proof in the [prime column](Proof.md) and its
[composite extension](CompositeColumns.md) extends for signed cancellation (not for unsigned main terms):
\[
 \sum_{b\in\mathcal B} W_b
   \left|\sum_{\substack{p\in NJ,\ p\ {\rm prime}\\p+bn=N\\
                                     P^-(n)>w}}
                    (\log p)\mu(n)\right|
 \ll N L^{-\kappa}\sum_{b\in\mathcal B}
               \frac{W_b E_{w,b}(N)}{\varphi(b)}
                     +N L^{-10}.
 \tag{3}
\]
As there, \(0\le W_b\le L\), \(w=1\) or \(w=\exp(L^\gamma)\)
with \(0<\gamma\le.15\), and \(E_{w,b}\) uses the local probabilities
\(d_b(r)=1/r\) at \(r\mid b\), \(1/(r-1)\) otherwise, with
\(r\mid N\) omitted. The last error power \(-10\) may be replaced
by any fixed negative exponent after choosing the required
precision. The bound stays uniform in \(J\subseteq J_0\).
For the parity-twisted application take \(w=1\); one can also place a
fixed-by-\(b\) mask \(1_{(n,d_b^\star)=1}\) where
\(d_b^\star\le\exp(O(\ell^4))\) and contains only primes below the
active bank. This extension does not assert an unsigned model in
any over-root range.

**Single change to the existing column estimates.** The prior
\(\beta<1/2\) requirement was used to *evaluate* the missed-bank
weight by BV for the true prime \(p\). It suffices for the signed
estimate to upper bound that nonnegative missed mass. Fix \(b\),
let \(X_b=N/b\ge N^{1-\beta}\), and keep the literal progression
\(p=N-b n\), \(n\) in the central interval selected by \(J\).
Let \(\mathcal P_{\rm sm}\) consist of all bank primes and the
primes \(\le w\) needed for the quotient roughness opening, all
\(\le\exp(2L^{.2})\). Put \(z_0=N^{(1-\beta)/20}\) and use the
dimension-one upper beta sieve in the prime form \(N-bn\) on
prime labels \(\lambda\le z_0\) outside \(\mathcal P_{\rm sm}\)
and not dividing \(b\), with level \(D_0=N^{(1-\beta)/4}\).
It is a nonnegative pointwise majorant for the actual prime form.
The usual one-root densities give a dimension-one sieve bound
uniformly when primes are deleted. All labels dividing \(N\)
may be kept whenever they are in this external alphabet:
in the prime form there is still one root there, and it is
not necessary to remove them. There are no roots at primes
dividing \(b\).

Expand the product of the exact missed-family indicators as in
the composite column proof (at most \(L^{O(1)}\) avoidance
clauses). In each clause additionally require the prime form
to avoid **all** \(\mathcal P_{\rm sm}\) primes (outside \(b\)),
and impose the quotient roughness mask. This restores the actual
p-prime restrictions at the entire bank: omitting them in the
Euler product would lose the needed logarithmic saving.
For each clause open these simultaneous small-prime avoidances
by Bonferroni at successive depths about \(L^{.1}\).
At each prime there are at most two distinct roots, the union
of the prime-form root and a selected quotient root \(n=0\).
The opened moduli and all root-choice multiplicities are
\(N^{o(1)}\). The unsigned reciprocal error is bounded by
\((O(\log L))^{L^{.1}}/(\lfloor L^{.1}\rfloor!)\) times the
absolute divisor harmonic, hence smaller than every log power.
Its floor cost, including the outside beta label and all
clauses, is \(N^{(1-\beta)/4+o(1)}\) per \(b\). One may
first apply the two Bonferroni enclosures to the nonnegative
external-sieve weight and then expand the latter, or estimate
each external label remainder by its absolute value. These
give the same bound and preserve the sign of the true upper.

Since the two alphabets are disjoint, the principal for each
clause is the external one-dimensional sieve multiplier times
its exact CRT local density. After restoring the short alphabet,
the prime-form local factor is
\(\prod_{\lambda\le z_0,\lambda\nmid b}(1-1/\lambda)
 \ll_\beta b/(\varphi(b)L)\), including the primes dividing
\(N\). Conditional on avoidance of those prime roots,
the n-hit probability is exactly \(1/(\lambda-1)\) for
\(\lambda\nmid bN\), \(1/\lambda\) for \(\lambda\mid b\),
and zero at \(\lambda\mid N\) (their roots coincide).
These are independent across the small primes by CRT.
Thus exact Boolean expansion, followed by recombination of its
principal, leaves the factor \(E_{w,b}\) and the product of the
missing-family probabilities. Each family has success probability
bounded below independently of \(b\) as before, so this last
product is \(O(L^{-\kappa_0})\).
Multiplying by \(\log p\le L\) proves the true missed-bank upper
\[
 \ll N E_{w,b} L^{-\kappa_0}/\varphi(b)
        +X_bL^{-A}+N^{(1-\beta)/4+o(1)}
\]
for any requested fixed \(A\). Summing the floor cost up to
\(N^\beta\) has a strict power reserve. If the additional
\(d_b^\star\) mask is used it can be dropped for this positive
missed upper. This works with shrinking prefixes inside \(J_0\);
no unsigned over-root BV is used.

**Covered parts.** The rest is literally the existing projected
comparison and Type I. Keep the first active bank and write
\(n=u v,\ N-p=u h,\ h=b v\). The coefficient on \(h\) is
divisor-bounded because it sums over \(b\mid h\), now with
\(b\le N^\beta\); neither the [projected mean square](../target_slope_switch/Proof.md)
nor its small-radical major estimate takes \(b\) as an external modulus.
For a varying \(d_b^\star\) the mask is retained as
\(1_{(h/b,d_b^\star)=1}\), since \(u\) uses larger bank primes.
It does not affect the divisor/moment bound on that residual.
Both Vaughan Type II slots of the source still have fixed
polynomial length on choosing \(D=N^{(1-\beta)/16}\).
This and the unchanged arbitrary-log covered packet hold
uniformly in the interval by the original log-mesh argument.
Square rows on active-bank primes have the same direct bound.

For Type I fix the outer \(b\) and the subpower quotient
avoidance label \(g\). The reduced residue for the quotient
variable after \(n=g v\) has modulus \(de\,\operatorname{rad}(N)\)
as in the prior proof, where source \(d\le D^2\) and \(e\)
is a subpower presieve label. The actual free quotient scale
is \(N/(bg)\ge N^{1-\beta-o(1)}\), so there remains a fixed
power reserve below the square root, and the total floor exponent
is at most \(\beta+(1-\beta)/8+o(1)<1\). If the extra mask is
present, impose it as \(1_{(v,d_b^\star)=1}\) (discard
\((g,d_b^\star)>1\) first) and use the exact convolution
\[
 \mu(v)1_{(v,g d_b^\star)=1}
   =\sum_{\substack{j\mid v\\ \ell\mid j \Rightarrow \ell\mid g d_b^\star\ (\ell\ {\rm prime})}}
                   \mu(v/j).
\]
The displayed support shorthand means every prime dividing
\(j\) divides \(g d_b^\star\), including \(j=1\).
The extra \(\omega(d_b^\star)=O(\ell^4)\) adds only \(N^{o(1)}\)
to the count of high \(j\)'s and at most a fixed log power to
the reciprocal weight. If a prime of this support also divides
\(de\,\operatorname{rad}(N)\), the actual reduced class admits
no \(j\) divisible by it, so omit those \(j\) before applying BV.
No assumption \((d_b^\star,b)=1\) is needed. The same elementary
large-\(j\) floor and actual maximal Möbius BV estimates apply.
This proves (3) by duality, without changing its hypotheses on
the genuine \(p\) and without an unsigned density conclusion.

## 3. Exact parity-twisted effect on the published near-root residual

Under the small-radical hypothesis, for the same actual quantities
as §1,
\[
 \sum_{\substack{p\in NJ,\ p\ {\rm prime}\\
        r\mid y,\ r\in\mathcal I_N,\ r\ {\rm prime}}}
      (\log p)(\log r)\,\mu(m) Q_y(m)=o(N).
 \tag{4}
\]
This is a parity-twisted test of the original score, not a bound on
its untwisted total. Both orientations of the \(r\)-mark are allowed.
The identity
\[
 \mu(m)Q_y(m)
   =\sum_{\substack{d\mid m,\ d<T_y\\\mu^2(d)=1}}
                   \mu(m/d)1_{(d,m/d)=1}
\]
is exact also on nonsquarefree \(m\) (both sides then vanish).
Thus \(b=rd\) is the genuine outer modulus, \(\mu(n)\) is the
actual quotient coefficient with \(n=m/d\), and set
\(d_b^\star=d\). Since \(d\ll S\) is subpower and \(r>N^{.49}\)
is prime, \(r\) and \(d\) are uniquely recovered from \(b\).
If an actual \(b\) divides \(y\), the central prime source and
\((p,N)=1\) enforce \((b,N)=1\). Terms with \(p\mid N\)
can again be discarded. In particular no same-variable tag
or inconsistent unit progression is put into (3).

For fixed central mesh cells of relative width \(\Delta\), freeze
the physical threshold \(T_y\) at a cell endpoint. For
\(T_y=y/B'\), take \(\Delta=(\log S)^{-3}\).
The only changed integer \(d\)'s are in an interval about
\(d\asymp S\) of width \(O(\Delta S+1)\). Its genuine harmonic
\(\sum 1/\varphi(d)\ll\Delta+(\log S)/S\): open
\(d/\varphi(d)=\sum_{e\mid d}\mu^2(e)/\varphi(e)\).
Inside the corresponding true prime interval of length
\(O(\Delta N)\), the residue \(N\bmod rd\) is reduced and
\(rd\le N^{.5+o(1)}\). Brun--Titchmarsh on that interval gives
prime log weight \(\ll \Delta N/\varphi(rd)\), since
\(\log(\Delta N/(rd))\gg L\). This upper is on the literal
boundary terms, independently of any signed cutoff/apparent
BV input. Sum over cells and use
\(\sum_{r\in\mathcal I_N}(\log r)/\varphi(r)\ll\log S\).
The cost is \(O(N\log S(\Delta+(\log S)/S))=o(N)\).
For fixed \(T_y\) no mesh is needed.

Now apply (3) on each cell with \(w=1\), mask \(d_b^\star=d\),
and \(W_b=\log r\) for admitted moduli. The weighted harmonic
of all such moduli in a cell is
\(\ll(\log S)^2\), since \(r\nmid d\),
\(\sum_{d\ll S}\varphi(d)^{-1}\ll\log S\), and the true
marked \(r\) harmonic with its logarithm is \(O(\log S)\).
The \(O((\log S)^3)\) cells and this harmonic are \(L^{o(1)}\),
so \(L^{-\kappa}\) still gives \(o(N)\). This proves (4).
It balances the two squarefree cofactor parity classes of the
signed score \(Q_y\). It does not evaluate either parity class
on its own and does not detect an untwisted prime pair.

The all-target low-rank estimate (1) and the small-radical
twist (4) are separate results. The next argument, not a deduction
from parity balance, is what pays the original signed branch.

## 4. The original untwisted all-rank near-root branch

We now prove (5), for the literal original score and each
allowed choice of marked primes. This proof does not deduce
the untwisted estimate from the parity-twisted estimate (4).

Freeze \(T_y\) on the same physical mesh as in §3. Its signed
replacement on genuine primes costs \(o(N)\) by the independent
BT upper in that section, since no factor \(\mu(m)\) was needed
there. This justifies working with a fixed \(T\asymp S\) in each
mesh cell, with literal cutoff side \(d<T\). There are \(L^{o(1)}\)
such cells; all arithmetic estimates below permit this loss. The
case \(T_y=S\) is one cell. Use \(C(m)\) for the usual first-active
bank coverage indicator. All its active prime labels exceed
\(\exp(cL^{.15})\), hence greatly exceed both \(T\) and the
maximum of all short-divisor label choices. Also \(r\) is larger
than all its primes. Consequently the bank scope on \(m\) is
exactly that on \(y\), and is unchanged on dividing \(m\) by
any allowed \(d<T\).

**Actual missed rows.** Open \(|Q(m)|\le\sum_{d\mid m,d<T}1\).
For fixed true \(r,d\), the outer modulus is \(b=rd\) and
\(m/d=n\) has the same bank status as \(m\).
Therefore the actual missed-bank upper in §2 (not the signed
\(\mu(n)\) estimate) applies at this \(b\).
Its harmonic total with the genuine \(\log r\) is
\(O((\log S)^2)\). The CRT floor exponents from §2 have
fixed power reserve here; use for example \(\beta=.6\).
Thus the missed part is \(O(NL^{-\kappa_0+o(1)})\)
over all mesh cells, including the coefficient \(\log p\).

**Covered Type II.** As usual replace the genuine-prime source by
\(\Lambda(p)\,1_{P^-(p)>z}\), \(z=\exp(L^{.24})\), and keep
actual target units. Proper powers cost \(N^{1/2+o(1)}\)
with the divisor-power envelope and log weights. On the first
active bank, extract \(u\mid m\) with one prime from each color
and write \(y=u h\). The exact coverage normalization for the
chosen labels is independent of the short divisors \(d<T\).
No factor \(\mu(u)\) is introduced: the untwisted score is
unchanged when these large bank labels are removed from its
divisor alphabet. Away from the same negligible bank-square
rows as in the original proof, the new residual on \(h\), with
the sum restricted to the prescribed \(\mathcal R\), is
\[
 \left[\prod_{i<j}(1-U_i(h))
       \prod_{\nu=1}^K (1+\omega_{j\nu}(h))^{-1}\right]
     \sum_{\substack{r\mid h,\ r\in\mathcal R}}
                  (\log r)\sum_{\substack{d\mid h/r\\d<T}}\mu(d).
 \tag{6}
\]
Indeed \(u\) is coprime to the other active primes in \(h\)
after removing bank-square rows, and removing \(r\) has
no effect on any of the subpower bank counts. There is no
new size restriction on \(h\), which still satisfies \(h\ll N/u\).
The residual (6) is bounded by \(L\tau(h)^2\),
so its square mean costs fixed log powers as in the existing
small-radical Type II proof. The original rough Vaughan source
provides the same two target-unit polynomial slots, one with
its actual long Möbius coefficient. The projected minor and
small-radical major take this same divisor-bounded residual,
with its original separation from the source. They give
arbitrary fixed log saving in the covered Type II sum.
The exceptions for possible \(u^2\)-part overlap are unchanged:
actual \(q^2\mid y\) for a bank prime \(q\) lies in
\(O(N\exp(-cL^{.15}))\) integers, and finite divisor moments
pay the extra power \(\tau^2\).
No unsigned prime estimate at \(rd\) is asserted.

**Elementary covered Type I.** Open the same covered mask
\(C(m)\) as its exact signed \(L^{O(1)}\) sum of bank-avoidance
patterns, and use the actual rough condition on the source
free slot. In a Vaughan Type I term write \(p=a k\) with
\(a\le D^2\), \(D=N^{(1-\beta)/16}\), grouping as in the
original proof. The source coefficient is bounded by \(O(L)\),
with possible \(\log k\) weight. Retain \((p,N)=1\) and the
corresponding \((y,N)=1\). Open the avoidances by small quotient
labels \(g\) (bank primes) and small source labels \(e\)
(primes at most \(z\)), of Bonferroni depths about \(L^{.1}\).
One can omit all target prime divisors in these labels:
they never divide their respective variables on true unit rows.
Open the actual signed short divisor \(d<T,\ d\mid m\) as
well. Since \(d<T\ll\min\mathcal P_{\rm bank}\) and \(r\) is
large, \((d,g)=(d,r)=(g,r)=1\) exactly; thus \(dg\mid m\)
is the correct product test. The conditions are
\[
    ae\mid p,\qquad rdg\mid (N-p).
\]
Only \((ae,rdg)=1\) can occur under the true target unit masks.
Write \(R=\operatorname{rad}(N)\le L^B\). For each unit class of
\(p\bmod R\), CRT now gives one class modulo \(Rae rdg\)
and density \(1/(R a e r d g)\). Summing over the \(\varphi(R)\)
unit classes multiplies the interval integral divided by
\(a e r d g\) by \(\varphi(R)/R\), a scalar independent of \(d\).
The floor per unit class is \(O(L)\) also when
\(\log k=\log(p/a)\) is present, by ordinary partial summation. The quotient and source
Bonferroni remainder bounds can use \(|\mu(d)|\le1\) and
the positive high-degree factorial terms, with CRT in the
same two modulus alphabets. The absolute reciprocal mass
of \(d<T\) is \(O(\log S)\); every other retained reciprocal
sum costs a fixed log power. The first discarded reciprocal
factorial term is super-logarithmically small. Restoring
floors including both Bonferroni tails costs
\(N^{.5+(1-\beta)/8+o(1)}\), since the \(r\)-count is
\(N^{.5+o(1)}\) and all of \(d,e,g\) are subpower.
This is a fixed power reserve. In these elementary comparisons
no second prime variable is inserted into the CRT model.

For each fixed \(a,e,r,g\), the signed \(d\)-model is now
\[
       \sum_{\substack{d<T\\(d,Q)=1}}\frac{\mu(d)}{d},
       \qquad Q=aegrN .
 \tag{7}
\]
All remaining weights, interval endpoints, and Boolean coefficients
are independent of \(d\) after the mesh. The conditions
\((d,r g)=1\) are automatic, but can be included in \(Q\).
The mask \(Q\le N^{O(1)}\) is allowed in a uniform subpower
Mertens bound. To see this without using a polynomial-endpoint
theorem, write
\[
 \mu(d)1_{(d,Q)=1}
    =\sum_{\substack{j\mid d\\\lambda\mid j\Rightarrow\lambda\mid Q}}
                        \mu(d/j).
\]
For \(j\le\sqrt T\) use the ordinary
\(\sum_{v<X}\mu(v)/v=O(\exp(-c\sqrt{\log X}))\)
on \(X=T/j\ge\sqrt T\). Its zero-free-region bound is more
than sufficient because \(\log T\asymp\ell^4\).
The positive \(j\) harmonic is \(\prod_{\lambda\mid Q}
(1-1/\lambda)^{-1}=O(\ell^{O(1)})\).
For \(j>\sqrt T\) use Rankin at \(1/\ell\) and the exact
Euler product
\[
 \sum_{\substack{j>\sqrt T\\\lambda\mid j\Rightarrow\lambda\mid Q}}\frac1j
 \le T^{-1/(2\ell)}
     \prod_{\lambda\mid Q}(1-\lambda^{-1+1/\ell})^{-1}
 \ll e^{-c\ell^3}\ell^{O(1)} .
\]
In the product, for \(\lambda\le L^2\) use
\(\lambda^{1/\ell}\le e^2\) and prime reciprocals; the finitely
many smallest primes are uniformly harmless for large \(N\).
Above \(L^2\), use at most \(O(L)\) distinct labels of \(Q\)
and maximum \(\lambda^{-1+1/\ell}\ll L^{-2}\).
The trivial unmasked inner harmonic for this large-\(j\)
tail is \(O(\log T)\). Therefore (7) is \(O_A(L^{-A})\)
uniformly in all retained variables and mesh cells.
No approximation to \(\mu(m)\) or to the parity of \(m\)
is invoked in this Type I argument. Sum the remaining
reciprocal masses against (7) with arbitrary reserves to
conclude that the covered Type I part is negligible.

The actual missed estimate and these two covered estimates
prove (5), with the independently transferred moving cut.
This proves the stated deletion from the original remainder:
when \(C_0\ge2\), only \(r>\sqrt N S^{C_1}\) survive at
an \(o(M)\) error on the specified small-radical targets.
No sign or smallness is claimed for that surviving range.
