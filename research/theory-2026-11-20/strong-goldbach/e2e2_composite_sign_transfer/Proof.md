# A calibrated composite-only determinant remainder with no bounded-rank opposite signs

Keep the true balanced-semiprime rectangle of [the same-quotient theorem](../e2e2_rational_projection/Proof.md): \(N=x\) is fixed and even, the two disjoint short prime label sets \(\mathcal U_0,\mathcal V_0\) are target units of sizes \(u,v\asymp x^{.4875}\), and the actual long variables \(t,s\asymp x^{.5125}\) run in prescribed windows in \(ut+vs=N\). The short prime label masks may be arbitrary subsets of the given intervals. Set \(L=\log x\), \(\lambda(t)=(\log t){\bf1}_{t\ {\rm prime},\,(t,N)=1}\), and write
\[
 [f,g]=\sum_{\substack{u\in\mathcal U_0,\ v\in\mathcal V_0\\
                 t\in I_t,\ s\in I_s,\ ut+vs=N}}
        \log u\log v\,f(t)g(s),\qquad
 R=[\lambda,\lambda].
\]
The geometric volume \(\mathcal V\) is the sum over \(u,v\) of \((\log u\log v)/v\) times the real length of the permitted \(t\)-interval, as before. Put \(M=\mathfrak S(N)\mathcal V\), where \(\mathfrak S\) is the ordered binary Goldbach singular series. The physical variables in these brackets are not replaced by independent random variables.

**Base and explicit debit.** For each fixed \(0<d\le .024\), let
\[
 D=x^d,\qquad
 F_D(t)=\sum_{\substack{k\mid t\\ k\le D}}\mu(k)\log(t/k),\qquad
 K_D(t)=\lambda(t)-F_D(t).
\tag{1}
\]
Then
\[
 R=M+[K_D,K_D]+o(x\mathfrak S(N)).
\tag{2}
\]
In the bracket a long prime dividing the target may be set to zero at negligible cost, so the remaining actual inputs are composite. On squarefree rank-two inputs \(K_D\le0\). The only squarefree rank-three inputs with \(K_D>0\) are
\[
 t=abc,\qquad a,b\le D,\quad ab>D,\quad c>D
 \quad\text{(distinct primes), when }K_D(t)=\log c .
\tag{3}
\]
For \(0<d\le .001\), all opposite-sign rows in (3) against an actual squarefree rank-two \(s=rq\) whose smaller prime \(r\le D\) have total negative magnitude \(O(d\,x\mathfrak S(N))\), with absolute implied constant (apart from fixed macroscopic scale constants). This includes the reversed orientation. It does not bound the corresponding rows with \(r>D\), or all higher-rank rows.

**Fixed-rank repair.** For every fixed integer \(J\ge3\), there are two explicit, possibly different scores \(F_{1,J}, F_{2,J}\), on the same actual long coordinates, such that
\[
 R=M+[\lambda-F_{1,J},\lambda-F_{2,J}]+o_J(x\mathfrak S(N)).
\tag{4}
\]
The remaining scores may again be set to zero on all primes. On every actual composite with at most \(J\) distinct prime factors, each score is nonpositive, **even if some factors repeat**. Consequently the part of the quadratic bracket in (4) on which *both* inputs have at most \(J\) distinct prime factors is nonnegative. An opposite-sign pair requires at least one long input with more than \(J\) distinct prime factors, as specified more precisely below. The cutoffs and normalized bank coefficients depend on fixed \(J\). No estimate for the sum of the surviving negative terms as \(J\) increases is asserted; (4) is not positivity for \(R\) or a Goldbach theorem.

## 1. Actual mixed prime and pure determinant estimates

We use a class of scores
\[
 F(t)=\sum_{\substack{k\mid t\\ k\le x^{.024}}}
       \bigl(A(k)\log t+B(k)\bigr),\qquad
 |A(k)|\ll_J1,\quad |B(k)|\ll_J L.
\tag{5}
\]
For each chosen target the coefficients are independent of the actual short-prime labels and physical long arguments. The explicit scores below satisfy these bounds. In every bracket an arbitrary permissible prime-product orientation has boundedly many representations: a positive \(n\ll x\) has at most two large distinct prime divisors of size \(\asymp x^{.4875}\), for large \(x\).

For \([F,\lambda]\) open \(k\mid t\); the actual source \(vs\) must equal \(N\) modulo \(u k\) and lie in the appropriate physical interval. If \((k,N)>1\) no such source can occur, as \(v,s\) are genuine target-unit primes. Otherwise \(u k\) is a target unit, \(v\ne u\), \(v\gg k\), and \(s\gg u k\); thus the entire actual source is a unit at this modulus. Every \(u k\ll x^{.5115}\), so use the [long-prime-slot dispersion theorem, (3) and its two-prime consequence](../prime_slot_dispersion_512/Proof.md), including its below-root portion. The congruence always has the actual common residue \(N\). The large prime divisor \(u\) identifies the label, and then \(k\) is uniquely determined. The arbitrary mask on the other short label is admissible (only the true long prime input, not the short label, needs Siegel–Walfisz). That theorem's maximal-endpoint version follows also by a log-fine grid in \(vs\): a relative strip of width \(L^{-B_0}\) costs \(O(xL^{-B_0}/q+1)\) integer values in the progression and at most two valid product factorizations per value. Summing this error over \(q\le x^{.512}\) and taking \(B_0\) large gives arbitrary log reserve, as does the same grid for the principal sum. The weight \(\log t=\log((N-vs)/u)\) is then handled by partial summation, with size and total variation \(O(L)\) in a central window. The error in (5) summed over the actual moduli and short-label log weights is \(O_{A,J}(xL^{-A})\) for every fixed \(A\).

Ordinary uniform prime PNT for prefixes replaces the remaining genuine \(s\)-slot density, after the congruence has been evaluated. Its endpoint error \(O_{A,J}(S L^{-A})\) on the polynomial long scale costs only logarithmic factors when summed with \(\sum_{k\le x^{.024}}1/\varphi(k)\ll L\) and the short-prime harmonic weights. There are \(O(1)\) genuine long primes dividing \(N\), already excluded. Change variables between \(s,t\) on the physical line and replace \(1/\varphi(u)\) by \(1/u\) at power-small cost. The resulting main uses the underlying volume measure
\[
 d\mathcal V(u,v,t)=\frac{\log u\log v}{v}\,dt,\qquad
             s=(N-ut)/v
\tag{6}
\]
on the actual real windows, with local factor
\[
 \sum_{\substack{k\le x^{.024}\\ (k,N)=1}}
       \frac{A(k)\log t+B(k)}{\varphi(k)}.
\tag{7}
\]
The other mixed orientation is symmetric, with exactly the same volume measure when expressed in \(t\).

For pure \([F_1,F_2]\), opening \(k\mid t,l\mid s\) gives
\[
  u k a+v l b=N,\qquad t=k a,\quad s=l b.
\tag{8}
\]
Since \(u,v\) are distinct primes much larger than \(k,l\), the gcd of the two coefficients is \(g=(k,l)\). A solution requires \(g\mid N\), without any assumption that \(t,s\) are target units. The zero Fourier mode is integration against (6) with factor
\[
 \sum_{\substack{k,l\le x^{.024}\\ (k,l)\mid N}}
   \frac{(k,l)}{k l}\,
     (A_1(k)\log t+B_1(k))(A_2(l)\log s+B_2(l)).
\tag{9}
\]

Here are details of the nonzero modes. Smooth only the \(t,s\) physical windows with relative widths \(L^{-A_0}\). For the sharp-to-smooth difference fix a short label and count at most \(O(TL^{-A_0}+1)\) actual long integer values at each endpoint (or the analogous \(s\)-bound). Across labels this gives \(O(xL^{-A_0}+x^{.4875})\) physical product values with multiplicity \(O(1)\) on each side. Weight all rows by \(O_J(L^4\tau(n)\tau(N-n))\), where \(n=ut\). Cauchy and \(\sum_{n\le x}\tau(n)^4\ll xL^{15}\) give \(O_{A,J}(xL^{-A})\) for sufficiently large fixed \(A_0\). The corresponding zero-mode smoothing error is negligible by the same argument with absolute harmonic local factors, or after their evaluation below. For example an absolute upper bound for (9), including the powers of \(L\), is \(O_J(L^5)\): write \(k=gk',l=gl'\) and sum \(L^2\sum_g g^{-1}\sum_{k',l'\le x^{.024}}1/(k'l')\). Each physical boundary volume summed with short-prime weights is \(O(xL^{-A_0})\).

For fixed \(g\mid N\), put \(m=u k/g,\ n=v l/g,\ \Delta=N/g\). They are coprime as required by (8). On dyads \(m\asymp M_1,n\asymp M_2\), their size is \(\ll x^{.5115}/g\). The independent coefficients on \(m,n\) are well-defined: the unique large prime gives \(u\) (or \(v\)), and hence the original divisor \(k\) (or \(l\)). Split the \(A,B\) terms separately. The continuous coordinate \(\xi=ma/\Delta\) gives
\[
 t=N\xi/u,\qquad s=N(1-\xi)/v .
\]
Thus at fixed \(\xi\) the two long-window smooth factors, including the logs of \(t,s\), enter independent \(m,n\) coefficients. Poisson in \(a\) yields the nonzero terms with prefactor \(\Delta/(mn)\), reciprocal phase \(e(h\Delta\bar m/n)\) (up to harmless sign), and integrand phase \(e(-h\Delta\xi/(mn))\). The \(\xi\)-integration lies in a fixed compact central interval. Repeated integration by parts in \(\xi\) removes \(|h|>x^\epsilon M_1M_2/\Delta\) with arbitrary power saving; the derivative constants are powers of \(L\) for each fixed order. In particular cases with this frequency cutoff below 1 retain no nonzero terms. On each remaining signed \(h\)-dyad of size \(A\), the last phase can be separated in the three dyadic normalized variables by a smooth Fourier transform on their logarithms. Its \(L^1\) cost is \(x^{O(\epsilon)}\): compact smooth cutoff in each variable, phase parameter bounded by a constant times \(x^\epsilon\), and a fixed number of integrations by parts for integrability in dimension three. The coefficients have separate \(L^2\) norms \(O_J(\sqrt{M_1}L^2)\), \(O_J(\sqrt{M_2}L^2)\), \(O(\sqrt A)\); powers of variables from this separation have modulus one.

Apply [Bettin–Chandee, Theorem 1, (1.2)](https://arxiv.org/pdf/1502.00769#page=2) to the actual numerator \(\Delta\) and these independent coefficients. Since \(A\Delta/(M_1M_2)\ll x^\epsilon\), the prefactor together with the three norm factors is \(\ll\sqrt\Delta\,x^{O(\epsilon)}\). Up to powers \(x^{O(\epsilon)}\),
\[
 AM_1M_2\ll x^{1.046}/g^3,\qquad
 A(M_1+M_2)\ll x^{.5345}/g^2,\qquad
 M_1+M_2\ll x^{.5115}/g.
\]
The two terms of that theorem therefore give respectively
\[
 x^{.993975+O(\epsilon)}g^{-1.8},\qquad
 x^{.9590625+O(\epsilon)}g^{-1.875}.
\tag{10}
\]
All dyadic and smoothing powers of \(L\) are harmless. Choose fixed \(\epsilon>0\) sufficiently small and sum the two convergent \(g\)-majorants. This proves (9), with an \(o(x)\) error, for the specified target and the original sharp physical windows. In particular the two long variables have never been identified or replaced by their separate marginals.

## 2. Euler calibration for the base

For \(F_D\), the local factor (7) is \(\mathfrak S(N)+O_A(L^{-A})\) uniformly in the physical \(t\), and (9) for \(F_D,F_D\) has exactly the same value. To see both with uniform errors, their underlying one- and two-variable Dirichlet series have the respective Euler factors
\[
 \prod_{p\nmid N}\left(1-\frac{p^{-z}}{p-1}\right),\qquad
 \prod_p\left(1-p^{-1-z}-p^{-1-w}
                           +{\bf1}_{p\mid N}p^{-1-z-w}\right).
\tag{11}
\]
The second follows by squarefree \(k,l\) and the required condition \(g\mid N\), not by assuming the two divisor variables are coprime. Factor out \(1/\zeta(1+z)\), or \(1/(\zeta(1+z)\zeta(1+w))\). The remaining convolution coefficients have absolute harmonic moments under tilt \(\sigma=c/\log L\) in each variable bounded by \(L^{O(1)}\) uniformly in \(N\). Indeed each \(p\nmid N\) contributes \(1+O(p^{-2+2\sigma})\) to that absolute product, and each \(p\mid N\) contributes \(1+O(p^{-1+2\sigma})\); geometric expansions of the denominators give the same conclusions at the finite small primes. Split target primes at \(L^2\) and use their total count \(O(L)\) above the split. Logarithmic moments are absorbed by a slightly higher tilt. At \(z=w=0\) both remaining Euler products are \(\mathfrak S(N)\): for \(p\nmid N\) the local factor is \(p(p-2)/(p-1)^2\) and for \(p\mid N\) it is \(p/(p-1)\).

To make this rigorous on the actual finite cutoff, convolution variables exceeding \(\sqrt D\) have an exponentially small tilted harmonic tail even after including trivial log powers for the inner sums. Otherwise the inner variables have cutoff at least \(\sqrt D=x^{d/2}\); the ordinary signed Möbius prime number theorem gives
\[
 \sum_{m\le Y}\mu(m)/m=O_A(L^{-A}),\qquad
 \sum_{m\le Y}\mu(m)\log m/m=-1+O_A(L^{-A})
\]
at every such polynomial \(Y\). Thus the inner \(\log(t/k)\) sum is \(1+O_A(L^{-A})\), and in the pure main each of the two inner sums supplies \(1\). This proves the displayed uniform calibration. Equations (7), (9) now give \([F_D,\lambda]=[\lambda,F_D]=[F_D,F_D]=M+o(x\mathfrak S(N))\), and hence (2).

If a true long prime \(t\mid N\) occurs in an input of \([K_D,K_D]\) or (4), its opposite \(s\) is divisible by \(t\), because \(v\) is a smaller prime. Write \(s=j t\) where \(j=O(1)\), and \(u+jv=N/t\). For each of \(O(1)\) long primes \(t\mid N\) and each \(j\) there are \(O(x^{.4875})\) label pairs, since \(v\) determines \(u\). Divisor-bounded weights cost \(x^{o(1)}\), so these rare exceptions to the composite-only formulation can be discarded. The argument in the other orientation is identical.

## 3. Pricing a genuine base opposite-sign sector

On a composite rank-two input with distinct primes \(r<q\), the larger factor exceeds \(D\) for large \(x\). Thus \(K_D=-\log r\) when \(r\le D\), and \(-\log s\) otherwise. On a squarefree rank-three input at least one factor \(c>D\). If no factor is small then \(K_D=-\log t\); if just one is small, its result is the same as rank two with that smaller factor; if \(a,b\le D\), inclusion or exclusion of the divisor \(ab\) gives respectively \(K_D=0\) or \(+\log c\). This proves (3), including all exact cutoff equalities.

For the indicated opposite-sign rows fix actual \(u,v,a,b,r\) with \(a,b,r\le D\) and \(ab>D\). The true unmarked complementary variables \(c,q\) are primes in
\[
       (u ab)c+(v r)q=N.
\]
Let \(g=(ab,r)\), necessarily \(1\), \(a\), or \(b\); if \(g>1\) it must divide \(N\). The interval of common progression indices lies in an interval of length \(O(Y_0)\), \(Y_0=xg/(uvabr)\gg x^{.022}\) at \(d\le .001\). Both actual primes exceed \(x^{.50}\) for large \(x\) (the base scale after removing \(ab\) or \(r\) is at least \(x^{.5105}\) up to fixed constants). Apply a dimension-two upper sieve in the progression index to the two actual affine prime forms. If one form vanishes on every index modulo a prime of its slope, the entire physical prime contribution is zero, since these slope primes are strictly smaller than the actual \(c,q\) at these exponents. Otherwise the two coprime reduced slopes have precisely the standard two forbidden residues outside their factors and \(N/g\), and coincide at a prime dividing \(N/g\) when both slopes are units. Removing the at most five distinct primes in the two slopes costs a bounded local factor. If at a prime, notably \(2\), there is no admissible residue, the physical count is zero; otherwise the local product for the sieve is \(\ll \mathfrak S(N)/(\log z)^2\) at \(z=Y_0^{c_1}\) with fixed small \(c_1>0\), since target factors of \(N/g\) are target factors of \(N\). Standard upper beta or Selberg sieve at a fixed power level below \(Y_0\) gives \(\ll Y_0\mathfrak S(N)/L^2\). Explicitly the count for each squarefree divisor of the sifting set is the number of forbidden CRT classes times length divided by that divisor, with error \(O(2^{\omega(\cdot)})\); a fixed power support well below \(Y_0\) absorbs the floors uniformly, regardless of the coefficients' height. Enlargement to a whole interval of length \(O(Y_0)\) makes this bound independent of shorter actual endpoints.

The weight is \((\log u)(\log v)(\log c)(\log r)\). Summing using the bounded harmonic log sums of the short prime labels reduces the bound to a constant times
\[
 x\mathfrak S(N)
  \sum_{\substack{a,b,r\le D,\ ab>D\\a,b,r\ {\rm prime},\ a\ne b\\
                           (ab,r)\mid N}}
       \frac{(ab,r)}{abr}\frac{\log r}{L}
 \ll d\,x\mathfrak S(N).
\tag{12}
\]
Indeed \(\sum_{a,b\le D,ab>D}1/(ab)=O(1)\) uniformly: when \(a\le\sqrt D\), the inner prime harmonic in \((D/a,D]\) is \(O((\log a+1)/\log D)\) by Chebyshev and partial summation, and \(\sum_{a\le\sqrt D}\log a/a=O(\log D)\); both labels above \(\sqrt D\) have bounded harmonic sums. For \((ab,r)=1\), use \(\sum_{r\le D}(\log r)/r=O(\log D)\). For \(r=a\) or \(b\), cancellation of the repeated gcd in (12) leaves at most \(d/(ab)\); retaining only those collisions at primes dividing \(N\) does not increase the bound. This is a bound for actual adverse rows of the same unpatched score, not a credit that can be added to the separate repair below.

## 4. Neutral banks that repair all fixed bounded ranks on both legs

Let \(K=J+1\) and fix
\[
 d=\frac{.02}{J+K(4K+3)},\qquad D=x^d .
\]
Choose \(2K\) disjoint prime banks indexed by \(1\le i\le2K\), with the \(i\)-th lying in \((x^{(2i+1)d},x^{(2i+2)d}]\), and omit primes dividing \(N\). Let \(H_i\) be the reciprocal prime sum in bank \(i\). For fixed \(J\), every \(H_i\) tends uniformly in \(N\) to \(\log((2i+2)/(2i+1))>0\) by Mertens and the negligible omission of the target's polynomial prime divisors. Use banks \(1,\dots,K\) on leg 1 and \(K+1,\dots,2K\) on leg 2, writing \(\mathcal I_1,\mathcal I_2\) for their index sets. Set
\[
 \begin{split}
 B_j(t)&=\prod_{i\in\mathcal I_j}H_i^{-1}
                    \sum_{\substack{r\mid t\\r\ {\rm prime\ in\ bank}\ i}}1,\\
 C(t)&=\sum_{\substack{k\mid t,\,D<k\le D^J\\P^+(k)\le D}}
                             \mu(k)\log(t/k),\\
 F_{j,J}(t)&=F_D(t)+C(t)(1-B_j(t)) .
 \end{split}
\tag{13}
\]
At a prime \(t\), \(C=0\) and \(F_{j,J}=\log t\). The scores belong to (5): opening \(B_j\) gives \(b=r_1\cdots r_K\) with one actual prime from each bank, all coprime to \(k\) and to \(N\); an opened divisor \(k b\) is \(\le x^{(J+K(4K+2))d}<x^{.02}\). The small part \(k\) and the ordered bank primes can be recovered uniquely from the opened divisor. Their weights are bounded by a \(J\)-dependent constant, and \(\log(t/k)=\log t-\log k\) retains the original small divisor, not the enlarged modulus. No multiplicity from repeated bank primes or across different banks is possible.

In (7), the additional bank product changes the main of a \(C(t)\) term by the factor
\[
 \prod_{i\in\mathcal I_j}\frac{1}{H_i}\sum_{r\ {\rm in\ bank}\ i}\frac1{r-1}
            =1+O_J(x^{-c(J)}).
\tag{14}
\]
This is multiplicative in \(b\) since \(k\) is coprime to all bank primes, and \(k\) must still be a target unit. The absolute small-divisor main including \(\log(t/k)\) is \(O_J(L^2)\), so the additional term in (13) costs \(o(x)\) in each mixed bracket. In (9), every bank prime is coprime to all small divisors and to every bank prime used on the opposite leg. Thus the common gcd is exactly the gcd of the two small divisors and the actual condition that it divides \(N\) is unchanged. Each complete bank product multiplies its corresponding main by
\[
 \prod_{i\in\mathcal I_j} H_i^{-1}\sum_{r\ {\rm in\ bank}\ i}1/r=1
\]
exactly. Hence all contributions containing \(C(1-B_j)\), including the term containing both corrections, have zero pure main. The use of disjoint bank families across the legs is essential here. Equations (7) and (9) give \([F_{1,J},\lambda]=[\lambda,F_{2,J}]=[F_{1,J},F_{2,J}]=M+o(x\mathfrak S(N))\); this proves (4).

Finally, whenever \(t\) has at most \(J\) distinct primes \(\le D\), their squarefree product is at most \(D^J\), so \(F_D+C\) is the **complete** small-divisor sum. It is exactly \(\log t\) if there is no small prime, \(\log p\) if \(p\) is the only distinct small prime, and \(0\) if there are at least two. This follows by expanding the full product \(\prod_{p\mid t,p\le D}(1-1)\) and its one logarithmic derivative: repeated factors of \(t\) add no new Möbius divisor. If, in addition, some bank on leg \(j\) has no prime dividing \(t\), then \(B_j(t)=0\); the score \(F_{j,J}\) is this nonnegative complete sum. Both hypotheses hold whenever \(\omega(t)\le J\), as the banks require \(J+1\) distinct primes. A positive composite value of \(\lambda-F_{j,J}\) can therefore only come from \(>J\) distinct small factors or from occupancy of every bank on its leg. The latter are actual composite factors, not abstract independent weights. Their normalization in (13) is not bounded uniformly in \(J\), and the moving \(d=d_J\) excludes any argument simply interchanging a fixed-\(J\) sign result with a high-rank limit.

This is a composite-only sign transfer for the actual near-balanced \(E_2+E_2\) determinant, not the binary prime count. The earlier [moving square-root cusp identity](https://github.com/mxym/math/commit/0e7e4c952d8f35448108f3af3b4fc60024877e00) works in the directly reflected prime geometry and retains a different composite score at a different cutoff. The [paired low-rank modification](https://github.com/mxym/math/commit/bf13a6e1d1a9b35bdea274481e7a9c4e2d26a1b8) uses a flattened physical midpoint rather than the cross-leg disjoint neutral banks here. The classical determinant and sieve inputs are not new; the result concerns the sign of a specified actual bounded-rank part. No claim is made that both-prime or both-semiprime positivity follows from the modeled marginals or from the repaired bounded ranks.
