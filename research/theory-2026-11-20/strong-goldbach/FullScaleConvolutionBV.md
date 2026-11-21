# Full square-root reflected rows from generalized Bombieri–Vinogradov

This is an application of the classical generalized Bombieri–Vinogradov theorem to the **product sequence at full scale \(x\)**, not ordinary prime BV at the quotient scale \(x/S\), and not a new theorem about generalized distribution itself.

Let \(N=2x\), \(I=(x/2,x]\), \(s\sim S=x^\alpha\) prime, \(.10\le\alpha\le.14\), \(n=sq\in I\), \(m=N-n\), and \(L=\log x\). Retain the literal weights and central interval of [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md). In particular the exact \(W_s(q)=K_{P_3}(sq)\) of the semiprime is a finite sum of \(s\)-weights times smooth tests of \(n\); the more general finite-separable weight family in that note is allowed. All cutoffs below may have arbitrary fixed positive power margins.

**Actual prime quotient.** Take \(q\) a genuine prime and allow arbitrary \(|\kappa_s|\ll L^C\). The Type I main and Type I zero estimate of (2) in that note hold for every \(U\ge x^{c_0}\), \(UV\le x^{1/2-\delta}\) with fixed \(c_0,\delta>0\). In addition, for every \(T_0\le x^{1/2-\delta}\), the actual signed contribution with \(d>U,\ell>V,d\ell\le T_0\) is \(O_D(xL^{-D})\) for every \(D\). In particular the complete reflected remainder of that genuine semiprime test can be taken supported on \(d\ell>x^{1/2-\delta}\), without modulus-factor conditions, for fixed convenient \(U,V\).

**Artificial quotient after reverse Vaughan.** Now take the exact fixed reverse coefficient
\[
 B(q)=\frac{C_q^{\rm hi}(q)}{\log q},\qquad
 C_q^{\rm hi}(q)=\sum_{\substack{rk\mid q\\r>U_q,\ k>V_q,\ rk>E}}
                 \mu(r)\Lambda(k),
\tag{1}
\]
where, as in the forward/reverse notes, \(U=x^{.454},V=x^{.004},Q=x^{.466}\), and \(U_q=x^{.070},V_q=x^{.010},E=x^{.080}\) is one cutoff valid for all reflected \(d>U\). Take \(\kappa_s=1\), or any of the smooth \(s\)-coordinate weights below. Then the **entire** signed double row
\[
 \sum_{\substack{s\sim S\ {\rm prime},\ q,\ sq\in I\\(s q,N)=1}}
     \kappa_s W_s(q) B(q)
       \sum_{\substack{d\ell\mid N-sq\\d>U,\ \ell>V,\ Q<d\ell\le T_0}}
                        \mu(d)\Lambda(\ell)
                      \ll_D xL^{-D}
 \qquad(T_0\le x^{1/2-\delta})
\tag{2}
\]
has no upper bound on the original quotient divisor \(A=s r k\). The result also admits sharp independent intervals on \(d,\ell,d\ell,r,k,j=q/(rk),r k\), and any bounded number of extra plain product intervals on \(A=s r k\) (see the mesh argument below). The requirement on \(\kappa_s\) in (2) is real: the available SW factor here is the actual short prime \(s\), unlike the prime-quotient statement. Arbitrary log-bounded \(\kappa_s\) is not inferred in (2). In the application's exact \(K_{P_3}\) cell \(\kappa_s=1\).

Thus, in the unrestricted exact double row, this removes **all smaller reflected products**, including \(.466<\log_x(d\ell)<.5-\delta\) even against genuinely large original other-side products \(A\). The previously proved cancellation of all small \(A\) can be used simultaneously, as explained below.

## 1. The theorem and precise supported factors

We use [Maynard, *Primes in arithmetic progressions to large moduli I*, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733), a generalized Bombieri–Vinogradov theorem. It states that if two independent sequences are divisor-bounded, supported on dyads of polynomially long lengths \(S,T\) with \(ST\asymp x\), then their convolution has centered progression discrepancy summed up through \(x^{1/2}/L^{C_D}\) of size \(O_D(xL^{-D})\), maximized over reduced residues, provided **one** of the factors satisfies its SW condition (6.1), including independent auxiliary coprimality. See also [Polymath, Theorem 14](https://doi.org/10.1186/s40687-014-0012-7) for the generalized theorem and [Liu–Park–Song, Theorem 3.2](https://doi.org/10.1007/s40993-017-0089-3) for classical restricted prime products. Fixed log-power weights are divided by those powers before the theorem, and its arbitrary log reserve pays to restore them. The underlying distribution scale is the actual product \(s q\), not \(q\).

For the genuine prime quotient take the \(s\)-factor as an arbitrary log-bounded weight on short primes and the \(q\)-factor as the SW sequence of genuine primes at length \(T\asymp x/S\). For (2), take the \(s\)-factor as genuine primes at the polynomial length \(S\) with smooth log-power weights in \(s\), and the \(q\)-factor as the divisor-bounded but not asserted SW sequence \(B(q)\). In both cases impose \(1_{(s,N)=1}\), \(1_{(q,N)=1}\) on their respective factors. The \((\cdot,N)=1\) mask on the factor known SW excludes only \(O(L)\) prime values. An arbitrary auxiliary excluded divisor \(d_0\) removes at most \(\omega(d_0)\le\tau_2(d_0)\) primes, allowed in (6.1). The classical SW theorem for primes with any log reserve, followed by partial summation, proves (6.1) for the actual supported intervals and smooth weights; moduli beyond a large power of \(L\) follow by the trivial reduced-class count for the prime indicator and its coprime mean. In particular the short prime coordinate in (2) is not multiplied by an arbitrary rapidly varying phase.

The use of the full-scale convolution theorem is uniform for the actual \(N\bmod d\ell\). On this physical unit domain any reflected divisor \(a\mid m\) must be coprime to \(N\), hence the target residue is reduced. For a fixed \(a\), its signed divisor coefficient is \(\mu(a)\) or a sum of \(\mu(d)\Lambda(\ell)\) over \(d\ell=a\) with indicated \(d,\ell\) intervals. All of these have magnitude at most \(1+\log a\). Thus a log reserve in the source absorbs these multipliers directly; no growth of a factorization count \(x^{o(1)}\) is charged to the BV saving. If the first Type I term includes \(\log(m/a)\), separate it exactly into \(\log m-\log a\).

## 2. Product test and sharp interval separation without twisting SW

For one fixed dyad \(S\), the physically relevant \(q\) lie in a bounded union of dyads \(q\asymp x/S\). Use \(L^{-F}\)-relative meshes in \(s,q\) (in the ordinary coordinates) and use the theorem above on the resulting independent intervals. A rectangle meeting one edge of \(sq\in I\) has \(n\) in a strip of width \(O(x L^{-F})\); the true coefficient at a physical \(n\) is at most \(L^{C'}\tau_2(n)^{C'}\tau_2(N-n)^{C'}\). Global divisor moments and Cauchy give \(O_D(xL^{-D})\) for the total such edge weight by taking \(F\) large. The same holds for the centered main summands, using \(\sum_{a\le x}(1+\log a)/\phi(a)\ll L^{C'}\) and the divisor moments at \(n\). A smooth physical \(n\)-weight or \(\log m\) varies by \(O(L^{C'-F})\) on each retained rectangle; freeze it there and bound the error by the same moments. The number of rectangles is polynomial in \(L\), and the theorem supplies an arbitrarily large log reserve. This proves the required sharp product/cut and smooth-weight version without asking for any SW theorem for \(s^{it}\) with polynomial-size \(t\).

In (2) the independent \(r,k,j,rk\) intervals are built into \(B(q)\) itself. For an additional basic interval on the true \(A=s e,\ e=r k\), freeze the \(s\) value only for testing that boundary on each of the just-used \(s\)-intervals. Any wrongly included or excluded tuple then has \(|s e/A_0-1|\ll L^{-F}\) at some endpoint \(A_0\). Endpoints outside the physical range are omitted. Counting all \(e\asymp A_0/S\) (no prime or smoothness restriction) and all \(s\sim S\) in a respective interval of length \(O(S L^{-F}+1)\), before any coefficient weights, gives
\[
 \#\{n=s e j \text{ in a boundary strip of this kind}\}
   \ll \frac{x}{A_0}\left(\frac{A_0}{S}\right)(S L^{-F}+1)
   \ll x(L^{-F}+1/S).
\]
Here \(A_0\gg S\) on any nonempty strip, and \(1+x/(s e)\ll x/A_0\), since the tuple is physical. We only need a bound for the set of contaminated \(n\), so repetitions can only make this count an upper bound. The actual weighted sum over these \(n\), including all their original factorizations, is arbitrarily log small using the same physical divisor moments. Main approximation costs the same after the harmonic modulus sum. This freezing makes the remaining \(e\)-cut independent of \(s\) within every rectangle. Thus (2) also holds with such product intervals and retains genuine SW on each prime \(s\)-interval. No release of coupled \(d\ell A\) masks is made free by this statement.

## 3. Actual principal terms

In both rows, after the BV step fix the physical \(n=sq\) in the centered reduced sum. For the first Type I piece the \(a=d\) summation is
\[
 \sum_{\substack{d\le U\\(d,Nn)=1}}
    \frac{\mu(d)\log(m/d)}{\phi(d)}
          =\mathfrak S(Nn)+O_D(L^{-D}),
\tag{3}
\]
by the uniform finite Euler identities (11) of [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md). In the genuine prime quotient case \(q\asymp x/S\) and \(q\ne s\), so replacing \(\mathfrak S(Nn)\) by \(\mathfrak S(Ns)\) costs a power-small error on that reduced domain, by its exact factor at \(q\). Ordinary PNT in each true \(q\)-interval, with the original smooth \(W_s\), gives the matching main in (2) of that note. Any omitted prime divisor of \(N\) among the prime coordinates contributes only power-small error, by the divisor bounds and polynomial scales.

For the other short or sliced-high piece, fix \(\ell=p^k\) with \(\Lambda(\ell)\ne0, \((\ell,Nn)=1\). The exact factor
\[
 \frac{\phi(d)\phi(\ell)}{\phi(d\ell)}
       = 1-\frac1p 1_{p\mid d}
\tag{4}
\]
splits the remaining \(\mu(d)/\phi(d\ell)\) sum into two masked \(\mu(d)/\phi(d)\) sums with masks \(Nn\) and \(Nn p\), divided by \(\phi(\ell)\). All endpoints at which an Euler tail is used are polynomially long: they are \(U\) in the complete second Type I piece (\(UV\le x^{1/2-\delta}\)), or endpoints of a genuine \(d>U\) interval in the sliced-high pieces. Each harmonic \(d\)-sum is \(O_D(L^{-D})\) with uniform masks of polynomial size. The remaining \(\sum_\ell\Lambda(\ell)/\phi(\ell)\) is log-bounded, and all \(s,q\) weights summed absolutely have total \(O(xL^{C'})\). This makes the principal part negligible, together with its progression discrepancy, and proves (2) and the actual prime-quotient claims.

Finally, in the full double row we may remove this \(a\le x^{1/2-\delta}\) slice and the earlier entire \(A\le x^{1/2-\delta}\) slice simultaneously. Their intersection is already bounded directly by the under-hyperbola CRT theorem of [ReverseVaughanDoubleResidual.md](ReverseVaughanDoubleResidual.md), since \(a A\le x^{1-2\delta}\) on exact unit support. This statement concerns the full row; the larger first-mode cuts with conveniently factored \(A\) use their own previous proofs and, if restricted complements are desired, must account for their respective overlaps. No arbitrary coefficients on a sharp \(d\)-dependent quotient family are silently included.

The original covariance proofs improving the much smaller **quotient-only** BV range remain distinct when targeting arbitrary bounded quotient weights or particular covariance estimates. They are not the best available bound for the actual prime semiprime Type I rows: generalized BV supplies the full square-root threshold for that input and for the indicated artificial quotient when the independent \(s\)-prime factor is SW. Both super-square-root factors, including balanced genuinely signed regimes, remain; no bound for them or binary Goldbach follows here.

The prime-product distribution step is classical, as in [Goldston, Graham, Pintz and Yıldırım's prime-product theorem](https://www.renyi.hu/~pintz/0609615.pdf), which attributes it to Motohashi. The use here is also separate from [Pham’s November 2026 Restricted Chen Sieve](https://www.preprints.org/manuscript/202611.0694), which has a different coefficient family and higher-level support conditions. The added part here is applying the one-SW-factor theorem directly to the exact reverse-high quotient product with the prime (s) as that factor, followed by its signed reflected mean calculation.
