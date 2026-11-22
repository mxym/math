# One-sided signed roughening of the actual balanced determinant remainder

Keep the actual even target \(N=x\), short prime label sets, and physical equation \(ut+vs=N\) of [the composite-only determinant transfer](Proof.md). In particular \(u,v\asymp x^{.4875}\) are distinct target-unit primes, the two genuine long windows have scale \(x^{.5125}\), and no averaging over \(N\) is taken. Write \(L=\log x\), \(\ell=\log L\), and use the bracket \([f,g]\), \(R=[\lambda,\lambda]\), and \(M=\mathfrak S(N)\mathcal V\) from that transfer. Here \(\lambda(t)=(\log t){\bf1}_{t\ {\rm prime},\,(t,N)=1}\). All errors below are \(o(x\mathfrak S(N))\), irrespective of whether a sparse short-label mask makes \(\mathcal V\) smaller than its natural macroscopic scale.

Use the exact bank construction (13) of that theorem, but at the single moving choice
\[
 J=\lfloor\sqrt{\ell}\rfloor,\quad K=J+1,\quad
 d=\frac{.02}{4K^2+4K-1},\quad D=x^d,\qquad
 W_+=D^{\sqrt{\log\ell}} .
\tag{1}
\]
Only sufficiently large \(x\) are considered. The two bank families remain disjoint and all bank primes are target units, as in the original construction. Write \(F_j=F_{j,J}\), \(K_j=\lambda-F_j\), and \(Y_z(n)={\bf1}_{P^-(n)>z}\).

**Theorem.** The calibrated identity \(R=M+[K_1,K_2]+o(x\mathfrak S(N))\) holds uniformly at (1). In this very same identity,
\[
 [K_1,K_2(1-Y_{W_+})]=o(x\mathfrak S(N)).
\tag{2}
\]
The method proves two disjoint complete signed removals on the second leg: all \(P^-(s)\le D\), including repeated factors and target-common factors, and then all \(D<P^-(s)\le W_+\). In particular
\[
 R=M-
 \sum_{\substack{u,v,t,s\ {\rm in\ the\ original\ rectangle}\\ut+vs=N\\
                     s\ {\rm composite},\ P^-(s)>W_+}}
      (\log u)(\log v)\,K_1(t)\log s
       +o(x\mathfrak S(N)).
\tag{3}
\]
The remainder still has a genuinely signed \(K_1\). Equation (2) is a **one-sided** statement: it does not assert that the respective removals can both be made in (3), or that their intersection has zero signed contribution. Nothing gives positivity for the balanced \(E_2+E_2\) count, let alone binary Goldbach.

## 1. Uniformity of the moving calibration

Here \(d\sim .005/\ell\), so \(D=\exp(\Theta(L/\ell))\). For bank \(i\le 2K\) its harmonic mass satisfies \(H_i\asymp 1/i\) uniformly: the limit profile \(\log((2i+2)/(2i+1))\) follows from prime Mertens with an error \(O_A((\log D)^{-A})\) at both actual endpoints, and the exclusion of target primes has cost \(O(L/D^3)\). Thus expansion of one bank product uses coefficients
\[
 \prod_i H_i^{-1}=\exp(O(J\log J))=L^{o(1)} .
\tag{4}
\]
An opened divisor \(k b_j\) has unique decoding into its small part \(k\) (all prime factors \(\le D\), \(k\le D^J\)) and its bank part \(b_j\), since the banks are distinct intervals above \(D\). The larger single-bank capacity is
\[
 k b_j\le x^{(3K^2+4K-1)d}<x^{.016}
 \quad(K\ge4),
\tag{5}
\]
and both bank products together have upper exponent \((4K^2+6K)d=.020+o(1)\). In particular, all score coefficients have the form (5) in the original proof, with bounds \(O(L^C)\) for a single fixed \(C\), not a varying divisor power. Pointwise \(F_j(t),K_j(t)\ll L^{1+o(1)}\tau(t)\), and likewise on the second leg.

The mixed and pure transfer estimates in §1 of the original proof are uniform with any fixed log-power coefficient bounds, as one sees directly from their maximal-prefix and Bettin–Chandee proofs. The moduli, smooth physical endpoint cutoff, number of dyads, and exponent margins are unchanged here; (4) pays all coefficient and endpoint costs with fixed log reserve. The base harmonic evaluations for the finite divisor cutoff are also uniform in this regime: the Euler convolutions in §2 of the original proof, for a target parameter \(Q\le x^{1.002}\) with \(2\mid Q\), have absolute moment \(L^{O(1)}\) at tilt \(c/\ell\). Split primes of \(Q\) at \(L^2\). Convolution variables exceeding \(D^{1/4}\) have mass \(\ll \exp(-c' L/\ell^2)\) times a fixed log power, while all remaining inner Möbius cutoffs \(\ge D^{1/4}\) admit ordinary PNT with arbitrary log reserve. In particular, for all \(D^{1/2}\le Y\le D\) and \(\log t'=O(L)\),
\[
 \sum_{\substack{k\le Y\\(k,Q)=1}}\frac{\mu(k)\log(t'/k)}{\varphi(k)}
       =\mathfrak S(Q)+O_A(L^{-A}).
\tag{6}
\]
The identical product-moment argument gives the two-variable base calibration with condition \((k,l)\mid N\), as in (11) of the original proof; the errors are arbitrary-log, not constants taken after \(J\).

The bank corrections in the mixed prime-main terms still cancel up to an arbitrary log error: \(\sum_{r\ {\rm in\ a\ bank}}1/\varphi(r)=H_i(1+O(D^{-3}))\). In the pure main they cancel exactly by disjointness of the two bank families, with density \(1/r\) and shared small divisor gcd only. These points prove the moving calibrated identity. A genuine long prime dividing \(N\) may again be removed at \(x^{.4875+o(1)}\) cost as in §2 of the original proof; here (4) justifies the pointwise divisor weight in that sparse deletion.

## 2. Uniform sieve gates, floor bounds, and actual exceptional rows

Throughout the new transfers use the fundamental lemma at level \(E=x^{.002}\). Its least ratio, even at the largest roughness cutoff \(z=W_+\), is
\[
 \frac{\log E}{\log z}\gg\frac{\ell}{\sqrt{\log\ell}},
\]
so the relative sieve error in the [bounded upper/lower weights of Theorem 19.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf#page=206) is \(O_A(L^{-A})\) for every fixed \(A\). The dimension-one axioms hold uniformly: pure affine forms have at most one root per prime after admissibility exclusions; mixed prime models have local weights at most \(1/(p-1)\) for \(p\ge3\), or zero, with \(2\mid N\) omitted. The inverse product bounds for any prime interval follow from Mertens and the convergent local \(O(p^{-2})\) corrections. The sieve weights have modulus at most one on squarefree moduli \(\le E\). A signed outer score is handled by taking the difference of the upper and lower expansions as a nonnegative pointwise envelope for the sieve error and pricing it against the **absolute, opened** weights.

For clarity about the floor budget, a fixed pure tuple counts a progression for the independent integer quotients in
\[
 (u k b_1)T+(v m b_2)Z=N,
\tag{7}
\]
where \(k\le D^J\) is squarefree and small-prime-supported and \(m\le x^{.001}\) is an exact small part to be defined below. Empty bank products are allowed. The additional sieve \(e\le E\) acts on \(Z\), not on the whole \(s\). Every CRT count on a physical prefix has \(O(1)\) floor error, with no coefficient-height dependence: the simultaneous congruence is either empty or a single residue class in the primitive progression parameter. Genuine log weights of \(t,s\) are applied by partial summation, whose size and total variation are \(O(L^2\tau(m))\) in the expanded scores. The total floor error, even counting all \(u,v\) as integers, is at most
\[
 x^{.975+(.020+o(1))+.001+.002+o(1)}
          =x^{.998+o(1)} .
\tag{8}
\]
Indeed \(k b_1 b_2\) uniquely determines its three parts (the bank ranges are disjoint), and \(\log_x k\le Jd=o(1)\). Allow a factor \(x^{o(1)}\) for the log weights, (4), and \(\tau(m)\). The rough-gate application without \(m,b_2\) is a smaller case.

On the true-prime side, the necessary maximal endpoint estimate is the [divisor-weighted version of the prime product progression theorem](../prime_slot_dispersion_512/Proof.md). The actual source is \(ut\), with its genuine long prime \(t\) in the specified prime-slot range. For (7) the mixed modulus is \(q=v m b_2 e\), at most \(x^{.5065+o(1)}\); its residue is always \(N\). In the permitted prime-source cases \((m,N)=1\) and \(e\) omits target primes. The source is a unit to the entire modulus: \(u\ne v\), \(u\) exceeds all its other prime factors, and the actual prime \(t\) exceeds \(q\). The macro prime \(v\) and bank part \(b_2\) are recoverable from \(q\); the two remaining small factors \(m,e\) admit at most \(\tau(q)\) decompositions. Their weights, including \(\tau(m)\), cost only a fixed divisor power and fixed log powers by (4). The admissible physical \(ut\) interval, possibly depending on \(v\), is dealt with by maximal prefixes; partial summation keeps its actual weight \(s=(N-ut)/v\). There is no theorem import with a varying residue other than \(N\). The resolved PNT main gives the *same* physical volume form \((\log u\log v)dt/v\) as in the pure determinant, with \(1/\varphi(v)\) replaced at power-small relative cost.

There are two **actual row deletions** in the small-part transfer. Define \(m=\prod_{p\le D}p^{v_p(s)}\), including all powers, and \(r_0=\operatorname{rad}((m,N))\).
* If \(m>x^{.001}\), its physical divisor support contains a \(D\)-smooth divisor \(a\in(x^{.0005},x^{.0005}D]\), by multiplying prime occurrences up to first crossing. Along the true determinant row, \(s=s_0-u j\); since \((u,a)=1\), imposing \(a\mid s\) costs \(O(x/(uv a)+1)\) points. The absolute harmonic bound
\[
 \sum_{\substack{a>x^{.0005}\\P^+(a)\le D}}\frac1a
 \ll_C L^{O(1)}e^{-.0005 C/d}
\]
follows by Rankin with tilt \(C/\log D\), for each fixed \(C\). The Euler moment is \(\ll_C \log D\) since \(\sum_{p\le D}(p^{C/\log D}-1)/p=O_C(1)\) and higher powers are summable. Choose \(C\) large for arbitrary log savings; the floor costs at most \(x^{.975+.0005+o(1)}\).
* If \(r_0>D^{1/2}\), there is a true divisor \(a\mid (s,N)\) in \((D^{1/4},D^{5/4}]\) by the same crossing with distinct primes. Its harmonic sum over \(a\mid N\) is \(\ll L^{O(1)}\exp(-c L/\ell^2)\) by tilt \(1/\ell\), and its floors cost \(x^{.975+o(1)}\).

These prove negligible weighted row deletions, not just model tails: every central product \(n=ut\) occurs with \(O(1)\) permissible label factorizations on each side, and \(\tau(t)\tau(s)\le\tau(n)\tau(N-n)\). Apply Cauchy and \(\sum_{n\ll x}\tau(n)^4\ll xL^{15}\) to the above rare row counts and the pointwise score bound after (5).

## 3. All rows with a small factor on the second leg

We prove
\[
 [K_1,F_2\,{\bf1}_{m>1}]=o(x\mathfrak S(N)),
 \qquad m=\prod_{p\le D}p^{v_p(s)}.
\tag{9}
\]
Keep \(1<m\le x^{.001}\) and \(r_0\le D^{1/2}\) by the two actual deletions. In \(F_2(s)\) its small-divisor part and its correction are explicit functions of \(m,s\): all the small-prime-supported \(l\mid s\) in those sums divide \(m\), and their weight is \(\mu(l)\log(s/l)\). They are affine functions of \(\log s\) with variation \(O(L\tau(m))\). For a bank term expand \(B_2(s)\) over one true prime from each leg-2 bank and fix its product \(b_2\). Now \(s=m b_2Z\), with \(P^-(Z)>D\) **exactly** characterizing that \(m\) is the full small part; \(b_2\) has no prime \(\le D\). Repeated bank prime factors in \(Z\) are allowed. Each occurrence of a bank tuple is precisely a term in the actual product of divisor sums that defines \(B_2(s)\).

Consider the pure \(F_1(t)\) response to a fixed \(m,b_2\) and a fixed actual s-side weight from this expansion. For each opened \(k,b_1\), equation (7) has coefficient gcd \(g=(k,m)\), because k is squarefree, the two bank families are disjoint, and the macro labels are distinct. Thus require \(g\mid N\), divide by \(g\), and parametrize by its primitive step. At a prime \(p\le D\) the step of \(Z\) is divisible by \(p\) only if \(p\mid k,\ p\nmid m\). In that case the \(Z\)-form is a constant, nonzero if \(p\nmid N\) (no sifting root) and zero if \(p\mid N\) (the rough row is impossible). Every other prime in the sieve range has one root. The CRT density in the physical \(t\)-interval is \(g/(v k b_1 m b_2)\) before the rough factors. In particular with
\[
 V(D)=\prod_{p\le D}(1-1/p)
\]
the signed small-divisor mean of \(F_D(t)\), after extracting \(V(D)/(m b_2)\) from (6) of the original proof, is
\[
 \sum_{a\mid r_0}\mu(a)
      \sum_{\substack{k'\le D/a\\(k',mN)=1}}
       \frac{\mu(k')\log(t/(ak'))}{\varphi(k')}.
\tag{10}
\]
To verify its local factors directly: for \(p\mid k,\ p\nmid mN\), the absence of the roughness root changes the factor \(1/p\) to \(1/(p-1)\). For \(p\mid k,\ p\mid m,\ p\mid N\), the gcd supplies a factor \(p\), the \(Z\)-step after dividing by \(g\) is a unit, and the final divisor factor at \(p\) is just \(\mu(p)=-1\). If \(p\mid m,\ p\nmid N\), \(p\mid k\) is prohibited by \(g\nmid N\). If \(p\mid N,\ p\nmid m\), \(p\mid k\) makes the rough \(Z\)-row impossible. This is the extra Euler zero \(\prod_{p|r_0}(1-p^{-z})\), not a replacement of all moduli by target units.

By (6) every inner sum in (10) has main \(\mathfrak S(mN)\), since \(D/a\ge\sqrt D\). Therefore (10) is \(\mathfrak S(mN)\) for \((m,N)=1\) and zero otherwise, with error \(O_A(\tau(m)L^{-A})\). Averaged harmonic divisor moments absorb the \(\tau(m)\); we do not claim a maximum bound on \(\tau(m)\) of fixed log size. The \(C(t)(1-B_1(t))\) response has exactly zero model: finite \(k\) outside \(D\) uses the same gcd and rough exclusions, and the leg-1 bank factors are all outside the sieve, outside \(m\), and disjoint from \(b_2\). Their reciprocal factors normalize to one without changing any condition.

The summed error in (10), along with both sieve sandwich errors, is \(o(x\mathfrak S(N))\). Indeed (8) handles floors, and the absolute pure main before cancellation is \(x L^{O(1)}\): use \(\sum_b w_b/b=1\) for bank products with their positive normalized weights, \(\sum_{k\le D^J}(k,m)/k\ll \tau(m)\log(2D^J)\) by the divisor expansion of gcd, and \(\sum_{m\le x^{.001}}\tau(m)^C/m\ll_C L^{O_C(1)}\) for the fixed small powers needed here. This bound includes the absolute s-side coefficient \(O(L\tau(m))\) and the physical short-prime harmonic volume; all root products are \(\le1\) before rearrangement. The superlog sieve error in §2 therefore pays the actual unsigned bill. Uniformity in extra target \(mN\) is exactly the scope of (6).

For the true \(\lambda(t)\) mixed response, \(m\) sharing a prime with \(N\) is impossible on its unit source. Otherwise use the actual moduli \(v m b_2 e\) of §2. For the rough condition on \(Z\), the local density at \(p\le D\) not dividing \(N\) is \(1/p\) when \(p\mid m\) (multiplying the **existing** modulus by \(p\)), and \(1/(p-1)\) otherwise. The local density is zero at \(p\mid N\), which need not be sifted. Thus, relative to the standard prime-side factor
\(V_N(D)=\prod_{p\le D,p\nmid N}(1-1/(p-1))\), the \(m\) factor including \(1/\varphi(m)\) is
\[
 \frac1{\varphi(m)}
 \prod_{p|m}\frac{1-1/p}{1-1/(p-1)}
   =\frac1m\,\frac{\mathfrak S(mN)}{\mathfrak S(N)} .
\tag{11}
\]
This handles arbitrary repeated powers in \(m\). The mixed absolute model also costs only \(xL^{O(1)}\), using \(m/\varphi(m)\ll L\), fixed divisor-power harmonic moments, and the normalized bank harmonic sums; its superlog sieve gap is therefore negligible. The remaining bank part has factor \(1/\varphi(b_2)\) rather than \(1/b_2\), a superlog relative error by (4) and \(p\mid b_2\Rightarrow p>D^3\). Finally \(V_N(D)=V(D)\mathfrak S(N)(1+O(1/D+L/(D\log D)))\) by the exact Euler product and its target-divisor tail. Equations (10) and (11) match the prime and artificial main against the whole **same physical s-side score**, with summed arbitrary-log errors. This proves (9). Since \(m>1\) at a central long value forces \(s\) composite, (9) proves \([K_1,K_2{\bf1}_{P^-(s)\le D}]=o(x\mathfrak S(N))\).

## 4. Nested rough gates on the rest of the second leg

Uniformly for every \(z\in[D,W_+]\), we prove the signed null
\[
       [K_1,(\log s)Y_z(s)]=o(x\mathfrak S(N)).
\tag{12}
\]
This uses the nested indicators themselves; **no** approximation by counts of marked primes in \((D,z]\) or assumed independence from the banks is needed.

In the pure \(F_1\) expansion, fix \(u,v,k,b_1\). Now the equation is \(u k b_1 T+v s=N\) with coprime slopes. If \(p\le z\) divides \(k b_1\), \(s\) is constant modulo \(p\): it vanishes if \(p\mid N\) (no rough row) and is nonzero otherwise (no sifting root). At every other prime in the range there is one root in the actual progression parameter. As all factors of \(k\) are at most \(D\le z\), and bank primes are target units, the resulting model relative to \(V(z)=\prod_{p\le z}(1-1/p)\) is
\[
 \frac{{\bf1}_{(k,N)=1}}{\varphi(k)}\,
       \frac{1}{b_1}\prod_{\substack{p\mid b_1\\p\le z}}(1-1/p)^{-1}.
\tag{13}
\]
This formula explicitly includes the bank/sieve overlaps \(p\le z,\ p\mid b_1\). A normalized bank sum in (13) is
\[
 H_i^{-1}\left(\sum_{r\ {\rm in\ bank}\ i,\ r>z}\frac1r+
                \sum_{r\ {\rm in\ bank}\ i,\ r\le z}\frac1{r-1}\right)
       =1+O(D^{-3})
\]
uniformly for all \(z\). Thus \(C(t)(1-B_1(t))\) contributes only a superlog-small model error after summing all terms, even when the widened cutoff enters actual banks. The main of \(F_D\) itself is \(\mathfrak S(N)\) by (6). All floor and sieve errors are paid as in §2 on actual rows with their original physical endpoints and \(\log s\), and are uniformly arbitrary-log after summing moduli.

On the true prime side the moduli are \(v e\le x^{.4895+o(1)}\) with exact residue \(N\), \(e\) from the \(z\)-sieve. Prime factors of \(N\) do not need sifting, since the physical \(s\) is a target unit whenever \(ut\) is. Hence the main is \(V_N(z)\) on the same geometric volume with weight \(\log s\). The exact Euler comparison \(V_N(z)=V(z)\mathfrak S(N)(1+O(1/z+L/(z\log z)))\) and (13) prove (12). This prime-side evaluation permits \(\lambda(t)\), not an unsigned density comparison of two modeled sources.

Both gates in \(Y_D-Y_{W_+}\) are literal on actual \(s\). This difference is supported on composites (a genuine long prime exceeds \(W_+\)), and on it \(K_2(s)=-\log s\) because no factor is \(\le D\). Subtract the two nulls in (12), and combine this disjoint deletion with (9), to obtain (2). On \(Y_{W_+}\) the remaining \(K_2\) is just \(-\log s\) times the composite indicator, up to the already negligible long target-prime exception. This proves (3).

The earlier [fixed-cutoff roughness transfer](https://github.com/mxym/math/commit/db5237ea53f7ea13278e9331f3b81f12afe361c3) concerns a different directly reflected score and uses ordered fixed parameters. Here the changing bank normalization, the exact full smooth factor of the opposite determinant leg including repeated primes, and the higher nested gate have all been audited in the same one-sided signed identity. Classical sieve and divisor estimates are used as stated; no claim is made for a simultaneous two-sided deletion or for a signed lower on (3).
