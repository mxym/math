# Smooth reverse Vaughan cutoff: finite core mass and an actual small-factor shield

Use the actual fixed-even-target setup of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md) and [WholePositiveSmallCore.md](WholePositiveSmallCore.md): \(N=2x\), \(L=\log x\), \(I=(x/2,x]\), \(n=sq\in I\), \(m=N-sq\), \((sq,N)=1\), and \(x^{.10}<s<x^{.14}\) a true prime. In the actual primed row \(q\) is also a true prime and its weight is \(W_s(q)=K_{P_3}(sq)\), with \(\kappa_s=1\). Let \(C\) and \(C^\dagger=C+P-J\) be the fixed reflected coefficients in the first note, and \(M_N=\mathfrak S(N)x/(2L)\). No assumption is made on existence of prime pairs for \(N\).

Fix \(y=.070\), \(Y=x^y\), and \(0<a<b<1\). Take a nonnegative \(C^\infty\) probability density \(\psi\) supported in \((a,b)\), and write \(\Phi(t)=\int_{-\infty}^t\psi(u)\,du\). Define the genuinely opened averaged quotient coefficient
\[
   B_f(q)=\frac1{\log q}\sum_{r k\mid q}
          \mu(r)\Lambda(k)\,\Phi(\log r/\log Y)\,1_{k>Y},
       \qquad f(t)=1-\Phi(t)\quad(t\ge0).
\tag{1}
\]
Thus \(f=1\) on \([0,a]\), is zero on \([b,\infty)\), and can be extended to a compact smooth function \(f:\mathbb R\to\mathbb R\) by multiplying \(1-\Phi\) by a smooth factor equal to 1 near and above 0 and zero on \(( -\infty,-1]\). This extension has no effect on (1).

**Theorem.** For each fixed \(D>0\),
\[
           \mathcal T_{\rm p}(C)=\sum_{s,q}W_s(q) C^\dagger(N-sq) B_f(q)+O_D(xL^{-D}),
\tag{2}
\]
with the actual constraints stated above and **integer** \(q\) on the right. For every fixed \(0<\eta<1\), put \(H_0=\exp(L^\eta)\). Then the actual absolute mass of the small-factor sector on the right of (2) satisfies
\[
 \sum_{\substack{s,q\\P^-(q)\le H_0,\ P^-(N-sq)\ge x^{.120}}}
   |W_s(q) C^\dagger(N-sq) B_f(q)|
       \ll_{f,y,\eta} M_N L^{\eta-1}+O_D(xL^{-D}).
\tag{3}
\]
There is no upper cutoff on the size or rank of the small-prime core of \(q\) in (3). In addition, the whole macro-rough reflected sector with a nontrivial core has absolute mass \(O_{f,y}(M_N)\); restricting it to core \(z>Y^A\) gives \(O_{f,y,t}(M_N e^{-t A})+O_D(xL^{-D})\) for any fixed \(t>0\). This is an actual fixed-target estimate for the smooth opened row, not a cancellation claim about the previous sharp-cutoff row or about actual prime pairs.

## 1. Exact averaging and exact small-core formula

At each \(u\) in the support of \(\psi\), use the reverse Vaughan cutoffs \(U_q=Y^u, V_q=Y, E=Y^{u+1}\). The high coefficient is exactly \(\sum_{r k\mid q,r>Y^u,k>Y}\mu(r)\Lambda(k)\), since \(rk>E\) is then automatic. The short terms have physical moduli \(se\) with \(e\le E<Y^2\). The proof in §1 of [WholePositiveSmallCore.md](WholePositiveSmallCore.md) is uniform here: its CRT floor uses short forward \(a\) with \(a se\le x^{.78}\), and its ordinary maximal prime BV uses \(se\le x^{.28}\). The coprime harmonic endpoints \(U_q/f_0\) for harmonic shifts \(f_0\le L^K\) are \(\gg x^{a y}/L^K\). All errors thus hold uniformly with arbitrary logarithmic reserve. For the two reflected corrections \(P,J\) the proof cited there works with these possibly unequal cuts: in the singular-ratio test at \(g\le L^K\), the first short term uses exactly the two finite \(\mu/d\) moments at \(U_q/f_0\), and the second short term fixes each \(k\le Y\) before that same harmonic \(r\)-sum; the third short-product term is empty. The \(g\)-tail uses the universal \(|C_q^{\rm hi}|/\log q\le \tau(q)\). The prime-power approximation and all genuine unit-on-\(N\) conditions are unchanged. Integrating gives (2), since the equality event \(r=Y^u\) is null for the smooth measure. This uses the **whole** row before later restricting it; it gives no sectorwise transfer from the sharp to the smooth weight.

Write \(q=z w\) uniquely with \(P^+(z)\le Y<P^-(w)\). Remove those \(q\) having \(p^j\mid q\) with \(p\le Y<p^j\) and \(j\ge2\). For each \(s\), the count in \(q\asymp X=x/s\) is \(O(XY^{-1/2})\): sum geometric tails over integer bases \(b>\sqrt Y\) from \(b^{-2}\), and over \(b\le\sqrt Y\) from the first \(b^{-j}<1/Y\). Counting positive multiples needs no separate floor term. On both rows every weight has a fixed divisor-power envelope times a power of \(L\), so over all \(s\) the exception contributes \(O(x^{1-y/2+o(1)})\).

On nonexceptional \(q\), every \(k>Y\) with \(\Lambda(k)\ne0\) lies in \(w\). If \(z=1\), then any \(r>1\) has \(r>Y\), so
\[
                     B_f(q)=\frac{\Lambda(q)}{\log q}-1
                     \qquad(z=1).
\tag{4}
\]
This holds also for a fully rough prime power. If \(z>1\), decompose \(r=d e\) with \(d\mid z\), \(e\mid w/k\). For \(e>1\), \(e>Y\) implies \(\Phi(\log r/\log Y)=1\), and the whole \(d\)-sum vanishes by \(\sum_{d\mid z}\mu(d)=0\). For \(e=1\) it equals \(R_f(z):=-\sum_{d\mid z}\mu(d) f(\log d/\log Y)\). Thus
\[
              B_f(q)=R_f(z)\frac{\log w}{\log q}\qquad(z>1).
\tag{5}
\]
In particular \(w=1\) gives literal zero and needs no sieve. Unlike the equal sharp cutoff, the smooth cutoff does not in general annihilate *all* one-prime cores (it does if their prime is at most \(Y^a\)). In particular (4) is an untouched genuine-prime term on the fully rough branch.

## 2. Fourier--Euler absolute core estimate

For even \(M\) let \(h_M(z)=\mathfrak S(Mz)/(\mathfrak S(M)z)\) for \((z,M)=1\). All variables \(z\) in this section are \(Y\)-smooth and coprime to \(M\). At any permitted prime \(p\), the aggregate \(h_M(p^j)\), \(j\ge1\), is \(A_p=1/(p-2)\). Fourier inversion using \(e(v)=e^{2\pi i v}\) gives
\[
       -R_f(z)=\int_{\mathbb R}\widehat f(t)
             \prod_{p\mid z}(1-e(t\log p/\log Y))\,dt\qquad(z>1).
\tag{6}
\]
Consequently the absolute harmonic sum is bounded by
\[
 \int_{\mathbb R}|\widehat f(t)|\prod_{p\le Y, p\nmid M}
       (1+A_p|1-e(t\log p/\log Y)|)\,dt.
\tag{7}
\]
Inserting \(z=1\) on the right only enlarges the upper bound. For each fixed \(Y\), Tonelli and absolute Euler factorization apply after taking the modulus, since finitely many primes are allowed and their geometric-power series converge.

The Euler product in (7) is \(O((1+|t|)^2)\) uniformly in \(Y,M\). Indeed by \(A_p=1/p+O(1/p^2)\) for \(p>2\), use \(|1-e(v)|\le\min(2,2\pi|v|)\) and split at \(Y^{1/\max(1,|t|)}\) if that is at least 3. The low-prime log sum is \(O(1)\) by \(\sum_{p\le v}\log p/p\ll\log v\); the higher-prime contribution is at most \(2\log\max(1,|t|)+O(1)\) by Mertens. If the split lies below 3, the entire log product is \(\le2\log\log Y+O(1)\), and \(\log Y<\max(1,|t|)\log3\); this proves the same assertion, including \(|t|\ge\log Y\). Excluding primes dividing \(M\) can only improve these positive products.

If \(z\) is required to have a prime factor \(p\le H_0\), the same product gains by a union bound the additional factor
\[
       \sum_{p\le H_0, p\nmid M} A_p |1-e(t\log p/\log Y)|
              \ll |t|\frac{\log H_0}{\log Y}.
\tag{8}
\]
The Fourier transform is rapidly decaying. This proves
\[
 \sum_{z>1}h_M(z)|R_f(z)|\ll_f1,\qquad
 \sum_{\substack{z>1\\ P^-(z)\le H_0}}h_M(z)|R_f(z)|
                  \ll_f\frac{\log H_0}{\log Y}.
\tag{9}
\]
For the tail insert \((z/Y^A)^{t/\log Y}\) with fixed \(t>0\). In the Euler product the new \(A_p(t)\) equals \(\mathfrak S(Mp)/\mathfrak S(M)\) times \(p^{-1+t/\log Y}/(1-p^{-1+t/\log Y})\). Uniformly in permitted primes \(A_p(t)-A_p\ll_t (\log p)/(p\log Y)\) for \(\log Y\ge2t\), by differentiation in the exponent and geometric tails. Thus its alteration costs \(\exp(O_t(1))\) in (7), and gives
\[
              \sum_{z>Y^A}h_M(z)|R_f(z)|\ll_{f,t} e^{-t A}.
\tag{10}
\]
The Fourier variable and Rankin parameter are independent.

## 3. Transfer to the actual reflected products without BV on large cores

For a fixed true \(s,z\) on the unit support, any nonzero row point has \(w>1\) by (5), so \(w>Y\). Its physical interval \(x/2<szw\le x\) has available length \(X_z\asymp x/(sz)\gg Y\) whenever nonempty. The required \(w\) and \(m=N-s z w\) are rough respectively at \(Y\) and \(x^{.120}\). Sieve the two *integer* linear forms \(w,N-szw\) in that interval at level \(R=x^{y/100}\), below both true roughness thresholds. The Selberg-square remainder \(O(R^2(\log R)^C)\) is power-smaller than \(X_z/L^2\) because \(X_z\gg x^y\). At every prime \(p\nmid Nsz\) there are exactly two distinct roots; at primes dividing \(N\) the two roots coincide (\((N,sz)=1\)), while at primes dividing \(sz\) the second form is a nonzero constant. In particular the 2-factor has only one root. The uniform Selberg comparison in §5 of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md) yields
\[
     \#\{w\text{ in this actual sector at }s,z\}
           \ll_y \mathfrak S(Ns z)\frac{x}{s z L^2}.
\tag{11}
\]
One may discard the extra unit condition for individual \(w\) in this upper sieve; the indispensable \((N,sz)=1\) is kept. This bound does not need primes in progressions at modulus \(sz\), which could be very large.

On \(P^-(m)\ge x^{.120}\), the total prime factor count of the physical \(m\le3x/2\), with multiplicity, is at most 8 eventually. Thus the literal divisor identity in §4 of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md) or simply (1)--(2) of that note gives \(|C^\dagger(m)|\ll L\). The actual \(W_s\) and \(\log w/\log q\) are bounded absolutely by constants. Combining (11) with (5) and any nonnegative upper bound on \(\sum_z |R_f(z)|h_{Ns}(z)\) bounds the corresponding physical sum by
\[
      \ll_y \frac{x}{L}\sum_s\frac{\mathfrak S(Ns)}{s}
                              \sum_z|R_f(z)|h_{Ns}(z).
\]
The true prime \(s\)-band has \(\sum_s1/s\ll1\), and adjoining \(s\) changes the singular series by a bounded factor. As \(H_0<Y\) eventually, the small-factor condition in (3) forces \(z>1\) and \(P^-(z)\le H_0\). Now (9)--(10) give (3), the full core bound, and the large-core bound. The already paid tiny-base powers have arbitrary log reserve. These results leave (4), the significant \(Y\)-rough portion, the nontrivial cores with no tiny prime, and reflected \(m\) outside the macro-rough condition. They give neither the required global one-sided budget nor a binary Goldbach proof.

## Scope relative to parallel work

[Pham's October v1](https://www.preprints.org/manuscript/202610.3061) studies reflected mixed rough estimates and signed boundary terms; the [November 1+1.75 manuscript](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) uses different small-factor and smooth progression cores. This note does not use their claimed conclusions. Its bound is for the actual integer-q opened sector after a whole-row exact cutoff average, with a Fourier–Euler bound on the absolute value of its resulting core. The earlier sharp signs, and the unresolved true-prime and reflected non-macro-rough contributions, are not bounded by this change of cutoff.
