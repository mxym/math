# Equal reverse cuts: all positive small cores of moderate size

Keep the actual \(C,C^\dagger=C+P-J\), \(W_s(q)\), \(I\), and scale \(M_N=\mathfrak S(N)x/(2L)\) from [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md), with \(\kappa_s=1\), \(L=\log x\), and \(x^{.10}<s<x^{.14}\) an actual prime. Use the following **different** reverse cuts:
\[
                      Y=x^{.070},\qquad U_q=V_q=Y,\qquad E=Y^2=x^{.140}.
\tag{1}
\]
The whole integer-\(q\) row with these cuts is still equivalent to \(\mathcal T_{\rm p}(C)\) up to arbitrary log accuracy; its weights are not the old reverse coefficients term by term. For an actual integer \(q\) in the opened row, decompose uniquely \(q=z w\) with
\[
 z=\prod_{p\le Y}p^{v_p(q)},\qquad P^-(w)>Y,\qquad (z,w)=1.
\]
Outside a total power-small contribution from \(q\)'s containing some prime power \(p^a>Y\) with \(p\le Y,a\ge2\), one has the **exact** coefficient
\[
 C_{q,Y}^{\rm hi}(q)=
 \begin{cases}
    \Lambda(q)-\log q,&z=1,\\
    R_Y(z)\log w,&z>1,
 \end{cases}
 \qquad R_Y(z)=\displaystyle\sum_{\substack{d\mid z\\d>Y}}\mu(d).
\tag{2}
\]
In particular the entire sector with exactly one distinct small prime is zero after paying the high-power exceptions. The rough-\(q\) and two-mark compensation statements of the two preceding notes remain valid also with (1), by exactly the same true coefficients on their stated sectors; their original statements at their own cuts are not being reinterpreted.

A genuinely broader signed bound holds as follows. Take **any** collection \(\mathcal Z\) of possible \(z\) cores, each satisfying \(1<z\le x^{.14}\), \(P^+(z)\le Y\), \(R_Y(z)>0\), and with no prime power \(p^{v_p(z)}>Y\). There is no finite-rank requirement on the small cores. Retain all actual \(m\) with \(P^-(m)\ge x^{.120}\), including the positive and negative ranks. The signed contribution of this whole sector of the new row is bounded by
\[
 \mathcal H(\mathcal Z) \ \le\
  -.90 M_N
    \sum_{\substack{s,z\in\mathcal Z\\(s z,N)=1}}
       W_s^\circ\,\frac{R_Y(z)}{(s-1)z}
        \frac{\mathfrak S(Ns z)}{\mathfrak S(N)}
     +O_D(xL^{-D}) ,
 \quad W_s^\circ=(1-\log_x s)(1-2\log_x s)^2 .
\tag{3}
\]
Here and below \(\sum_{s,z\in\mathcal Z}\) means \(s\) in the specified prime band and \(z\in\mathcal Z\). The estimate is uniform for the choice of \(\mathcal Z\) and holds for every fixed \(D>0\). The additive error is included even for very sparse collections. The signed weight in (3) is \(\kappa_s W_s(q) C^\dagger(m) C_{q,Y}^{\rm hi}(q)/\log q\), on the actual physical \((sq,N)=1\) support. The endpoint \(z=1\), the \(R_Y(z)\le0\) cores and \(m\) with smaller factors are not covered by the asserted negative bound.

## 1. The new cuts are valid on the whole row

Replace the genuine \(q\)-prime indicator by \(\Lambda(q)/\log q\) as in [ReverseVaughanDoubleResidual.md](ReverseVaughanDoubleResidual.md), with power-small extra proper powers. Apply literal Vaughan at (1). Its two short pieces use \(e\le Y\) or \(e\le Y^2\), respectively. If one includes a short product cut in its third term, it is empty: \(r>Y,\ k>Y\) imply \(rk>Y^2=E\) strictly. Thus equality at \(E\) is not misclassified. The term \(\Lambda_{\le Y}(q)\) vanishes at the central actual \(q\). We claim that the two short pieces vanish against the whole reflected \(C\).

For fixed \(s,e\) the actual modulus in \(m\) is \(A=s e\le x^{.28}\), with true class \(N\bmod A\), exact \((m,N)=1\) and original one-variable log and product test. Reassemble the complete \(C\) as its true \(\Lambda(m)\) minus its three short-divisor pieces as in [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md). With \(a\le Q<\sqrt x\), all short pieces have \(aA\le x^{.78}\), so exact unit-on-\(N\) CRT gives density \(\phi(N)/(N a A)\) with total floor \(O(x^{.78+o(1)})\) over these moduli, including weights and multiplicities. The first \(\mu_{\le U}*\log\) has the literal \(\log(m/a)=\log m-\log a\); using coprime \(\mu/a\) finite harmonic moments with mask \(AN\), its center is exactly \(1/\phi(A)\) after multiplication by \(\phi(N)/N\). The other short harmonic means are negligible by the same finite coprime identities, since \(U\) is polynomially long and \(UV<Q\). Thus ordinary maximal prime BV at moduli \(\le x^{.28}\) for the reflected true \(\Lambda(m)\) makes the entire \(C\) sum negligible against both short \(q\) pieces. All coefficients are log-bounded per original \(e\); their log variation in the physical \(m\)-test allows partial summation, and \(A=s e\) has at most divisor multiplicity (in fact \(O(1)\) admissible \(s\)). Excluded \(m\)-prime powers of primes dividing \(N\) are harmless by the same physical divisor bound. This uses the **whole** \(C\) reassembly, not the earlier fixed-\(d\) Möbius BV which had a smaller range in \(e\).

The artificial \(P,J\) centers of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md) also apply at (1). For \(J\) the \(q\)-weight was arbitrary divisor-bounded. For \(P\), its singular-ratio expansion through \(g\le L^K\), exact \((d,g)=\sum_{f\mid(d,g)}\phi(f)\) center, and true prime-power exceptions are unchanged. The short \(q\)-divisor floors now run up to \(Y^2=x^{.14}\), still well below the central \(q\)-length \(X=x/S\ge x^{.86}\), and the endpoints \(Y/f\) in the coprime moments remain polynomially long. The large \(g\) tail uses \(|C_{q,Y}^{\rm hi}(q)|/\log q\le\tau(q)\) and is unchanged. Thus globally
\[
             \mathcal T_{\rm p}(C)
                  =\mathcal T_{{\rm v},Y}(C^\dagger)+O_D(xL^{-D}).
\tag{4}
\]
No restriction on \(q\)'s small core is made in proving the whole cancellation underlying (4).

## 2. Exact small-core factorization and the exceptional powers

For fixed \(s\sim S\), the count of \(q\asymp X=x/S\) divisible by some \(p^a>Y\) with \(p\le Y,a\ge2\) is \(O(XY^{-1/2})\), even allowing integer bases. For bases \(b>\sqrt Y\), sum the convergent geometric tail starting with \(b^{-2}\). For \(b\le\sqrt Y\) start with the first \(b^a>Y\), and its geometric tail costs \(O(1/Y)\) per base. Multiplied by \(X\) this gives the stated bound without a floor term (count positive multiples by \(O(X/b^a)\)). Over all \(s\sim S\), including the original divisor-power envelope of the weights, the cost is \(x^{.965+o(1)}\).

Outside this set, every \(\Lambda(k)\ne0\) in the high \(k>Y\) piece must have \(k\mid w\). For \(z>1\), fix such \(k\). An \(r\mid q/k\) with any nontrivial \(w/k\)-part is \(>Y\) regardless of the \(z\)-part \(a\mid z\), so all its terms cancel by \(\sum_{a\mid z}\mu(a)=0\). For the \(w/k\)-part 1, the remaining \(r=a\) contributes exactly \(R_Y(z)\), independently of \(k\). Summing \(\Lambda(k)\) over \(k\mid w\) gives (2), including \(w=1\) where \(\log w=0\). When \(z=1\), all nontrivial \(r,k\) are above \(Y\), giving \(\Lambda(q)-\log q\) exactly. If \(z\) is a pure prime power \(p^a\), its only nonzero Möbius divisors \(1,p\) are both \(\le Y\), so \(R_Y(z)=0\). The earlier two-mark sector is unchanged because \(z=p t\) with \(p,t\le Y<pt\) has \(R_Y(z)=+1\), while the rank-four fully rough \(q\) sector keeps \(z=1\) with its old coefficient.

No general sign is inferred for three or more distinct small primes. E.g. for the three exponents near .025 each, the total is above .070 but every pair below, giving \(R_Y(z)=-1\); when all three are near .040, all pairs are above .070 and \(R_Y(z)=2\). Both are nonempty exponent chambers; the rough remainder \(w\) still varies.

## 3. Exact local sieve at arbitrary positive cores

Hold \(s,z\) with \((s z,N)=1\) fixed. In the physical \(m\)-sequence the congruence for \(e\mid w=(N-m)/(s z)\) is
\[
                       m\equiv N\bmod s z e,
\]
where \(e\) is squarefree with prime factors \(\le Y\) and coprime to \(N\). Unlike the two-mark note we now **include** prime divisors of \(z\) in the roughness sieve; they need not be polynomially large and no repeated-small-prime removal can be inferred for them. The local density is exactly
\[
            g_{s,z}(p)=
            \begin{cases}
              0,&p\mid N,\\
              1/p,&p\mid z,\\
              1/(p-1),&p\nmid N s z
            \end{cases}
            \qquad (p\le Y).
\tag{5}
\]
There is no separate \(s\)-case since \(s>Y\). To check (5), in the reduced main \(1/\phi(s z e)\) one extra factor \(p\mid z\) multiplies the denominator by \(p\), not \(p-1\); when \(p\nmid z\) it multiplies by \(p-1\). The actual \(m\)-prime-product masks below have every factor \(\ge x^{.120}>Y\), so no coprimality to \(z,e\) is lost and the only remaining main mask is \((m,Ns)=1\), exactly as in the two-mark proof. For \(z\) coprime to \(Ns\), its factors are \(<s\), so \(\phi(s z)=(s-1)\phi(z)\). The resulting sieve product is
\[
      V_{s,z}(Y)=(1+o(1))\frac{e^{-\gamma}}{.070 L}\,
                       \mathfrak S(Ns z)\frac{\phi(z)}{z}.
\tag{6}
\]
At \(p\nmid Ns\) dividing \(z\), the change from \(1-1/(p-1)\) to \(1-1/p\) gives the ratio \(((p-1)/(p-2))(1-1/p)\); this proves (6) from the previous uniform product, including the exact 2-factor. The dimension-one condition is uniform because these changes only decrease the local densities. The notation \(p\le Y\) may be implemented by sieving to \(\lfloor Y\rfloor+1/2\), so the fundamental parameter is unchanged up to \(o(1)\).

For all ranks \(2\le k\le8\) and the positive upper masks or weighted semiprime used in [TwoMarkNegativeCompensation.md](TwoMarkNegativeCompensation.md), the requisite progression error sum holds through \(e\le D_0=x^{.210}\). Indeed \(s z e\le x^{.14+.14+.21}=x^{.49}\), so use full generalized BV on the actual \(k\)-prime product with both grouped scales polynomial, preserving the same central boundary and unit masks. At fixed modulus \(a=s z e\), there are at most \(\tau(a)^C\) factorization choices, even allowing this arbitrary \(\mathcal Z\); the sign weights \(R_Y(z)\) also have divisor bound. The reduced progression error at modulus \(a\) is trivially \(O(x/\phi(a))\), since the individual ordered-product weights after normalization are bounded by fixed constants and the interval count is \(O(x/a+1)\). By Cauchy, ordinary absolute BV with arbitrary log reserve therefore absorbs any fixed divisor weights, via \(\sum_{a\le x}\tau(a)^C/\phi(a)\ll L^{C'}\). The main boundary and weight approximations are exactly those used in the two-mark proof. This makes the total progression error \(O_D(xL^{-D})\) even after the \(R_Y(z)\) summation. This is precisely the fixed-\(N\) varying-\(z\) calculation that permits arbitrary core families.

With \(D_0=x^{.210}\) and sifting scale \(Y\) the lower and upper linear constants are \(2\log 2/.210-o(1)\) and \(2/.210+o(1)\) respectively, after multiplying by \(e^{-\gamma}/.070\); the local factors in (6) remain explicit. Thus the weighted row main normalized by the true \(m\) product density has common label factor
\[
              W_s^\circ\frac{R_Y(z)\mathfrak S(Ns z)}{(s-1)z}.
\]
Here \(1/\phi(z)\) from the true conditional base cancels precisely \(\phi(z)/z\) in (6). The moving physical \(W_s(q)\) equals \(W_s^\circ+O(1/L)\); the difference is relative \(o(1)\) times the same total nonnegative main, plus log-small arithmetic error, by the genuine upper sieve. No uniform boundedness of the harmonic core sum by \(O(1)\) is required.

## 4. Net negative sign and an explicit new disjoint sector

Since \(z\le x^{.14}\) and \(q\ge x^{.86}/2\), one has \(.83\le \log w/\log q\le1\) for large \(x\). Use (2) and \(R_Y(z)>0\). The same actual \(m\) ranks, densities and half-switch sign as in §4 of [TwoMarkNegativeCompensation.md](TwoMarkNegativeCompensation.md) apply without change: rank two weighted negative density \(D_2>1.12\), odd and repeated ranks negligible relative to the common positive label mass (with arbitrary log additive error), and upper positive density for even ranks \(4,6,8\) less than .545 with all actual cutoff and neck errors paid. Since the label factor is *the same* for the upper and lower sieve, the net negative coefficient on \(x/(2L)\) times this factor is at least
\[
         \frac{.83\cdot 1.12\cdot 2\log 2-.545\cdot 2}{.210}-o(1)
                     > .90 .
\]
Here \(\log2>.69\) gives the indicated strict margin. The older upper bound with .92 on the reverse ratio is not needed. This proves (3). It is valid for actual \(z\) with an unbounded number of small prime factors because the only rank restriction is on the reflected \(m\), and the outer core weight was handled by divisor-weighted BV.

For one explicit nonoverlapping illustration, take \(z=p t\) with actual primes \(p,t\) in any of the following three rectangles in \(\log_x\) coordinates:
\[
\begin{array}{c|c}
 (.006,.012)&(.065,.070)\\
 (.012,.024)&(.059,.070)\\
 (.024,.036)&(.047,.070).
\end{array}
\tag{7}
\]
They have \(p t>Y,\ z<x^{.14}\), \(p< x^{.036}\), and \(R_Y(z)=1\). Thus they are disjoint from both earlier compensation sectors. The prime harmonic sum \(\sum_{z\in\mathcal Z}1/z\) here tends to
\[
  (\log 2)\log(70/65)+(\log2)\log(70/59)
                 +\log(3/2)\log(70/47) > .329.
\]
The inequality can be certified by the positive \(\operatorname{arctanh}\) series (e.g. \(\log 2>.69,\log(70/65)>.074,\log(70/59)>.170,\log(3/2)>.405,\log(70/47)>.398\)). Since \(W_s^\circ>.44\), \(\sum_s1/(s-1)>.336+o(1)\), and \(\mathfrak S(Ns z)\ge\mathfrak S(N)\), (3) gives a further signed contribution \(\le-.043 M_N\) eventually. These are whole macro-rough reflected sectors, not selections of only their negative ranks.

## 5. Exact reason the principal model cannot settle the rest

The small-core main coefficient has an exact untruncated Euler accounting. At fixed \(s\nmid N\), for unrestricted positive \(Y\)-smooth cores \(z\) with \((z,Ns)=1\), write
\[
             h(z)=\frac{\mathfrak S(Ns z)}{\mathfrak S(Ns)z}.
\]
For an odd \(p\le Y\) outside \(Ns\), its \(p^j,\ j\ge1\), harmonic contribution is \(A_p=1/(p-2)\) upon summation over \(j\), so \(B_p=1+A_p=(p-1)/(p-2)\). Then absolute convergence over the finitely many underlying primes and literal divisor switching give
\[
 \sum_{\substack{z\ Y{\rm -smooth}\\(z,Ns)=1}} R_Y(z)h(z)
   =\left(\prod_{\substack{p\le Y\\p\nmid Ns}}B_p\right)
       \sum_{\substack{d>Y,\ d\ Y{\rm -smooth}\\(d,Ns)=1}}\frac{\mu(d)}{\phi(d)}
   =1+O_D(L^{-D}).
\tag{8}
\]
For the first equality a required squarefree \(d\mid z\) inserts \(A_p/B_p=1/(p-1)\) at \(p\mid d\). For the second, the full sum in \(d\) is the inverse of the product \(B_p\), while every \(d\le Y\) is automatically smooth and its finite coprime \(\mu/\phi\) harmonic sum is arbitrarily log small from (11) of [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md). The finite product is log-bounded uniformly. Thus the formal complete signed small-core reservoir has principal mass \(+1\), balancing the \(-1\) part of the fully rough coefficient; it is not an additional net bias proving Goldbach. Equation (8) is about the **untruncated principal model**, not the actual remaining sign in the finite \(q\)-sum (which has moving \(w\), the true \(\Lambda(q)\) term on \(z=1\), and large/negative cores). The theorem (3) captures a genuinely larger actual negative class, but supplies no upper bound for that complement and no binary Goldbach conclusion.

[Chan’s November finite sieve construction](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also uses unique small/rough factorization and sign-aware beta weights; [Pham’s restricted Chen sieve](https://www.preprints.org/manuscript/202611.0694) analyzes other local Euler densities. Here the signed core factor is the exact Möbius divisor sum of a genuinely different whole reverse-Vaughan cutoff, and the (1/p) density at a prime already dividing the core must be kept. The principal cancellation in (8) is not a sign for the remaining actual row.
