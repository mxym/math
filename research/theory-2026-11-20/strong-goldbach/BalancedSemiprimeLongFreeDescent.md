# Whole reverse long-free descent through the quotient square root on actual reflected semiprimes

Use \(N=2x\), \(L=\log x\), \(m=N-sq\in[x,3x/2)\), \(sq\in(x/2,x]\), \((m,N)=1\), with \(x^{.10}<s<x^{.14}\) an actual prime and \((s,N)=1\). Keep the exact \(W_s(q)=K_{P_3}(sq)\), \(M_N=\mathfrak S(N)x/(2L)\), and the smooth reverse cutoff \(B_f(q)\) of [SmoothReverseCoreShield.md](SmoothReverseCoreShield.md), with \(Y=x^{.070}\). In an opened row \(q\) is an integer, not an actual prime.

Fix \(0<\eta<.002\) and \(w=\eta/1000\) **before** taking \(x\to\infty\). Put \(\alpha=\log_x s\), \(c_s=(1-\alpha)/2\), and
\[
             B(s)=x^{c_s+2\eta},
 \qquad |\log_x p-(c_s-\eta)|<w.
\tag{1}
\]
Retain the **actual** reflected semiprimes \(m=p h\) with \(p,h\) prime and the displayed band, and write \(F_s(m)=-2\log p\) there, zero otherwise. It is the exact linear half-cut weight on this physical rank-two band, since \(p<h\) with a fixed exponent margin. In particular the weight is genuine even when \(s,p\) move. This is a different reflected rank-two band from [TrueSemiprimeReverseDispersion.md](TrueSemiprimeReverseDispersion.md).

Use the true reverse long-free coefficients \(P_{B(s)}(r),H_{B(s)}(k)\) of [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md), defined as sums over \(r=t b\) or \(k=t b\) with integer \(b>B(s)\). They are **not** restricted to prime \(b\). Write
\[
 B_{mathrm{cen},s}(q)=
  \frac{1}{\log q}\sum_{r k\mid q}
       (\mu(r)-P_{B(s)}(r))(\Lambda(k)-H_{B(s)}(k))
           \Phi(\log r/\log Y)1_{k>Y}.
\tag{2}
\]
Here \(\Phi(0)=0\) and the fixed smooth \(\Phi\) equals 1 above a compact subinterval of \((0,1)\), as in the reverse note.

Let \(\mathcal R(F)\) be the exact profilewise reference on this true rank-two band:
\[
  \mathcal R(F)=
    \sum_{\substack{s\text{ prime}\\(s,N)=1}}
       \frac{\mathfrak S(Ns)}{s-1}
       \sum_{\substack{x\le m<3x/2\\(m,Ns)=1}}
     F_s(m)\frac{W_s((N-m)/s)}{\log((N-m)/s)}.
\tag{3}
\]
It is negative, and \(-\mathcal R(F)\asymp w M_N\) with absolute positive comparison constants in the fixed-\(\eta\) asymptotic. Then, uniformly at the individual fixed target, for every fixed \(D>0\),
\[
 \sum_{s,q}W_s(q)F_s(m)\{B_f(q)-B_{\mathrm{cen},s}(q)\}
                 =-\mathcal R(F)+O_{D,\eta,f}(xL^{-D}).
\tag{4}
\]
Thus the full switched long-free piece has a **nonzero** main, positive in this application. Using [CompensationNeutrality.md](CompensationNeutrality.md), the remaining centered sum equals the entire actual prime-quotient statistic
\[
          \sum_{s,q} W_s(q)F_s(m)B_{\mathrm{cen},s}(q)
            = \sum_{s,\ q\ \mathrm{prime}} W_s(q) F_s(m)+O_{D,\eta,f}(xL^{-D}).

\tag{5}
\]
The prime restriction on the right of (5) is on the quotient \(q\), not on \(m\), which is the selected true semiprime.

In this centered physical row the **whole** sector \(\Omega(q)\le2\) has absolute contribution
\[
                 O(\eta\,|\mathcal R(F)|)+o_{\eta,f}(M_N).
\tag{6}
\]
The implied constant in the first term is independent of \(\eta\). This is a bounded-rank reduction of the genuine sum in (5), not an estimate of the remaining ranks or a bound on its full discrepancy from (3).

## 1. Collapse the two long-free pieces before switching

On actual inputs \(r,k\le q\le x/s\), the reciprocal Heath--Brown identities used in [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md) apply with order 10 and \(u=\mu1_{\le x^{1/10}}\). Their marked-free coefficient formulas hold unchanged with (1). Indeed every marked complementary \(t\) is \(\le x/B(s)<x^{.58}\), where the support identities (4)--(5) of that note are literal. Since
\(B(s)^2=(x/s)x^{4\eta}>q\), at most one free factor can exceed \(B(s)\), across **both** expansions together. In particular the product of the two marked pieces is zero, and the difference between the weights before/after modification is exactly the long-\(r\) plus long-\(k\) part, with **plus** signs.

For fixed \(b>B(s)\), set \(a=q/b\). In the long-\(r\) part \(r=t b\), the reverse \(\Phi=1\) automatically, while \(k>Y\) is kept. Summing the free original \(j\) and the short \(t\) together gives \(\mu_2*1=\mu\), so this coefficient at \(a\) is
\[
                         - (\mu*\Lambda_{>Y})(a).
\]
In the long-\(k\) part \(k=t b>Y\) automatically and the reverse \(\Phi\) on \(r\) remains. Summing the original \(j\) together with \(t\) gives
\(\sum_{t\mid d}\{\mu(t)\log b-(\mu*\Lambda)(t)\}=1_{d=1}\log b-\Lambda(d)\).
If \((\mu\Phi)(a)=\mu(a)\Phi(\log a/\log Y)\), the full coefficient is therefore
\[
      L(a,b)=-(\mu*\Lambda_{>Y})(a)
                    +(\mu\Phi)(a)\log b-(\mu\Phi*\Lambda)(a).
\tag{7}
\]
Each of the three coefficients before its explicit log is log-bounded, by the exact identity \(\sum_{d\mid a}\Lambda(d)=\log a\) and boundedness of the fixed \(\Phi\). There is no mask on the old factors \(r,k,j\) in (4) except their reverse opening tests; extra coupled cuts would not in general allow (7). All coprimality conditions survive this collapse: on the original unit support every factor of \(q\) is coprime to \(N\), and the switched physical equation with \((m,N)=1\) forces this same condition on \(s,a,b\).

Now the literal switched modulus is \(s a\), and the exact free value is \(b=(N-m)/(s a)\). The true upper endpoint on \(a\) is
\[
               a<Z_s(m)=\frac{N-m}{s B(s)}
                        \asymp x^{c_s-2\eta}.
\tag{8}
\]
There is precisely one \(b\) for each \(m\equiv N\bmod s a\), \(a\) in this interval. In particular (4) concerns all of these a labels without a factorability hypothesis on a itself. The total modulus exponent at the upper cap is \((1+\alpha)/2-2\eta\), approximately \(.55\) to \(.57\), rather than only the ordinary square-root range.

## 2. Dispersion at every switched modulus in (8)

Use [Lichtman, arXiv:2309.08522v1, Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5) with short SW sequence the genuine prime \(p\) at exponent \(\beta=c_s-\eta+O(w)\), long sequence genuine \(h\), modulus slots \((a,s,1)\), and actual residue \(N=2x<x^{1+\varepsilon}\). These slots are literal 1-bounded after fixed log divisions as in [TrueSemiprimeReverseDispersion.md](TrueSemiprimeReverseDispersion.md). The third is a legitimate unit slot: in the source's dyadic convention \((Q_i',2Q_i']\) (its application following (5.20)), take \(Q_3'=1/2\) and the coefficient supported on 1. Proposition 5.2 imposes no positive lower power on this slot; its proof factors that unit as rough unit times smooth unit. This does **not** insert a previously absent modulus 2.

Let \(v_1\le c_s-2\eta+o(1)\), \(v_2=\alpha+o(1)\), \(v_3=0+o(1)\), and \(\theta=7/32\). At the maximum \(v_1\) the four rails, ignoring width first, are
\[
\begin{array}{ll}
 v_1-\beta=-\eta,&2\beta+v_2+2v_3=1-2\eta,\\
 \theta+\beta+v_1+5v_2+2v_3=1+\theta+4\alpha-3\eta,
   &(1+2\theta)\beta+v_1+(5-2\theta)v_2+(2+2\theta)v_3
           =1+\theta+(4-3\theta)\alpha-(3+2\theta)\eta.
\end{array}
\]
The last two are \(<1.78\) and \(<1.69\) throughout the actual \(s\)-band. All needed inequalities improve at smaller \(a\). Width changes \(O(w)\), fixed dyad factors \(o(1)\), and the actual \(2^\theta\) factor in the third are absorbed, e.g. with source reserve \(\varepsilon=\eta/100\). The genuine \(p\) with its independent \(N\)-unit mask is polyrough and satisfies auxiliary SW on every independent prime interval, including the fixed log test, exactly as in the preceding dispersion proof.

To implement the actual cutoffs, use disjoint log-fine boxes in \(s,p,h\) and central physical \(m\), first freezing \(s,m\) at their midpoints in (8). A wrongly included/excluded physical point obeys \(|b/B(s)-1|\ll L^{-K}\). At each fixed \(s\sim S\), there are \(O(x/(s B(s)))\) possible \(a\); for each such \(a\) at most \(O(B(s)L^{-K}+1)\) wrong integral \(b\). Summing over the dyad gives \(O(xL^{-K}+x/B_{min})\) possibilities; log and divisor factors paid by Cauchy and global moments on \(m,N-m\) are harmless. The p-band moving edge has \(s^{1/2}p\) at relative distance \(O(L^{-K})\) from its endpoint, since \(p=x^{c_s-\eta\pm w}\) is equivalently \(s^{1/2}p=x^{1/2-\eta\pm w}\). With \(s,p\) fixed, count \(h\) in the true residue modulo \(s\) exactly as in the preceding note. In the reduced mean the error in (8) is its harmonic boundary \(O(L^C(L^{-K}+1/Z_s(m)))\); the p-band boundary is paid by counting \(h\) and summing \(1/p\) over its thin interval. Exact \(W_s\), \(1/\log q\) and \(\log b=\log(N-m)-\log s-\log a\) are separated by the same fixed Taylor expansions or included in these fine boxes. No hard physical ordering on the already collapsed q factors is added. The resulting signed weighted discrepancy from the exact reduced mean is \(O_D(xL^{-D})\).

In that reduced mean put \(Q=(N-m)/s\) and \(F_0=N s m\) for a fixed outer \(s,m\) with \((m,Ns)=1\). The total harmonic coefficient before \(W_s(Q)/(s-1)\) is
\[
       \frac1{\log Q}
        \sum_{a<Z_s(m),(a,F_0)=1}
                                \frac{L(a,Q/a)}{\phi(a)} .
\tag{9}
\]
The true reduced mean is \(1/\phi(sa)\), and \(s\mid a\) is not forbidden physically. At fixed \(s,m\), those terms have absolute harmonic mass \(O(L^C/s)\) before the outer \(s\)-factor: \(L(a,b)\ll L\) and \(\sum_{a\le x,\ s\mid a}1/\phi(a)\ll L^C/s\). The exact \(\phi(s)\phi(a)/\phi(sa)\) correction is at most one. Accordingly \(s\mid a\) may be excluded at power-small cost. The other condition \((m,s)=1\) is required in the reduced mean and automatically holds in the physical row. This gives (9).

For a fixed sharp reverse \(U=Y^u\) in the smoothing support, evaluate (7) by the finite masked \(\mu/\phi\) moments of [UnmarkedSemiprimeWholeTypeI.md](UnmarkedSemiprimeWholeTypeI.md), with \(Z=Z_s(m)\asymp x^{c_s-2\eta}\).
* The first harmonic term is \(-\mathfrak S(F_0)+O_D(L^{-D})\). Indeed \(\mu*\Lambda=-\mu\log\). For the removed \(\Lambda_{\le Y}\) convolution, fix \(\ell=p'^{j}\le Y\) and use the exact local overlap factor \(1-p'^{-1}1_{p'\mid d}\) in \(1/\phi(d\ell)\). Both endpoints \(Z/\ell\) or \(Z/(\ell p')\) are polynomially long here, so their constant \(\mu/\phi\) moments are log-small.
* The middle term is the difference of the two masked \(\mu/\phi\) log moments at \(U,Z\), with \(\log(Q/a)=\log Q-\log a\); each difference is log-small.
* The last term is log-small because the full \(\mu*\Lambda\) harmonic main \(\mathfrak S(F_0)\) exactly equals the harmonic main of \(\mu_{\le U}*\Lambda\). For the latter, fix \(d\le U\) and use the ordinary harmonic PNT and the correction
\[
 \sum_{(\ell,F_0)=1,\ \ell\le Z/d} \frac{\Lambda(\ell)}{\phi(d\ell)}
  =\frac1{\phi(d)}\left(\log(Z/d)+C_{F_0}
      -\sum_{p'\mid d}\frac{\log p'}{(p'-1)^2}+O_D(L^{-D})\right).
\]
This is the identity in §2 of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md), with polynomially long endpoint here. The extra prime sum is killed by fixing \(p'\le\sqrt U\) and the unit \(\mu/\phi\) moment at \(U/p'\); larger primes are power-small by absolute summation.

Average over \(u\). Thus (9) is \(-\mathfrak S(N s m)/\log Q\) plus arbitrary log reserve. All prime factors of a retained \(m\) are polynomially large, so \(\mathfrak S(N s m)/\mathfrak S(N s)=1+O(x^{-c})\). This proves (4), including its sign. The proof of the matching identity in [CompensationNeutrality.md](CompensationNeutrality.md) applies to this \(s\)-dependent p-band using the same independent boxes and the same physical edges (its short moduli are \(s e\le x^{.28}\)). This gives (5). Finally, \(-\mathcal R(F)\asymp w M_N\) follows by prime PNT / partial summation: at each \(s\), \(\sum_{p\text{ in (1)}}1/p\asymp w\) uniformly, the true \(h\)-interval has \(\asymp x/(p L)\) primes, \(|F_s|\asymp L\), \(W_s\gg1\), \(\log Q\asymp L\), and the actual prime \(s\)-band has harmonic mass tending to \(\log(7/5)\). The removed prime divisors of \(Ns\) in these polynomially large prime bands cost a negative power of \(x\). Constants in these asymptotic comparisons can be taken independent of fixed \(\eta,w\); the onset of the asymptotic may depend on them.

## 3. Pointwise rank-two support and the actual neck sieve

If \(q=P t\) has a true prime \(P>B(s)\), then each centered reverse factor in (2) vanishes if it contains \(P\), by the exact identities at the end of [SwitchedLongFreeReverseColumns.md](SwitchedLongFreeReverseColumns.md). One has \(t<Z_s(m)<B(s)\). Therefore \(P\) must go into the completely free original \(j\), and the remaining coefficient equals the original short reverse high coefficient on \(t\), divided by \(\log q\), not \(\log t\). This is zero whenever \(t=1\) or \(t\) is prime, since no factorization \(r k\mid t\) then has both \(r>1\) (needed for \(\Phi\)) and \(k>Y\). In particular every actual prime q and every squarefree semiprime q with its larger prime above \(B(s)\) is exactly absent from the centered row. If the smaller semiprime factor \(a\le Y\), its partner has to exceed \(B(s)\) by polynomial powers, so this includes **all** squarefree semiprime small cores. Pointwise the original weight on \(q=a b\) is \(-1\) when both primes exceed Y, and \(-\Phi(\log a/\log Y)\log b/\log q\) when \(a\le Y<b\); in both such long-factor cases the long switch removes it exactly. When neither factor exceeds \(B(s)\), the only nonzero reverse splits have \(r,k\le B(s)\), so the centered weight equals the original \(-1\). True q squares in this band have weight \(-1/2\), and are power-negligible by their count \(O(\sum_s\sqrt{x/s})=O(x^{.57})\) before divisor/log weights.

It remains to bound the absolute semiprime neck with both q prime factors \(a\le b\le B(s)\). They lie in actual ranges
\[
           x^{c_s-2\eta+o(1)}\le a\le x^{c_s+o(1)},
       \qquad x^{c_s+o(1)}\le b\le x^{c_s+2\eta}.
\tag{10}
\]
Instead of fixing all three short labels and losing the very short physical affine interval, **reverse which prime product supplies dispersion**. Use the genuine triple \(n=s a b\) in \(I\) as the source sequence, and for each genuine \(p\) in (1) upper-sieve \(h=(N-n)/p\). At a squarefree sieve divisor \(e\mid h\), the exact progression on this n input is \(n\equiv N\bmod p e\). Choose level \(D_h=x^{.070}\), sieve threshold \(z_h=x^{.035}\), and the usual upper dimension-one linear weights \(\lambda_e^+\) supported on the sieve primes below \(z_h\) and prime to \(N\). These bounds are valid for every true h prime here; the weights are independent of the variable labels p and s, since both exceed the sifting range. This gives a positive upper envelope for the unweighted actual five-prime neck count.

Apply the same Lichtman Proposition 5.2 now with slots \((p,e,1)\), SW short group the **larger true q prime** b, and other group \(s a\) (disjoint factor scales, hence its independent coefficient is 1-bounded). In (10) the slot-1 exponent satisfies \(\log_x p\le c_s-\eta+w<\log_x b-\eta/2\) for large x. The second rail obeys
\[
           2\log_x b+\log_x e
             \le 1-\alpha+4\eta+.070<.979 ;
\]
the last two are \(<1.50\) with fixed reserves, by \(c_s\le.45\), \(\eta<.002\). Again \(Q_3'=1/2\) is the unit slot, and \(N=2x\) is the actual moving residue allowed by the source. The p-band, b-bound, sorted condition and product n interval can be separated by the independent log meshes of §2 **before** grouping \(s a\). A moving b-bound edge fixes s and b in its thin relative interval and then counts the true remaining product a; it gives the same \(O(xL^{-K}+x^c)\) physical bound with \(c<1\) by the reciprocal labels. The \(a\le b\) boundary similarly fixes a and gives only a thin interval in b. The moving p-bound when p is an outer modulus label is handled using \(p\mid m\) and the triple physical divisor envelope: for fixed s,p the integer \(n=sq\equiv N\bmod p\) lies in one class in q mod p, and the same count (4) of [TrueSemiprimeReverseDispersion.md](TrueSemiprimeReverseDispersion.md) applies. Once e is summed, its possible boundary multiplicity is bounded by the divisors of h; positive envelope not needed in the edge error. In the reduced mean all these edges are paid with harmonic sums. There is no additional arbitrary near-neck mask inserted after grouping. Thus the error after the exact upper-sieve sum has arbitrary log reserve.

In the reduced mean, \((n,e)=1\) is automatic since every true n factor exceeds \(z_h\). The condition \((n,p)=1\) is retained at first. Physically \(p\mid n\) and \(p\mid m\) would force \(p\mid N\), hence is impossible; the only possible reduced-mean coincidence is \(p=a\) (\(b\) lies strictly higher and s far lower). Its removal from the unconditioned product count costs power-small amounts after \(1/\phi(p)\) and all e weights: for fixed s,p the eligible b count is \(O(x/(sp)+1)\) and the second \(1/p\) is a negative power after summing p. Consequently the common dimension-one mean factor, following \(\phi(pe)=\phi(p)\phi(e)\), is
\[
             \sum_e\frac{\lambda_e^+}{\phi(e)}
                     \ll \frac{\mathfrak S(N)}{L}.
\]
Here the local density is \(1/(\ell-1)\) at sieve primes \(\ell\nmid N\), zero otherwise, with no \(p\)-dependence: \(p>z_h\). The standard uniform Mertens product and upper \(F(2)\) give the bound, with absolute constant for the fixed level \(D_h\).

At fixed s the actual triple n-support in (10) has
\(O((x/(sL))(\eta+o(1)))\) members, by summing the true primes \(a\) over their harmonic neck and applying the uniform ordinary PNT upper for \(b\) (both exponents \(>.42\)). The true \(p\)-band has harmonic mass \(O(w+o(1))\) uniformly. Thus the whole five-prime neck count is
\[
                  O(\eta w\,\mathfrak S(N)x/L^2)
                              +o_\eta(M_N/L).
\]
The implied constant in the first term is absolute, because all sieve rails unrelated to the width have fixed margins and the sieve level is independent of \(\eta\); error constants and the onset of prime-interval asymptotics are allowed to depend on fixed \(\eta\). Since the true reflected weight is \(O(L)\) and the surviving coefficient is \(-1\), this gives (6).

## 4. What survives and why (6) does not decide the sign

For fully \(Y\)-rough q of squarefree rank three, the pointwise next signs are already opposite. In (7), for \(a\mid q\), \(a>1\) one has
\(L(a,q/a)=\mu(a)(\log q+\log a)+\Lambda(a)\).
If \(q=P t\) with \(P>B(s)\), the residual instead follows directly from the free-j observation:
\[
         B_{\mathrm{cen},s}(q)=-\log t/\log q<0\qquad
                        (t\text{ a true fully rough semiprime}).
\]
This is **adverse** multiplied by the negative reflected weight. If all three q primes are \(\le B(s)\), there cannot be any two-prime divisor \(a<q/B(s)\) (its complement would exceed B). Each singleton below \(q/B(s)\) contributes \(-\log q\) to the removed part, so the centered coefficient is the number of such singletons minus one. At most one q prime can be at or above \(q/B(s)\), since a third factor \(>Y\) and \(.070>4\eta\) would otherwise make the product too large. This residual is therefore positive (1 or 2), **favorable** against the negative reflected weight. Neither affine population is counted asymptotically here. Higher ranks and nontrivial small cores above rank two also survive; (6) makes no assertion about them. In particular the exact nonzero long-free main (4) cannot be silently declared canceled or counted as net positive prime slack. Strong Goldbach remains open.

## Related work

[Lichtman's Proposition 5.2](https://arxiv.org/abs/2309.08522) supplies the distribution, not a lower bound for the whole true-prime row. Related 2026 work includes [Arneth's marked-switching and parity audit](https://zenodo.org/records/23011047). The exact whole long-free main and the five-prime neck bound here concern the reflected semiprime geometry in (1), not the larger problem or the remaining rank-three sign comparison.
