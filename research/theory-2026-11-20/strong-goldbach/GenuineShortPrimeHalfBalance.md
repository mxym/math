# A strict rough half-score balance on the genuine short-prime quotient family

This is a fixed-target result on a true product source, not a prime-pair bound. The independent short **prime already occurring in the first quotient-triprime family** permits Fouvry's arbitrary-coefficient convolution theorem past the square root. The resulting complete rough half-score has a strictly positive weighted principal term. Simultaneously an explicit physical family of reflected composites has a strictly negative score and a uniformly positive lower occupancy. Neither fact, nor the two together, bounds the signed remainder of the original Goldbach test.

## 1. Actual family and the half-score

Use \(N=2x\), \(L=\log x\), \(n=sq\in(x/2,x]\), \(m=N-n\), the unit condition \((n,N)=1\), and \(W_s(q)=(1-t)(1-2t)^2\), \(t=\log s/\log n\). Use exactly the first profile of [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md):
\[
 q=a P Q,qquad x^{.010}<a<x^{.070},qquad
 P,Q<x^{.501},qquad aP>x^{.501},qquad x^{.10}<s<x^{.14}.
\tag{1}
\]
All these variables are actual primes and \(a,P,Q\) are distinct. The other factors \(P,Q\) both exceed \(x^{.28}\) once \(x\) is large. In fact \(P>x^{.431}\) and \(Q=n/(s aP)<x^{.399}\), so \(P\) is always the larger macroprime. This identifies \(P\) independently of the value of \(a\) once the long cofactor \(A=sPQ\) is given. The label \(s\) is also unique on this family. Write \(\mathcal Q_1\) for the physical rows in (1), and
\[
 A_1(N)=\sum_{\mathcal Q_1}W_s(q)
     =(I_1+o(1))\frac{x}{2L},\qquad
 M_N=\frac{\mathfrak S(N)x}{2L},
\]
with the exact constant \(I_1>.05097\) from the ordinary prime product calculation in §3 of that note. No prime condition on \(m\) is used to evaluate \(A_1\).

Fix sufficiently small \(\kappa>0\), \(z=x^\kappa\), and take \(J=\lceil1/\kappa\rceil\). With \(u=1-2t\), define the polynomial
\[
 f(t)=A u-\sum_{j=1}^{J}c_j u^{2j+1},
 \qquad
 c_1=1/4,\quad c_j=\frac{1}{4j(J-1)}\ (2\le j\le J),\quad
 A=1+\sum c_j.
\tag{2}
\]
Thus \(\sum 2j c_j=1\), \(f(0)=1\), \(f'(0)=0\), \(f(1/2)=0\), and \(f\) is antisymmetric about \(1/2\). On \([0,1/2]\), \(f\ge 1-2t\), \(0\le f\le1\), and \(f'\le0\). Indeed \(-f'(t)=2\sum (2j+1)c_j(1-u^{2j})\) is nonnegative and bounded by 3, and its cubic term alone gives \(-f'(t)\ge3t\) there. Every odd derivative of order \(3\le r\le2J+1\) is uniformly strictly positive on \([0,1]\), since the corresponding term with \(2j+1=r\) is a positive constant and all other nonzero terms are even powers of \(u\) with nonnegative coefficients.

For squarefree \(r>1\) write
\[
 H_f(r)=\sum_{d\mid r,\,d<\sqrt r}\mu(d)f(\log d/\log r).
\]
The total scored sum used here is
\[
 \mathcal H(N)=\sum_{\substack{\mathcal Q_1\\m\text{ squarefree},\ P^-(m)>z}}
                  W_s(q)\log m\,H_f(m).
\tag{3}
\]
In particular a true prime \(m\) has score \(H_f(m)=1\), and is included. The half sum on any squarefree odd rank equals one half its full polynomial divisor sum by antisymmetry of \(f\) and of the Möbius signs under complementary divisors. Hence it is strictly negative on **all** odd composite ranks allowed by this roughness: for factors of normalized logarithms \(t_i>0\) the full sum is \((-1)^r\prod t_i\) times the average of \(f^{(r)}\) over the box of sums of points in \([0,t_i]\), from repeated one-dimensional differences. The true rank is at most \((1+o(1))/\kappa<2J+1\). This does not assert an even-rank sign in general.

## 2. A strict fixed-target principal lower

Uniformly for all large even \(N\) there is an absolute \(c>0\) such that
\[
                         \mathcal H(N)\ge c\kappa I_1 M_N .
\tag{4}
\]
The asymptotic argument keeps \(\kappa\) fixed sufficiently small before letting \(x\) grow, with the resulting fixed \(f\) in (2).

We use precisely [Fouvry, *Autour du théorème de Bombieri–Vinogradov II*, Corollaire 1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf), not the well-factorable second corollary. In a dyad of the true short prime \(a\), let \(\nu=\log_x a\) up to \(O(1/L)\); the long source is the weighted sequence on \(A=sPQ\). Independently supported sequences are of lengths \(x^\nu,x^{1-\nu}\). For the short prime, SW on any actual fine interval with the auxiliary coprimality condition follows from ordinary prime SW and a trivial count of deleted prime divisors; all prime labels dividing \(N\) are separately excluded. The long coefficient is divisor-bounded and needs no SW. For arbitrary divisor-bounded coefficients on the actual moduli, Fouvry permits a fixed power margin below the exponent
\[
                  \min\{(1+\nu)/2,(4-6\nu)/7\}.
\]
On the full range \(.010\le\nu\le.070\) this is at least \(.505\). The common residue is the actual \(N\); the source scale in the theorem is four times the product of lower ends of its dyads, which is \(>2x=N\) except on the central endpoint \(n=x/2\) with vanishing edge width. For literal fixed-power scope one may extend the fine-box lower endpoints to a product just above \(x/2\) after omitting a log-small boundary strip, as below. No small-residue hypothesis or factorability of the Mertens coefficients is imposed.

The transfer with arithmetic-dependent source support is justified as follows. Use relative \(L^{-K}\) meshes for the ordinary coordinates \(a,A\); in the long coefficient keep the identified \(P,Q,s\) as exact labels, cut \(aP>x^{.501}\) at a frozen \(a\) on its small mesh interval, and keep the remaining large-cofactor tests independent of \(a\). Any incorrectly admitted row has either \(n\) in an \(O(xL^{-K})\) strip at a central endpoint, or the true divisor \(aP\) of its physical \(n\) within relative \(O(L^{-K})\) of \(x^{.501}\). The latter has at most \(O(x L^{-K}+x^{.499})\) such integers by summing all multiples of the labelled divisor, before weights. Freeze the moving \(d<\sqrt m\) at each retained source rectangle; the only newly changed labels have \(m=dk\) with \(d\asymp\sqrt x\), \(|k-d|\ll\sqrt x L^{-K}\), altogether \(O(xL^{-K}+\sqrt x)\) before weights. All counts are on the single physical strips and not paid once per box at this size. Fixed divisor moments with Cauchy control the weighted border errors; the principal terms obey the same argument with harmonic sums over the divisors. Smooth functions of \(n,m\) may also be frozen within rectangles at arbitrary log precision, while \(W_s(q)\) retains its finitely many separated powers of \(\log s\) and smooth physical factors. One may first discard the central strip \(n-x/2\le 10xL^{-K}\) so that actual lower mesh endpoints meet the residue size hypothesis strictly. Log-power costs in the resulting independent boxes are absorbed by Fouvry. This follows the [same-cofactor proof](https://github.com/mxym/math/blob/a75fffdaf7a7611bb4d48c1c9a1c161b92d055b4/research/theory-2026-11-20/strong-goldbach/paired_cofactor_gate/Proof.md), but the long cofactor here has all three indicated prime labels, and **its unknown reflected prime occupancy is not transferred**.

In (3) we may drop squarefreeness of the \(z\)-rough \(m\) at power-small cost using \(\sum_{p>z} x/p^2\) and fixed divisor bounds (any multiple of \(p^2\) also has \(p<2\sqrt x\)). Its Möbius divisor labels \(d\) are \(z\)-rough, hence coprime to the sifting variables \(w\) with prime factors \(\le z\). Use separately upper and lower fundamental-lemma weights at level \(D=x^{.004}\), swapping for negative divisor coefficients. Now \(dw\ll x^{.504}\), inside the margin above, and \(dw\) identifies its smooth and rough parts. All the actual counted progressions have common reduced residue \(N\). The fixed-target prime ratio model for \(w\), after reversing the coprime principal sum, is
\[
 V_N(z)=\prod_{p\le z,\ p\nmid N}\Big(1-\frac1{p-1}\Big)
       =(1+o_\kappa(1))\frac{e^{-\gamma}\mathfrak S(N)}{\kappa L}.
\tag{5}
\]
There is no dependence on the physical \(n\) in this local factor because all its prime factors exceed \(x^{.010}>z\). For \(p\mid N,p>z\) the factors contribute only \(1+o_\kappa(1)\), since there are at most \(O(1/\kappa)\) of them. The sieve model has the uniform dimension-one hypothesis with density at most \(1/(p-1)\) on odd primes, and excludes 2 since \(N\) is even. The relative upper/lower fundamental-lemma error is \(O(S^{-S/2})\) with \(S=.004/\kappa\) sufficiently large (as in Koukoulopoulos Theorem 19.1 used in the cited same-cofactor proof). This is in the ***absolute*** harmonic sum for \(d\), \(O(1/\kappa)\), when estimating the signed expression.

The principal \(d\)-measure is explicitly the rough harmonic Möbius measure. Its cumulative mass through exponent \(t\) converges uniformly to Dickman's \(\rho(t/\kappa)\) for \(0\le t\le1/2\), with its jump from the unit at \(t=0\). For this fact expand \(d\) into its ordered distinct prime factors (divide by their factorial), using the finite number \(\le1/\kappa\) of slots, and prime reciprocal measure \(du/u\) on each slot. Differentiating the resulting signed simplex expansion gives \(u\rho'(u)=-\rho(u-1)\) and \(\rho=1\) on \([0,1]\), exactly as in the quoted proof. Uniformity on the compact window follows from the continuous finite-rank simplex boundaries; and omitting the primes dividing the actual \(nN\) above \(z\), or replacing \(1/\phi(d)\) by \(1/d\), has error \(o_\kappa(1)\) by the bounded number of polynomially large primes. Similarly \(\log d/\log m\) differs from \(\log_x d\) by \(O(1/L)\), harmless in the absolute harmonic majorant, and the frozen cutoff has exponent \(.5+O(1/L)\). Partial summation gives the signed main coefficient
\[
 G_f(\kappa)=-\int_0^{1/2}\rho(t/\kappa) f'(t)\,dt
                  \ \ge\ \tfrac32\kappa^2 ,
\]
where the upper endpoint term is zero and the unit at \(t=0\) is included by the Stieltjes integral. Thus the full actual expression (3) is
\[
 \mathcal H(N)=L V_N(z) A_1(N)\left[
          G_f(\kappa)+O(\kappa^{-1}S^{-S/2})+o_\kappa(1)\right].
\]
Here the arbitrary log savings also absorb mesh and progression errors; the replacement \(\log m\) by \(L+O(1)\) is valid by the same smooth breakup and absolute harmonic majorant. Choose \(\kappa\) so small that the displayed fixed fundamental-lemma error is \(<\kappa^2/2\), and then take \(x\) sufficiently large. Equations (5) and the actual source mass give (4).

## 3. A strict negative signed block on the same physical source

In (3) also consider the physical reflected integers \(m\) carrying both a genuine marked prime \(p\) and a genuine marked prime \(e\) with
\[
 x^{.5-.9\kappa}<p<x^{.5-.8\kappa},\qquad
 x^{1.1\kappa}<e<x^{1.2\kappa},\qquad p e\mid m .
\tag{6}
\]
On this entire subfamily the score is \(\le-c_\kappa<0\), where \(c_\kappa\) depends only on the fixed roughness. The primes are distinct, and \(m\) has at least three factors since \(p e<x\). Let \(\vartheta=\log p/\log m\), \(\delta=.5-\vartheta\). Then \(.79\kappa<\delta<.91\kappa\) for all sufficiently large \(x\); every other prime divisor of \(m\) has exponent \(>.95\kappa>\delta\). Thus among short divisors of \(m\) containing \(p\), only \(p\) occurs. All proper divisors of \(m/p\) are short, whereas \(m/p\) itself is not. The exact half sum for even rank therefore is
\[
 H_f(m)=\sum_{d\mid m/p}\mu(d) f(\log d/\log m)-2f(\vartheta).
\tag{7}
\]
The first is a nonpositive full odd difference of order at least 3 (the cofactor has odd rank), and the second is strictly negative of size \(\gg\kappa\). On odd rank the preceding full odd-difference identity gives strict uniform negativity: each \(t_i>.95\kappa\), a derivative lower is given by the single known positive coefficient \(c_{(r-1)/2}\), and \(r\) ranges over a fixed finite set. Formula (7) pays all higher ranks, not only a hypothesized plentiful rank-three or rank-four piece.

To prove genuine lower occupancy of (6) on the entire indicated source, apply the same Fouvry transfer and use the lower sieve for the actual roughness of \(m\), at level \(x^{.004}\). All moduli \(p e w\le x^{.504+.4\kappa}\) fit the strict margin to \(.505\) if \(\kappa\) is chosen sufficiently small. The factors \(p,e\) are each above \(z\) and are in disjoint bands, while \(w\) is \(z\)-smooth, so collected coefficients are bounded and no uncontrolled Q1 weight appears on the short prime. Nonunit coincidences with \(nN\) are excluded in the true coprime principal; they are negligible in the harmonic masses of the markers because those primes are polynomially large, and there are \(O_\kappa(1)\) such potential overlaps. The uniform lower model gives, weighted by \(W_s(q)\), at least a fixed positive fraction of
\[
 A_1(N)V_N(z)
   \left(\int_{.5-.9\kappa}^{.5-.8\kappa}\frac{dt}t\right)
   \log(12/11).
\]
All actual repeated prime squares of \(m\) are negligible at this scale by roughness as above. An individual physical \(m\) may be counted at most \(O_\kappa(1)\) times by the marks, so forgetting them gives a positive constant times \(\mathfrak S(N)x/L^2\). By (7) and its odd counterpart, the indicated negative part of (3) has magnitude at least a fixed positive multiple of \(M_N\). This is a lower occupancy on genuine Q1 with actual reflected composites, not a lower count of *prime* \(m\) on that family's triple-prime long cofactor.

## 4. The original signed debit remains

The original reflected \(C\)-row on genuine \(\mathcal Q_1\) is, by [FullScaleConvolutionBV.md](FullScaleConvolutionBV.md), the actual \(\sum W_s(q)\Lambda(m)-(I_1+o(1))M_N\). Indeed the cutoff and square-root log margins there apply independently of the genuine short factor \(a\), and the same mask freezing argument above handles the marked source. Proper prime powers of \(m\) have negligible weight, and every true prime has \(H_f(m)=1\) and survives the roughness filter. Consequently the signed C-row equals
\[
 \mathcal H(N)-I_1 M_N
    -\!\!\sum_{\substack{\mathcal Q_1, m\text{ squarefree composite}\\P^-(m)>z}}
                  W_s(q)\log m H_f(m)+o(M_N).
\]
In particular the proved negative composite block is *added* when passing back to the original C-row, not a favorable Goldbach reserve in that row. Neither the full positive estimate (4) nor the explicit negative occupancy evaluates this remaining signed composite sum: other even ranks can pay the positive mass, and the full odd negative compensation has no useful small upper. The theorem also supplies no extension to \(\mathcal Q_2\), whose only known independent short prime is \(s>x^{.10}\), outside the required Fouvry exponent for this joint level.
