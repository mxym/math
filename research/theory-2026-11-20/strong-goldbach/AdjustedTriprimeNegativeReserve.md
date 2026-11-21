# A uniform negative reserve on the same two adjusted quotient profiles

This note concerns the original whole reflected weight \(C\) and the exact adjusted reverse coefficient \(D_B\) of [AdjustedTriprimePositiveBudget.md](AdjustedTriprimePositiveBudget.md), with \(N=2x\), \(B=x^{.501}\), \(U_q=x^{.070}\), \(V_q=x^{.010}\). The original true \(q\)-prime row has the whole adjusted representation there. No extra reflected \(J\) subtraction is made.

On the true quotient side, let \(\mathcal Q_1\) consist of \(q=a_q P Q\) with distinct genuine primes, \(x^{.010}<a_q<x^{.070}\), \(P,Q<B\), and \(a_qP>B\). The mark \(P\) is unique on the physical central support. Let \(\mathcal Q_2\) instead consist of \(q=P Q R\) with three distinct prime factors \(<x^{.358}\), unordered. These tests are functions of the integer \(q\) and the ambient \(x\) only. The former may additionally have the **same** fixed marked \(P\)-band in both signs, e.g. \(x^{.438}<P<x^{.445}\). The stated positive-budget lower used the full first family; it is not invoked after restricting this band. The latter family has no extra mark. On physical rows \(n=sq\in(x/2,x]\), \(x^{.10}<s<x^{.14}\), \((n,N)=1\), the two families have the exact \(D_B(q)/\log q=1\) and \(2\), respectively. Every prime factor of either \(q\) is \(>x^{.010}\). We do not approximate the factorization or replace \(D_B\) by this value outside the corresponding family.

Use the reflected chamber and \(s\)-band of [ActualNegativeThreeMarkReserve.md](ActualNegativeThreeMarkReserve.md), with \(m=N-sq=p c a b w\), four distinct actual marked primes, \(P^-(w)>x^{.004}\), and
\[
\begin{array}{c|c}
 \text{label}&\text{allowed }\log_x\text{ interval}\\ \hline
 s&[.1009,.1011]\\
 p&[.218-\eta/100,.218+\eta/100]\\
 c&[.282-\eta-\eta/100,.282-\eta+\eta/100]\\
 a&[2\eta,2.1\eta]\\
 b&[2.2\eta,2.3\eta].
\end{array}
\tag{1}
\]
Then for each \(i=1,2\) there exists a fixed \(c_i>0\) such that, for all sufficiently large even \(N\),
\[
 \boxed{
 \sum_{\substack{(s,q)\text{ physical as above}\\q\in\mathcal Q_i\\
             m\text{ has a witness in }(1)}}
      \frac{W_s(q)}{\log q}\, D_B(q)\,C(m)\ \le\ -c_i M_N .
 }
\tag{2}
\]
Choose a common fixed \(\eta>0\) sufficiently small for both families. Each physical row is counted once, not once per eligible marking. The two terms (2) are disjoint, and are disjoint from the **narrow positive** chamber of the cited positive-budget note, since \(p<x^{.25}\) here. This is a fixed-target result in the same adjusted quotient profiles as that note, but on different reflected \(m\). It gives a real negative reserve, not an estimate on the unbounded complement or proof that the reserve pays the positive excess. No numerical size for \(c_i\) is claimed.

## 1. Changed source for the exact lower sieve

Write \(K=p c a b\) and
\[
 \Sigma(x,N)=\!\!\!\sum_{\substack{s,p,c,a,b\text{ as in }(1)\\(sK,N)=1}}
               \frac1{sK},\qquad
 R_N=\frac{\mathfrak S(N)x}{L^2}\Sigma(x,N).
\]
As in the prior proof, \(\Sigma(x,N)\gg \eta^2\) by ordinary prime reciprocal sums, with a uniform constant for all sufficiently small fixed \(\eta\) and large \(x\). We count labelled tuples first.

For every allowed \(s\), the count of actual \(q\in\mathcal Q_i\) with \(x/(2s)<q\le x/s\) is between \(c_i' x/(sL)\) and \(C_i' x/(sL)\), with constants independent of \(\eta\). For the lower bound it suffices to choose the following independent actual prime exponent boxes: \(\log_x a_q\) near \(.0665\) and \(\log_x P\) near \(.441\) for \(i=1\), or two labelled macroprime exponents near \(.297\) and \(.300\) for \(i=2\). Ordinary PNT on the actual remaining prime interval (relative length bounded away from zero) and reciprocal sums over the first prime labels give the required uniform lower. These boxes have strict margin for the physical \(q\)-tests when \(s\) varies through (1), including the optional \(P\)-restriction above. The full upper follows in the same way by dropping final-prime cap constraints when using PNT, since its possible exponents stay uniformly positive and the harmonic ranges of the other prime slots are fixed. Equivalently use the interior and full-upper PNT calculation of the positive-budget note. Repeated bases give a power-small error since the polynomial lower exponents are fixed. For \(i=2\), counting ordered triples and dividing by \(3!\) can only change constants here.

The lower Rosser–Iwaniec sieve of [ActualNegativeThreeMarkReserve.md](ActualNegativeThreeMarkReserve.md), §1, is applied to \(w=(N-sq)/K\) at level \(D=x^{.012}\) and \(z=x^{.004}\), exactly the ratio \(3\). Its modulus is \(K d\) with squarefree \(d\le D\), \((d,N)=1\). For the discrepancy use [Lichtman Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5) in the same actual three modulus slots \((ab d,p,c)\) and the same actual residue \(N\). The **only** short source factor that must satisfy Siegel–Walfisz is the actual prime \(s\). The independent complementary coefficient on \(q\), in its own interval, is the \(1\)-bounded indicator of \(\mathcal Q_i\) and its target-unit mask, not a prime weight with an implicit condition on a factor of \(q\). This is expressly the two-way convolution, with the entire three-prime product in the complementary slot. All strict exponent rails of §1 of the previous proof are unchanged, since the slot scales are still \(s\asymp x^{.101}\), \(q\asymp x/s\). In particular this does not try to insert the small \(a_q\) into the SW slot.

The sharp product window \(x/2<sq\le x\) is handled by the same fine Cartesian boxes on **the labels \(s,q\)**, not on the internal factorization of \(q\). The discarded boundary involves \(O(xL^{-F})\) integers \(n\). A given integer \(n\le x\) has boundedly many eligible \(s\) by the polynomial lower bound on \(s\), and the usual divisor moment bound on \(N-n\) pays the possible modulus/sieve weights. The same principal harmonic boundary estimate is valid with the new \(1\)-bounded \(q\) coefficient. All masks on \(q\) are fixed independently of \(s\) within these boxes, and the sum of errors is \(O_A(xL^{-A})\) for every fixed \(A\). The multiplicity bound for \((ab d,p,c)\) holds as before; a residue with \((Kd,N)>1\) yields no physical term on unit support.

For clarity, the short sieve factor is still exactly
\[
 g_K(\ell)=\frac{\varphi(K)}{\varphi(K\ell)}
       =\begin{cases}1/\ell,&\ell\mid K,\\1/(\ell-1),&\ell\nmid K,\end{cases}
 \qquad \ell<z,\quad \ell\nmid N.
\]
All actual \(s,q\) factors exceed \(z\), so they automatically avoid every prime dividing \(d\) and the tiny \(a,b\). The possible overlap \((q,pc)>1\) in the principal term, relevant in particular in \(\mathcal Q_2\), is negligible uniformly for each \(s,p,c\): the trivial number of multiples is
\[
 O\!\left(\frac{x}{s p}+\frac{x}{s c}+1\right)
      =o\!\left(\frac{x}{sL}\right).
\]
All \(p,c\) exponents have a fixed positive lower bound. The factors \(s,p,c\) are disjoint by size. For target-unit \(q\), the analogous deletion of multiples of any prime factor of \(N\) that can occur in \(q\) costs \(O(x^{.99} L/s+L)\), uniformly, since all actual \(q\)-factors exceed \(x^{.010}\). The \(s\)-mask and \(K\)-mask \((sK,N)=1\) apply as in the prior proof. These errors may be summed over all markings and moduli with the harmonic bounds in that proof; any power saving absorbs their log factors. The moving \(g_K\) satisfies the same uniform dimension-one bound, and the lower sieve product \(\gg\mathfrak S(N)/L\) is unchanged. Thus for each family the lower sieve gives at least \(c_i'' R_N\) labelled physical rows.

## 2. Precisely why the two-neck upper survives

The previous two-form upper at fixed \(s,D_0\) writes the exact free affine forms \(y=y_0+s v\), \(q=(N-D_0y_0)/s-D_0v\) with physical interval length \(Y\gg x^{.038}\). The first form remains \(x^{.004}\)-rough. The second is no longer a prime, but every eligible \(q\in\mathcal Q_i\) has all factors \(>x^{.010}\), hence avoids all primes used by that very upper sieve, whose radius is \(x^{.002}\). No fixing of a prime divisor of \(q\) is needed. The root counts at \(s,N,D_0,2\) are exactly the same because the affine forms and true coprimality masks are unchanged. In particular there is no new short-interval reduction or claimed PNT for the three-prime product in this one-dimensional sieve step. The uniform bound \(\ll_\gamma \mathfrak S(N)x/(sD_0L^2)\) follows word for word from §3 of the prior note.

The one-neck and two-neck harmonic openings of that proof therefore give
\[
 \sum j\ll_\gamma(\eta+1/L)R_N,\qquad
 \sum j(j-1)\ll_\gamma(\eta+1/L)^2R_N
\]
with precisely the same \(\mathcal I_p,\mathcal J_{K,p}\) and largest free choice, and the midpoint seam has labelled count \(o(R_N)\). The squareful deletion works with the same divisor bound because \(m\) and \(s\) determine the integer \(q\); admissible \(q\) is counted as an integer, not with an unbounded multiplicity of decompositions. All resulting upper constants are independent of \(\eta\) for the fixed \(x^{.004}\) roughness cutoff.

## 3. The physical signed sum

Use the exact same squarefree sign calculation from §2 of the previous proof. Outside the negligible seam and squareful sector:
* With no neck divisor, \(C(m)\le-\eta L\) for each parity.
* The one-neck positive part in the odd branch is \(O(\eta L j)\), and the even branch has positive part at most \(O(Lj(j-1))\).

These are statements about the actual original \(C(m)\) and do not involve the source \(q\) being prime. On each \(q\)-family multiply by the **exact positive** adjusted quotient factor \(D_B/\log q=1\) or \(2\), times \(W_s(q)\) which is bounded above and below positively throughout (1). The \(j=0\) lower occupies \(\gg_i R_N\) labelled rows after \(\eta\) is fixed sufficiently small; passing to the physical union loses at most the same bounded marking multiplicity as previously. Thus the genuine negative rows provide at most \(-c_i'''\eta L R_N\). The total possible positive part of this same physical chamber is
\[
 O_\gamma(LR_N[\eta(\eta+1/L)+(\eta+1/L)^2])+o_\eta(LR_N).
\]
Choose \(\eta\) small relative to the two fixed lower constants and then take \(x\) large. This proves (2) since \(LR_N=2\Sigma(x,N)M_N\). The opposite-sign edge \(q=PQ\) from the positive-budget note is not used here. The positive triprime \(m\)-profiles and most of the signed adjusted remainder still are not controlled.

[Arneth’s September preprint](https://zenodo.org/records/23016346) gives a different exact same-target compensation example and a conditional uniform capacity criterion. The bound here is for the two specific quotient profiles and the original marked reflected sign calculation; no uniform net compensation is inferred.
