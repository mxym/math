# A largest-prime descent for the actual weighted Vaughan residue

Use the matched signed sequence \(c_N^W\) of [FlexibleMarkedCarrierFiveEighths.md](FlexibleMarkedCarrierFiveEighths.md), supported on \(J=N-I\), \(I=(x/2,x]\), \(x=N/2\). This note uses only its maximal Type I estimate (11) to \(Q=x^{5/8-\eta}\), \(0<\eta<.006\), and its pointwise log-power bound. Nothing presumes that \(m=N-n\) is rough. The resulting exact residual has a genuine largest-prime restriction on its signed Möbius factor, and a second complementary log-divisor restriction. It is not a bound for the residual.

## 1. Weighted use of the established Type I error

Write \(U_V=V=x^{.300}\), \(L=\log x\), and \(E(r)=\sup_t|\sum_{m\le t,r\mid m}c_N^W(m)|\). Before the reduction below, the only Vaughan term left is precisely
\[
 \mathcal T=\sum_{\substack{d>U_V,\ l>V,\ h\ge1\\m=d l h\in J}}
                  \mu(d)\Lambda(l)c_N^W(m).
 \tag{1}
\]
Indeed the first logarithmic residue and the third convolution in the usual Vaughan identity are absorbed by Type I, since \(U_V V=x^{.600}<Q\); the isolated \(\Lambda_{\le V}\) term vanishes on \(J\). This is the exact pre-alternation \(k=l h\) quotient expression, so both actual signs and the actual von Mangoldt summand are retained.

For every fixed integer \(j\), (11) also gives
\[
                 \sum_{r\le Q}\tau_j(r) E(r)\ll_B x L^{-B}.
 \tag{2}
\]
Cauchy bounds its square by \((\sum E(r))(\sum \tau_j(r)^2 E(r))\). Since \(c_N^W\ll L^C\), the second sum is at most \(L^C\sum_{r\le Q}\tau_j(r)^2(x/r+1)\ll_j x L^{C_j}\), using \(Q<x\) and the standard divisor moment. The first factor has arbitrary log reserve, proving (2). Intervals in a progression variable cost at most two prefixes; a factor \(\log z\) on the remaining free integer \(z\ll x\) uses partial summation at cost \(O(L)\). These are the only extensions of Type I needed.

## 2. Two exact subtractions on the original quotient sum

Let \(\mu_2=\mu*\mu\). For fixed \(k=l h\) define
\[
 a(d;k)=-\sum_{\substack{c\mid d\\ck\le Q}}\mu_2(c),\qquad
 b(d;k)=\mu(d)-a(d;k)=2\mu(d)-\!\!\sum_{\substack{c\mid d\\ck>Q}}\mu_2(c).
 \tag{3}
\]
The last identity follows from \(\mu_2*1=\mu\); there is no squarefreeness restriction. If \(k>Q\), the first sum is empty. For the other side define
\[
 a'(l;d,h)=\sum_{\substack{e\mid l\\e d h\le Q}}\mu(e)\log(l/e),\qquad
 b'(l;d,h)=\Lambda(l)-a'(l;d,h)
          =\sum_{\substack{e\mid l\\e d h>Q}}\mu(e)\log(l/e).
 \tag{4}
\]
The equality uses \(\mu*\log=\Lambda\). Define the cutoff \(H(m)=m/Q\); the notation \(H\) here is not the physical free-factor length of the earlier .09 notch.

Replacing the coefficients in (1) is legitimate in **both** slots:
\[
 \mathcal T=
 \sum_{\substack{d>U_V,\ l>V,\ h\ge1\\m=d l h\in J}}
              b(d;l h)b'(l;d,h)c_N^W(m)+O_B(x L^{-B}).
 \tag{5}
\]
To check this identity with its error, expand \(b b'=(\mu-a)(\Lambda-a')\). Each of the following three terms is Type I at modulus \(\le Q\).

* In \(a(d;l h)\Lambda(l)\) write \(d=c z\). The modulus \(r=c l h\le Q\) is independent of the free \(z\), with \(d>U_V\) an interval condition. The absolute coefficient sum at fixed \(r\) is at most \(L\tau_4(r)\): sum over \(c,l,h\), \(|\mu_2(c)|\le\tau_2(c)\), \(\Lambda(l)\le L+O(1)\).
* In \(\mu(d)a'(l;d,h)\) write \(l=e z'\). The modulus \(r=e d h\le Q\) leaves \(z'\) free with only the prefix/interval and \(\log z'\). The absolute sum of the auxiliary coefficients at fixed \(r\) is \(\le\tau_3(r)\).
* In the cross term write \(d=c z,l=e z'\). Retain the exact modulus \(r=e h c z\le Q\) from \(a'\). The other condition is \(c e h z'\le Q\), an upper interval cutoff on the free \(z'\); \(e z'>V\) is its lower cutoff. All fixed coefficients over \(e,h,c,z\) at modulus \(r\) are at most \(\tau_5(r)\) in absolute sum, allowing \(\tau_2(c)\) for \(\mu_2(c)\). The same \(\log z'\) partial summation applies. This checks the cross despite the original two variable-dependent cutoffs.

Use (2) in all three cases. Arbitrary dyadic factor windows on the original, independently named \(d,l,h\) can also be retained, since they remain interval cuts or fixed factors after each unfolding. No estimate for an arbitrary quotient-weighted residue class is used.

## 3. Actual support properties and the squareful scope

Every nonzero \(b(d;k)\) in (5) satisfies \(P^+(d)\le H(m)\). In fact \(k=l h> x^{.300}\), \(m=d k\asymp x\), so
\[
           (Q/k)^2/d=Q^2/(km)\ll x^{-.050-2\eta}.
\]
If \(P\mid d\) is prime with \(P>H(m)=dk/Q=d/(Q/k)\), then \(t=d/P<Q/k<P\); in particular \(P\) occurs once. The divisors \(c\mid d,\ c\le Q/k\) are then precisely all divisors of \(t\) (every one allowed). So \(a(d;k)=-\sum_{c\mid t}\mu_2(c)=-\mu(t)=\mu(d)\), even for squareful \(t\), giving \(b=0\). When \(k>Q\) the condition \(P>H(m)\) is impossible because \(H(m)>d\). Thus the support reduction is exact, and throughout \(P^+(d)\ll x^{3/8+\eta}\). It does not exclude squareful \(d\) on this smooth support.

A more detailed parity statement is confined to a real subfamily. For \(k\le Q\), put \(U=Q/k\) and let \(t\) be the *full* part of \(d\) supported on prime bases \(\le U\), with multiplicities. If \(t\le U\), then \(a=-\mu(t)\) exactly. For factorization \(d=t P_1\cdots P_j\) with every \(P_i>U\) and all distinct, \(b=\mu(t)(1+(-1)^j)\), also zero if \(t\) is squareful. If any of the large factors is repeated, \(\mu(d)=0\) but \(b=\mu(t)\), which is not necessarily zero. When \(t>U\), the formula using the full \(\mu(t)\) is not valid; keep (3). No statement that the original shifted sequence has few small prime factors is made.

For example on the upper block \(d>x^{.600}\), \(k\ll x^{.400}\), write instead the fixed truncation \(U_0=x^{.218}\) in (3). Its whole \(a_{U_0}\) part in (1) is still negligible because \(U_0 k\ll x^{.618}<Q\), and the coefficient estimate at \(r=c k\) is \(L\tau_3(r)\). There are at most three large prime factors counted with multiplicity because \(d\ll x^{.700}\). For squarefree \(d\) with full small part \(t\le U_0\), only \(j=2\) survives (since \(j=0\) would force \(d\le U_0\)); the weight there is \(2\mu(t)\). This particular parity description does **not** apply when a large factor is repeated or the full small part exceeds \(U_0\), and it is not an assertion that those excluded pieces are negligible.

## 4. Exact simplification of the other side

At fixed \(m=d k\), (4) rewrites as
\[
 b'(l;d,k/l)=\sum_{\substack{w\mid l\\w<H(m)}}\mu(l/w)\log w .
 \tag{6}
\]
Consequently, after summing over \(l\mid k,\ l>V\), its effective coefficient for \(k>V\) is precisely
\[
 B_{H,V}(k)=1_{k<H}\log k-\sum_{\substack{e\mid k\\e\le V}}\Lambda(e).
 \tag{7}
\]
For (7), swap \(e'=l/w\) and \(w\). Since \(H(m)>V\) for large \(x\), terms with \(w>V\) sum to \(1_{V<k<H}\log k\) by \(\sum_{e'|k/w}\mu(e')=1_{k=w}\). Terms with \(w\le V\) sum to \(-\sum_{e'w\mid k,\ e'w\le V}\mu(e')\log w\), as the unrestricted Möbius sum vanishes for \(k>w\). The final convolution is \(\Lambda\). The strict \(w<H\) and weak \(e d h\le Q\) boundaries agree even for integer equalities. In particular this second subtraction reproduces the logarithmic/prime-divisor split for the \(k\)-side, but now the Möbius variable has the separately established largest-prime support.

There is an exact local description when \(l\) contains a prime \(P>H\). Write \(l=P t\). Here \(d h>x^{.300}\), hence \((Q/(d h))^2/l=Q^2/(m d h)\ll x^{-.050-2\eta}\), just as on the other side. Thus \(t<Q/(d h)<P\). In (4) only \(e\mid t\) occur, all of them; \(a'=\log P\,1_{t=1}+\Lambda(t)\). It follows that \(b'=0\) on a prime \(l>H\), and \(b'=-\Lambda(t)\) when \(t>1\). This creates signed composite coefficients, not merely an approximation to the original prime sequence; by (7), after collapsing the \(l\)-sum, the entire \(k\ge H\) block keeps its negative small prime-divisor weights. Thus one cannot drop the large-prime sector of \(k\) on grounds of the prime case of \(b'\).


## 5. Squarefree version with a fixed reserve

One may impose squarefreeness of the **whole** \(m\) before beginning Vaughan, not just on \(d\) after subtraction. This changes the original \(\Lambda\)-weighted sum by \(O(x^{1/2}L^C)\), as only prime powers are removed. It does not change the matched reference: this statement multiplies both terms of the already formed \(c_N^W(m)\) by \(\mu^2(m)\), and the prime-log main of that same reference loses at most the same power-small prime-power mass.

Fix \(0<\zeta<.001\), and set \(Q_0=Q/x^\zeta\). For any fixed \(j\) the sequence \(c_N^W(m)\mu^2(m)\) satisfies (2) through \(Q_0\), uniformly in every maximal prefix. Indeed write \(\mu^2(m)=\sum_{e^2\mid m}\mu(e)\) and fix \(0<\gamma<\zeta/2\). For \(e\le x^\gamma\), the combined modulus \(R=\operatorname{lcm}(r,e^2)\le r e^2\le Q\); for each \(R\), both \(r\) and \(e\) divide \(R\). Thus the multiplicity weighted by \(\tau_j(r)\) is bounded by a fixed divisor power of \(R\), to which (2) applies; the same prefix variable can be retained. For \(e>x^\gamma\), each \(m\) counted is \(\ll x\) and divisible by one such \(e^2\), with at most \(O(x\sum_{e>x^\gamma}e^{-2})=O(x^{1-\gamma})\) possible \(m\)'s. The two divisor counts, \(r\mid m\) and \(e^2\mid m\), even with fixed divisor powers, cost \(x^{o(1)}\) pointwise. Together with the bound for \(c_N^W\) this is power small. There is no relative error from an additional small-prime filter.

Now use \(Q_0\) instead of \(Q\) throughout (1)–(7) on this squarefree sequence. The initial \(U_V V=x^{.600}<Q_0\) still holds. In the unfolded low-modulus terms the squarefreeness is already in the prefix sequence; the same exact windows apply. On every surviving term \(m,d,k\) are squarefree, \(d,k\) are coprime, and all \(d,l,h\) are pairwise coprime. The smooth support in §3 becomes \(P^+(d)\le m/Q_0\ll x^{3/8+\eta+\zeta}\). In the parity subfamily \(t\le U=Q_0/k\), the distinct-factor formula now applies literally wherever that inequality holds, with no squareful exception; the unsifted case \(t>U\) still remains. The exact \(B_{H,V}\) formula is unchanged except \(H=m/Q_0\); for this version its divisor log sum simply reads \(\sum_{p\mid k,\ p\le V}\log p\).

## 6. Unresolved core

Determining the sign or any sufficiently small bound of the remaining \(c_N^W(d k)\)-weighted sum, with the exact signed smooth-divisor coefficient \(b(d;k)\) and the remaining \(\beta\) or negative divisor weights in (7), still needs genuine fixed-target Type II input. No cancellation estimate for the squareful part or for this core follows from the support statement. The result concerns the one actual \(K_P\)-weighted carrier, not the full polynomial low residual or binary Goldbach.

[Arneth's October 2026 binary Goldbach candidate architecture](https://zenodo.org/records/23504447) also uses exact divisor and Vaughan identities to isolate an unresolved signed correlation. The present support reduction concerns the stated matched Type I estimate, its adaptive reciprocal cuts, and a genuine smooth Möbius factor in one selected weighted carrier. It does not settle parity separation, claim an advance for a different signed operator, or turn the coefficient signs into a prime-pair lower bound.
