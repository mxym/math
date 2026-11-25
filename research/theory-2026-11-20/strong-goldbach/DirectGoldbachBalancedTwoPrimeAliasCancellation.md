# Small signed aliases in balanced two-prime delta moduli

This extends the [actual small-alias cancellation](DirectGoldbachPrimeModulusSmallAliasCancellation.md) to a family of composite moduli made from **two polynomial-sized prime factors**. Neither factor is merely a polylogarithmic cofactor. The target \(N\) stays fixed throughout. The theorem does not pay the \(k=0\) target atom or any large aliases.

Let \(X=N\) even, \(L=\log X,\ Q=X^{1-\delta}\) with fixed \(0<\delta<1/4\). Use the smooth interior prime weights \(w,g\) of the prior note, with \(g=1\) near the reflected support of \(w\). Take moduli \(q=rs\) with distinct genuine primes \(r,s\) in bands of lengths comparable to \(R,S\), where \(RS\asymp Q'\), \(Q/L^{C_0}\ll Q'\ll Q\), and
\[
 X^\epsilon\le R,S\le X^{1/2-\epsilon}
\]
for fixed \(\epsilon>0\) (any nonempty configuration with these inequalities is allowed). Use smooth fixed-ratio windows or literal interval cutoffs, and count each modulus once, using \(r<s\) if necessary. One may also impose the original top cutoff and multiply by its smooth constant-kernel factor. After the usual deletion of input characters of conductor \(\le R_0=Q/L^{K_0}\), with \(K_0\) sufficiently large relative to \(C_0\), the actual sum of all nonzero small aliases \(0<|k|\le L^D\) on this block is
\[
 \ll_{D,C_0,\epsilon,\delta,w,g}
 \frac{X}{L^2}\frac{Q'}{Q}(\log\log(3N))^{O(1)}
       +O_A\!\left(\frac{XQ'}{Q}L^{-A}\right) = o(X)
 \quad(A>0).
 \tag{1}
\]
In particular a fixed log-power number of boxes with an overlapping bounded cover and geometric summation in \(Q'/Q\) can be treated; alternatively the estimate is directly \(o(X)\) for the union of the disjoint dyadic boxes in the stated exponent range, of which there are only \(O(L)\) per product scale. The formula is for the high-input block **before** product-conductor or other pair masks.

## 1. The exact high-input centering

For \(v=w,g\), write \(\Theta_v(a;q)\) for the true weighted prime count in the unit residue \(a\bmod q\), and \(\Theta_v\) for its total. Both \(r,s<R_0<rs\) on the stated bands for large \(X\). CRT and the primitivity of nonprincipal characters modulo a prime imply that precisely the characters nonprincipal in **both** variables survive. The projected residue vector is exactly
\[
 E_v(a;q)=\Theta_v(a;q)-\frac{\Theta_v(a;r)}{s-1}
                         -\frac{\Theta_v(a;s)}{r-1}
                         +\frac{\Theta_v}{(r-1)(s-1)} .
\]
Pushing it to any proper divisor \(1,r,s\) gives the zero vector. Thus expanding the actual Ramanujan coefficient \(c_q(N-a-b)\) by \( \sum_{d\mid q,\ d\mid N-a-b}\mu(q/d)d\) leaves only \(d=q\). The multiplier of the resulting congruence form is \(c_Q C_{q/Q}/Q\), with the constant physical kernel of the [top delta identity](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/LargeConductorDeltaSectors.md). The congruence in that form groups literal sums \(N+krs\).

As in the previous note, represent each centered unit class by a genuine prime sequence minus a smooth unit-lattice sequence. Give the lattice on class \(a\bmod q\) density
\[
 \rho_{v,q}(a)
 =\frac{q}{X\int v}
  \left(\frac{\Theta_v(a;r)}{s-1}
       +\frac{\Theta_v(a;s)}{r-1}
       -\frac{\Theta_v}{(r-1)(s-1)}\right).
\]
Poisson gives \(X\int v/q+O_M((X/q)(q/X)^M)\) lattice mass in that class, so this realizes the exact centered vector to arbitrary power accuracy. Both the original and lattice vectors vanish in nonunit classes. The densities \(\rho_{v,q}\) are \(O(L^{O(1)})\) by trivial prime-log counts in any residue (they need not be nonnegative). Define \(E(t)\) to be the maximum reduced-residue error for the two smooth true-prime projections modulo \(t\). Then uniformly in the unit class the difference between \(\rho_{v,q}(a)\) and \(q/\varphi(q)\) is
\[
 O\!\left(r E(r)/X+s E(s)/X+L^{-A}\right).
\]
Indeed the two residue means and the total mean have exactly the principal coefficients that combine into \(q/\varphi(q)\). Replacing the variable density by this common value in any one centered alias costs this error times \(O(XL^{O(1)})\), using the total mass of the other factor or the pointwise bound of its smooth density. Summing over \(r,s\) with the \(1/Q\) multiplier costs at most
\[
 \ll \frac{RS}{Q}L^{O(1)}
       \left(\sum_{r\asymp R}E(r)+\sum_{s\asymp S}E(s)+XL^{-A}\right).
\]
Ordinary maximal Bombieri–Vinogradov at the true long-prime scale \(X\) pays this to arbitrary log precision, including the sum over the fixed log-power number of small aliases after increasing the exponent. All required moduli are the individual \(r,s\), not their large product. For the constant lattice replacement, omitting indices divisible by \(r\) or \(s\) changes each actual mixed or lattice convolution by \(O((X/r+X/s+1)L^{O(1)})\); this is power-small relative to \(X\). Thus each nonzero small alias has mixed-minus-lattice net main \(-X\int w\) just as in the single-prime case, while retaining the actual prime–prime term for evaluation.

## 2. Actual prime pairs opposite a product of two primes

Introduce the short polynomial on the literal products \(rs\), with coefficients \((\log r)(\log s)\) and the stated windows. The same three-input argument of the previous note applies with short length \(Q'\), yielding the weighted average of the genuine \(R(N+krs)\) main \(X\mathfrak S_k(N)\int w\) times the expected weighted number of such products, with error \(O_A(XQ'L^{-A})\) before normalization. Here is the change to each part of that proof.

For the short minor bound, first consider independently bounded separable coefficients on the two prime bands (including their log weights), and allow a smooth product weight or a literal product window; in the expanded square these impose interval cuts or weights in the free variable with uniformly bounded variation. Cauchy in the \(r\)-sum, with this variable afterward allowed to range over all integers, gives squared bound
\[
 \ll Q' L^{O(1)}\sum_{|h|\ll S}\min(R,\|h\alpha\|^{-1})
 \ll (Q')^2 L^{O(1)}(1/R+1/S+1/d+d/Q')
\]
when \(|\alpha-a/d|\le d^{-2}\), \((a,d)=1\). For the spacing bound, break \(h\) into blocks of length at most \(d/2\); different points in a block are spaced \(\gg1/d\) by comparison with \(ha/d\), and their truncated inverse-distance total is \(O(R+d\log(2d))\). The term at zero is included. If needed \(r<s\) is one further interval cut in the free variable. Thus the genuine short product polynomial has arbitrary log saving on the same small-denominator minor complement at scale \(Q'\). Its preimage under \(-k\) has log-power denominator bounds for \(0<|k|\le L^D\); the long-prime collars are handled by Mikawa's short-interval mean square as before because \(Q'\) differs from \(Q\) by only a fixed log power. The restriction \(r\ne s\) deletes at most \(O(\sqrt{Q'}L^2)\) total short weight.

On the long majors, the two actual short prime indices are independently equidistributed among units by Siegel–Walfisz with arbitrary log savings; smooth product weights and order endpoints are handled by partial summation on the literal intervals (for each fixed outer variable first apply it to the inner interval with its true endpoint, and then apply it to the other variable). Products of two independent uniform unit classes are uniform on units. Thus the reduced denominator \(d/(d,k)\) contributes exactly the same \(\mu(d/(d,k))/\varphi(d/(d,k))\) as the single short prime in the previous argument, and consequently the same \(\mathfrak S_k(N)\). In the archimedean integral the displacement \(krs/X=o(1)\) leaves \(g\) identically one on the reflected support; the long integral is exactly \(X\int w\) against the short window mass. All asymptotic errors are uniform in \(|k|\le L^D\). Removing the two prime logarithms in the short inputs uses separate factors \(L/\log r,L/\log s\) with uniformly bounded variations; alternatively apply the same proof with those factors present. The literal unweighted moduli then have total \(O(Q'/L^2)\).

Finally subtract the mixed/lattice main from Section 1. The surviving main is proportional to \(\mathfrak S_k(N)-1\) with coefficient independent of \(k\); the preceding note's actual Euler-product floor estimate sums this over both parities and both signs of \(k\) with \((\log\log(3N))^{O(1)}\) loss, not a loss proportional to the number of aliases. Normalize by \(1/Q\). This proves (1); the factor \(Q'/Q\) also permits geometric summation over product scales. The model contribution may be positive or negative in individual aliases. No summand at the actual target was bounded by shifting it to one of those aliases.
