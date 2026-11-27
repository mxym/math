# Arbitrarily deep pure prime-power congruences for Erdős–Straus

Research note, 27 November 2026. We study explicit refinements of the six residual unit-square classes modulo \(840\), not the full conjecture.

The [Elsholtz–Tao classification, Proposition 1.9](https://arxiv.org/html/1107.1010) gives seven standard congruence families with polynomial decompositions of \(4/n\), four Type I and three Type II. A **pure \(q\)-power level \(i\)** below means one of these displayed canonical congruences whose literal modulus divides \(4q^i\); the modulus of a simultaneous pair of conditions is their least common multiple. This is not a claim about identities of modulus involving other primes or about all decompositions of an individual \(n\).

**Theorem 1 (exact depth on a residue ray).** Let \(\ell\equiv3\pmod4\) and \(q\equiv1\pmod4\) be primes with \(q>\ell^2\). Put, with an empty minimum equal to \(+\infty\),
\[
 e=\min\{r\ge1:4q^r\equiv-1\pmod\ell\},\qquad
 m=\min\{r\ge1:q^r\equiv-1\pmod\ell\}.
\]
If \(e<\infty\) then \(e\) is odd, and set \(j=(e+1)/2\) (otherwise set \(j=\infty\)). On the compatible residue ray \(n\equiv-\ell\pmod{4q^i}\), the first pure \(q\)-power level that occurs in the first Type I family is exactly \(j\). In fact the first level among the seven displayed canonical families is \(\min(j,m)\). When finite, the Type I level \(j\) and the Type II level \(m\) both have explicit decompositions with three distinct positive denominators.

The depths are unbounded: take \(q\equiv-4\pmod\ell\), still \(q\equiv1\pmod4\), for which the two depths coincide and tend to infinity along a sequence of choices of \(\ell\). Every resulting class refines all six residual classes modulo \(840\) independently when \(q>7\). For a finite pre-existing sieve whose moduli avoid \(q\), every one of its surviving reduced classes in those six classes gets a solved refinement by CRT.

There is also a quantitative statement for the first Type I layer.

**Theorem 2 (first-layer residual fraction).** For each prime \(q>7,\ q\equiv1\pmod4\), mark the unit residues \(-f\bmod q\) for divisors \(f\equiv3\pmod4\) of \(4q+1\). In any fixed one of the six residual classes modulo \(840\), the relative density among primes left unmarked for every \(q\le B\) is
\[
   \exp\bigl(-\kappa\log B+O((\log\log B)^2)\bigr),
   \qquad \kappa=\frac{\zeta(2)\zeta(3)}{12\zeta(6)}.
   \tag{1}
\]
It multiplies the residual fraction of any simultaneously imposed independent sieve using only odd primes \(q\equiv3\pmod4\) outside \(840\), by CRT for each fixed cutoff. The density is taken in the input prime variable first, at each fixed \(B\), not with \(B\) freely growing at that input scale.

The individual congruence formulas are classical: see also [Bloom–Elsholtz, *Egyptian fractions*, Theorem 1](https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf) and [Salez’s seven modular equations](https://arxiv.org/html/1406.6307). The contributions here are the sharp depth comparison inside a prime-power tower and the exact first Type I residual exponent. A recent general exceptional-set bound, [Dmytro Trybushnyi, arXiv:2611.14167](https://arxiv.org/abs/2611.14167), is a different result using a broader sieve; we do not improve its exponent. The [2025 range verification](https://arxiv.org/abs/2509.00128) is also not extended.

## 1. The explicit decompositions

In the first Type I family, fix \(c,d,f,k\ge1\) with \(fk=4c^2d+1\) and require \(n\equiv-f\pmod{4cd}\). For \(n>0\) in this class set
\[
 a=(n+f)/(4cd),\qquad b=ak-c .
\]
Indeed \(ak>c\) from \(ak=(n+f)(4c^2d+1)/(4cdf)\), so \(b>0\). Since \(b+c=ak\),
\[
 4abcd=a+(b+c)n ,
 \qquad
 \frac4n=\frac1{acd}+\frac1{abd}+\frac1{bcdn}.
 \tag{2}
\]
For \(e=2j-1<\infty\), take \(c=q^{j-1}, d=q, f=\ell, k=(4q^{2j-1}+1)/\ell\). The parity assertion follows because \(-1/4\) is a quadratic nonresidue modulo \(\ell\), so an exponent giving it cannot be even. Here \(k/c>4q^j/\ell>2\), so \(b>c\). Also \(a<n\) because \(n+\ell<4q^j n\), and therefore \(acd<abd<bcdn\).

In the first Type II family, if \(q^m\equiv-1\pmod\ell\), take \(u=1,\ v=q^m,\ c=(u+v)/\ell,\ d=(n+\ell)/(4uv)\). Then \(4uvcd=u+v+cn\), and the denominators are
\[
                       uvd,\quad ucdn,\quad vcdn .
\]
Here \(v>1\) and \(n\ge4v-\ell>v\) on the positive ray, so \(uvd<ucdn<vcdn\). On prime inputs sufficiently large in the fixed progressions, (2) is genuinely Type I and this second decomposition genuinely Type II: in each case the denominators not carrying the explicit factor \(n\) are coprime to \(n\). For instance in (2), \(a\equiv f/(4cd)\) and \(b\equiv1/(4cd)\pmod n\) for primes avoiding the fixed constants.

## 2. Exact lower-level exclusions

Fix \(i\ge1\) and consider the required class \(-\ell\bmod4q^i\). A family of exact modulus \(4q^i\) covers it only if its residue is \(-\ell\bmod4q^i\). A family at a divisor of that modulus addresses the same test at an earlier level.

**First Type I family.** Its parameters have \(cd=q^i\), say \(c=q^h,\ d=q^{i-h}\) with \(0\le h\le i\). Thus \(f\mid L:=4q^{i+h}+1\) and \(f\equiv\ell\pmod{4q^i}\). If \(h=i\), then \(L=(2q^i)^2+1\), which has no prime divisor \(3\bmod4\); this prevents \(f\equiv\ell\equiv3\bmod4\). Otherwise \(h\le i-1\). If \(f<4q^i\), it must equal \(\ell\). If \(f\ge4q^i\), the cofactor \(k=L/f\) is smaller than \(4q^i\), so it is the least positive inverse of \(\ell\) modulo \(4q^i\). Write
\[
             \ell k=1+s(4q^i),\qquad 1\le s\le\ell-1.
\]
The equation \(k\mid L\) gives \(k\mid s-q^h\) by subtracting \(q^h(\ell k)\) from \(sL\). But \(k>(4q^i)/\ell\) is strictly larger than both \(q^h\) and \(s\), using \(q>\ell^2\), so \(q^h=s\). The only possibility is \(h=0,s=1\), and now \(\ell k=4q^i+1=L\), which again implies \(\ell\mid L\). Therefore **any** hit at this level requires \(\ell\mid4q^{i+h}+1\) for some exponent \(i+h\le2i-1\). This rules out \(i<j\), or every level if \(e=\infty\). It proves the exact depth of this family by (2).

**First Type II family.** At modulus \(4q^i\), the parameters \(u,v\) have \(uv=q^i\), the witness \(g\mid u+v\) with \(\gcd(g,4uv)=1\), and the residue is \(-g\). As \(g\le q^i+1<4q^i\), one must have \(g=\ell\). After removing the lesser power of \(q\) in \(u+v\), this requires \(q^r\equiv-1\pmod\ell\) for some \(0\le r\le i\). So \(i\ge m\), and the construction in §1 attains it.

**The other five displayed families contribute no earlier levels; in fact none hit this ray with a literal modulus dividing \(4q^i\) at any level.** In the second and third Type I displays of Proposition 1.9, the additional modulus \(f\) is coprime to the \(4\)-multiple in the first condition. If their combined period divides \(4q^i\), then \(f\) is a power of \(q\) and thus \(f\equiv1\pmod4\). The first condition \(n\equiv-f\pmod4\) is incompatible with \(n\equiv-\ell\equiv1\pmod4\). The third Type II display is similarly incompatible modulo \(4\), since its coprime parameter \(g\) is a power of \(q\) and its residue is \(-4u^2d-g\). The second Type II display requires its odd modulus \(f\equiv3\pmod4\) from \(4ud\mid f+1\); no such divisor of \(4q^i\) exists.

It remains to check the fourth Type I display: \(n\equiv-g^{-1}\pmod{4uv}\) with \(g\mid u+v,\ \gcd(g,4uv)=1\). At level \(uv=q^i\), the required hit would imply \(\ell g\equiv1\pmod{4q^i}\) and hence \(g\ge(4q^i+1)/\ell\). If the exponents of \(q\) in \(u,v\) are both positive, then \(g\le q^{i-2}+1\) after removing the lesser power of \(q\), a contradiction. Otherwise \(g\mid q^i+1\); still \(g\le q^i+1<4q^i\). Write \(\ell g=1+s(4q^i)\) with \(1\le s\le\ell-1\). As \(q^i\equiv-1\pmod g\), one has \(g\mid4s-1\), which is impossible since \(0<4s-1<4\ell<g\). Level \(i=0\) is immediate in the seven displays: its modulus divides \(4\), and any permitted unit residue is \(3\bmod4\). This completes the exact comparison.

## 3. Arbitrarily deep examples and the six Mordell classes

Choose \(q\equiv-4\pmod\ell\) and \(q\equiv1\pmod4\). Dirichlet’s theorem gives arbitrarily large prime \(q\) for each fixed \(\ell\). The order \(t=\operatorname{ord}_\ell(-4)\) is even because \(-4\) is a nonresidue and \(\ell\equiv3\pmod4\). Here \(e=t-1,\ m=t/2,\ j=t/2\). For each fixed \(D\), only finitely many primes \(\ell\) can have order \(\le D\): they divide at least one of the nonzero integers \((-4)^r-1\), \(1\le r\le D\). As there are infinitely many primes \(3\bmod4\), these exact depths are unbounded.

For a smaller example, \(q=409,\ \ell=11\) gives \(e=3\) and \(m=5\), so depth exactly 2. The new class is \(n\equiv669113\pmod{669124}\), with \(c=d=409,\ f=11,\ k=24879247\) in (2). Intersecting with the six Mordell classes gives the following residues modulo \(140516040\):
   
| \(n\bmod840\) | refined residue |
|---:|---:|
| 1 | 22081081 |
| 121 | 102375961 |
| 169 | 50184289 |
| 289 | 130479169 |
| 361 | 122449681 |
| 529 | 10036849 |

All are reduced classes. For a pre-existing finite list of moduli one can always choose the auxiliary \(q\) outside its prime divisors. As the six classes are all \(1\bmod4\), the new constraint is just \(n\equiv-\ell\pmod{q^j}\) within each old reduced survivor progression. CRT gives a reduced refinement and Dirichlet’s theorem supplies infinitely many primes there. This shows a genuine strict refinement over any fixed finite sieve in that sense, not that any particular prime failed every known identity, and not that any entire Mordell class is now solved.

## 4. The first Type I layer and its residual density

At level \(4q\) in the first Type I family, \(cd=q\). The choice \(c=q\) gives \(4q^2+1\), a sum of two squares which has no divisors \(3\bmod4\). Thus exactly the \(c=1,d=q\) choice matters on input classes \(1\bmod4\). Let
\[
                     r(q)=\#\{f\mid4q+1:\ f\equiv3\pmod4\}.
\]
These \(f\) give distinct nonzero forbidden residues \(-f\bmod q\): they are coprime to \(q\), and equality modulo \(q\) together with equality modulo 4 would force difference at least \(4q\), whereas all lie in \([3,4q+1]\). Moreover they are all nonresidues modulo \(q\) when \(q\equiv1\pmod4\), by Jacobi reciprocity:
\[
         \left(\frac{-f}{q}\right)=\left(\frac{q}{f}\right)
                         =\left(\frac{-1}{f}\right)=-1,
\]
since \(4q\equiv-1\pmod f\). Thus \(r(q)\le(q-1)/2\). CRT and prime equidistribution for the fixed product modulus give the exact relative survivor fraction
\[
    \prod_{\substack{7<q\le B\\ q\ {\rm prime},\ q\equiv1\ (4)}}
                   \left(1-\frac{r(q)}{q-1}\right).
 \tag{3}
\]

We evaluate its logarithm. Put
\[
 P_o=\prod_{p>2}\left(1+\frac{1}{p(p-1)}\right).
\]
The elementary identity \(n/\varphi(n)=\sum_{d\mid n}\mu^2(d)/\varphi(d)\) gives
\[
 \sum_{\substack{f\le Y\\ f\equiv3\ (4)}}\frac1{\varphi(4f)}
              =\frac{P_o}{8}\log Y+O(1).
 \tag{4}
\]
For details, the untwisted odd sum \(\sum_{n\le Y,\ n\ {\rm odd}}1/\varphi(n)\) has coefficient \(P_o/2\): expand the identity and use the odd harmonic sum \(\frac12\log x+O(1)\), with convergence of \(\sum_{d\ {\rm odd}}\mu^2(d)(1+\log d)/(d\varphi(d))\). The corresponding twisted sum with the character modulo 4 is bounded, since \(\sum_{m\le x}\chi_4(m)/m\) is bounded and \(\sum_d\mu^2(d)/(d\varphi(d))\) converges. Take half their difference to restrict to \(3\bmod4\), and divide by 2 since \(\varphi(4f)=2\varphi(f)\) for odd \(f\). This proves (4).

For a dyadic window \(X<q\le2X\), the divisors counted by \(r(q)\) are paired by \(f\mapsto(4q+1)/f\), preserving \(f\equiv3\bmod4\). There is no square case for odd prime \(q\): \(4q+1=(2v+1)^2\) would give \(q=v(v+1)\). Hence \(r(q)\) is twice the count of those \(f<\sqrt{4q+1}\). Take \(Y=\sqrt X/(\log X)^A\) for a sufficiently large fixed \(A\). For \(f\le Y\), the conditions \(q\equiv1\bmod4,\ 4q\equiv-1\bmod f\) form one reduced class modulo \(4f\). The Bombieri–Vinogradov theorem, summed over these moduli, supplies the main term
\[
   2(\operatorname{Li}(2X)-\operatorname{Li}(X))
                \sum_{f\le Y,\ f\equiv3\ (4)}1/\varphi(4f)
\]
with error \(O(X/(\log X)^2)\), by taking \(A\) large enough. For \(Y<f\le\sqrt{8X+1}\), Brun–Titchmarsh bounds the tail by \(O((X/\log X)\sum_f1/\varphi(4f))=O(X\log\log X/\log X)\) by (4). The moduli there are \(O(\sqrt X)\), so the denominator in the Brun–Titchmarsh bound is comparable to \(\log X\). Thus
\[
 \sum_{\substack{X<q\le2X\\q\ {\rm prime},\ q\equiv1\ (4)}}r(q)
 =\frac{P_o}{8}X+O\bigl(X\log\log X/\log X\bigr).
\]
Summing dyadically and then using partial summation yields
\[
       \sum_{\substack{q\le B\\q\ {\rm prime},\ q\equiv1\ (4)}}\frac{r(q)}{q-1}
          =\frac{P_o}{8}\log B+O((\log\log B)^2).
\]
The replacement of \(q\) by \(q-1\) costs \(O(1)\) since \(r(q)\le\tau(4q+1)\ll_\epsilon q^\epsilon\). The same divisor bound shows that the sum of squares of \(r(q)/(q-1)\) converges, so the error in taking logarithms in (3) is bounded. Finally \(P_o=(2/3)\zeta(2)\zeta(3)/\zeta(6)\) by the Euler product. This proves (1).

## Verification boundary

[verify_erdos_straus_prime_power_coverage.js](verify_erdos_straus_prime_power_coverage.js) replays exact arithmetic for the first Type I/II depth formulas, the relevant other families, positivity and distinctness of denominators, the six CRT refinements, and local distinctness of the residues in (3). These finite checks are not a Lean kernel run and do not replace the prime number theorems in §4. The exact-depth statement concerns only the specified classical congruences with the specified literal moduli; it is deliberately not a lower bound on the complexity of all possible solutions.
