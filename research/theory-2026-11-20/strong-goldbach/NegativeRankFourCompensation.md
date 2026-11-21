# A negative rank-four compensation in the exact opened row

Use the notation, subpower cutoffs, and actual half coefficient \(C^\dagger=C+P-J\) of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md), with \(\kappa_s=1\), the complete first prime band \(x^{.10}<s<x^{.14}\), and the true \(W_s(q)=K_{P_3}(s q)\). In the **artificial** quotient row \(\mathcal T_{\rm v}(C^\dagger)\), retain the exact coefficient \(C_q^{\rm hi}(q)/\log q\) with \(U_q=x^{.070},V_q=x^{.010},E=x^{.080}\), not a prime indicator. Let \(\mathcal D\) be the following actual physical part of that row:
\[
 \begin{gathered}
       sq\in I,\quad (sq,N)=1,\quad
       m=N-sq=p_1p_2p_3p_4\ \text{with distinct actual primes},\\
       x^{.120}\le p_i\le x^{.450}\quad(1\le i\le4),\\
       q\text{ composite},\qquad P^-(q)\ge x^{.071}.
 \end{gathered}
\tag{1}
\]
Uniformly for every sufficiently large even \(N=2x\), this piece gives a strictly negative contribution at the original natural scale:
\[
 \sum_{\mathcal D} W_s(q)\,C^\dagger(N-sq)\frac{C_q^{\rm hi}(q)}{\log q}
                     \ \le\ -.012\,M_N,\qquad
 M_N=\frac{\mathfrak S(N)x}{2\log x}.
\tag{2}
\]
This is an actual negative compensation, not a statement about the apparently positive rank-four term in the **true** \(q\)-prime row. It does not bound the rest of the signed artificial row.

## 1. Exact even-rank pointwise sign

On the squarefree shape (1) every divisor cutoff error \(E_H,E_C,E_P\) in (10) of [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md) vanishes: the only possible \(\Lambda\) arguments in those errors are \(\ll H^3\), whereas every actual prime factor is at least \(x^{.120}\). The first two sums of (10) combine into the divisor test that is \(\log a\) for \(a<Z=m/B\) and \(\log(m/a)\) for \(a\ge Z\). This differs from \(\min(\log a,\log(m/a))\) only for a central range \(Z\le a\le\sqrt m\), with absolute difference \(O(\log H)\). There are at most 16 divisors here. For even squarefree rank, complements have equal Möbius sign, so the exact symmetric-min test gives
\[
            2\!\!\sum_{\substack{a\mid m\\ a<\sqrt m}}\mu(a)\log a .
\]
Let \(a_1\le a_2\le a_3\le a_4\) be the four \(\log p_i\), and \(\sigma=\log m\). All singletons are below half and all triples are above half. For each partition of the four labels into two pairs, exactly the lesser of the two log sums belongs in the divisor sum; equality would make the two distinct squarefree prime products equal, impossible. The inner sum is therefore
\[
   -\sigma+(a_1+a_2)+(a_1+a_3)+\min(a_1+a_4,a_2+a_3)
        =\min(2a_1,\sigma-2a_4).
\]
Thus uniformly on (1),
\[
          C^\dagger(m)=2\min(2a_1,\sigma-2a_4)+O(\log H)
                          \ \ge\ (.200-o(1))L,
\tag{3}
\]
as \(\sigma\ge L=\log x\), \(a_1\ge.120L,a_4\le.450L\). The true \(W_s(q)\) is \(\ge .44\) for large \(x\), since \(\log s/\log(sq)\le .14+o(1)\).

On the \(x^{.071}\)-rough \(q\) support, every nontrivial divisor \(r,k\) respectively exceeds the exact thresholds \(U_q,V_q\), and \(rk>E\) is then automatic. The literal convolution, with the \(r=1\) contribution removed, is
\[
              C_q^{\rm hi}(q)=(\mu*\Lambda*\mathbf1)(q)-\log q
                              =\Lambda(q)-\log q .
\tag{4}
\]
Thus for rough composite \(q\) of at least two distinct prime factors the actual ratio in (2) is \(-1\). It is also nonpositive on proper prime powers; their count will be shown negligible. In particular (2) is obtained by exhibiting negative terms, not by cancellation inside the stated sector.

## 2. Sieve on the actual four-prime product, with the full-scale modulus

Let
\[
 a_m=\frac1{24}\sum_{\substack{p_1p_2p_3p_4=m\\ x^{.120}\le p_i\le x^{.450}}}1
\]
where the four prime factors in this definition are ordered and need not initially be distinct, so \(0\le a_m\le1\). On distinct products it is exactly the required indicator. The total number of \(m\le 3x/2\) with a repeated prime from this band is \(O(x^{.88})\) by the elementary square-divisibility bound. In the physical sum over \(s,q\), each \(m\) determines \(n=N-m\), and the number of admissible \(s\)'s dividing \(n\) is bounded by \(\tau_2(n)=x^{o(1)}\); all other rank-four weights cost at most a fixed log power or divisor power. Thus the total repeated-prime cost is power-small, and it is legitimate to use \(a_m\) as a positive sequence for distribution and then remove those cases.

For each fixed \(s\) in the prime band, take the sequence of \(q=(N-m)/s\) formed from \(m\in N-I\), \(m\equiv N\bmod s\), \((m,N)=1\), weighted by this \(a_m\). Define
\[
        X_s=\frac1{s-1}\sum_{\substack{m\in N-I\\(m,Ns)=1}}a_m .
\]
When sieving by a squarefree \(e\) composed of primes \(p<y=x^{.119}\) with \(p\nmid Ns\), the literal physical divisibility \(e\mid q\) is \(m\equiv N\bmod s e\). The local model mean is exactly \(X_s/\phi(e)\): all prime factors of \(m\) here exceed \(y\), so the coprimality to \(e\) adds no loss; \((s,e)=1\) by construction, and the centered reduced average at \(s e\) keeps \((m,Ns)=1\). Sieve out no primes dividing \(N\), because every physical \(q\) is a unit modulo \(N\). The prime \(s\) is also excluded if it lies below the particular sifting threshold, ensuring the reduced scalar formula; its omitted effect is included in the exact singular factor below. The residue \(N\bmod s e\) is reduced. Nonunit \(s\) were excluded from the start.

The error \(R_s(e)\) in this model satisfies
\[
 \sum_{\substack{s\text{ in band}\\ e\le x^{.355}\\ e\text{ as above}}}|R_s(e)|
                    \ll_D xL^{-D}
\tag{5}
\]
for every fixed \(D\), and also with any fixed divisor weight in \(e\) if desired. Use the full \(x\)-scale generalized BV, [Maynard I, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733), or [Liu--Park--Song Theorem 3.2](https://doi.org/10.1007/s40993-017-0089-3) for restricted prime products. For the explicit application of the former, split the four prime variables into dyads, take the first prime variable as the genuine SW factor, and group the remaining three into the divisor-bounded other factor. **Both** groups have fixed polynomial length here, as every original prime is at least \(x^{.120}\). Impose \((p_i,N)=1\) factor-wise; the SW factor loses only \(O(L)\) prime values for this mask and \(\omega(d_0)\) more for an auxiliary fixed divisor \(d_0\). For the central product cut, a relative \(L^{-F}\) rectangular mesh of the four labels leaves edge \(m\)'s in \(O(xL^{-F})\) interval strips. Physical divisor moments, together with the \(\tau_2(N-m)\) multiplicity of any admissible modulus \(s e\mid N-m\), pay arbitrary log precision. In the reduced mean the harmonic modulus sum gives the same property. This avoids any rapid twist on the genuine SW input.

The true moduli are \(s e\le x^{.495}\), so the full BV theorem applies with log reserve. A modulus at this scale has \(O(1)\) possible prime labels \(s\ge x^{.10}\) dividing it; once \(s\) is chosen, \(e\) is determined. This proves (5) from the absolute source discrepancy bound. A fixed extra \(\tau(e)^C\) may instead be paid by Cauchy and trivial reduced interval count with the divisor moment, but is not needed for the ordinary Rosser--Iwaniec remainder here. No bound for a single large \(s\)-row error is required; the summed error (5) is what is used.

## 3. Strict positive lower count of genuine rough composites

For \(p\nmid Ns\) use dimension-one local density \(g_s(p)=1/(p-1)\), and for \(p\mid Ns\) set \(g_s(p)=0\), including \(p=2\). Its dimension-one product condition is uniform because removing prime factors from the full odd-prime product can only lower its reciprocal ratio over an interval. Uniformly at \(w=z=x^{.071}\) and \(w=y=x^{.119}\),
\[
 V_s(w)=\prod_{p<w}(1-g_s(p))
      =(1+o(1))\,\frac{e^{-\gamma}\mathfrak S(Ns)}{\log w}.
\tag{6}
\]
Indeed compare to \(\prod_{p<w}(1-1/p)\): omitting 2 gives the factor 2; odd primes contribute \(1-1/(p-1)^2\) before omission corrections; each odd \(p\mid Ns\) then contributes the multiplier \((p-1)/(p-2)\). The omitted singular-product tail at \(p\ge w\) is \(o(1)\) uniformly, since \(\log(Ns)=O(L)\) and \(w\) is polynomial.

Use the classical Rosser--Iwaniec linear sieve (Friedlander--Iwaniec, *Opera de Cribro*, Theorem 11.12; see the displayed functions and statement of [Tao's linear sieve notes, Theorem 2](https://terrytao.wordpress.com/2015/01/29/254a-supplement-5-the-linear-sieve-and-chens-theorem-optional/)). In the needed ranges \(F(u)=2e^\gamma/u\) for \(1<u\le3\), and \(f(u)=2e^\gamma\log(u-1)/u\) for \(2\le u\le4\). The error in each main constant can be made \(o(1)\) uniformly using the dimension-one condition, taking the fixed sieve approximation error arbitrarily small and then \(x\) sufficiently large. Its remainder sum is covered after summing \(s\) by (5).

First sieve to \(z=x^{.071}\) with lower level \(D_{\rm lo}=x^{.284}\) and \(u_{\rm lo}=4\). The genuine \(z\)-rough count, summed over \(s\), is at least
\[
         \left(\frac{\log 3}{2\cdot.071}-o(1)\right)
                    \sum_s\frac{X_s\mathfrak S(Ns)}{L}
                    +O_D(xL^{-D}).
\]
Since \(z<s\) for all our \(s\), and \(q\) was already unit to \(N\), there is no missing local sieve condition that would enlarge the actual \(z\)-rough population. Next use the upper sieve at \(y=x^{.119}\), \(D_{\rm up}=x^{.355}\), so \(1<u_{\rm up}=.355/.119<3\). Every true prime \(q\asymp x/S\) passes this sieve. The weighted actual prime count is at most
\[
         \left(\frac{2}{.355}+o(1)\right)
                   \sum_s\frac{X_s\mathfrak S(Ns)}{L}
                   +O_D(xL^{-D}).
\]
The two estimates refer to the same actual \(a_m\) sequence and normalization, and it is valid to subtract the upper bound for primes from the lower bound for rough numbers. The gap is
\[
                  \Delta=\frac{\log 3}{.142}-\frac{2}{.355}
                                   >\frac{149}{71}>2.09>0,
\tag{7}
\]
where \(\log 3>1.098\) follows by the positive \(\operatorname{arctanh}(1/2)\) series. The true proper prime-power \(q\)'s have total label count at most \(x^{(1+.14)/2+o(1)}\) by summing \(O((x/S)^{1/2}\log x)\) over each prime dyad \(s\), so may also be removed at power-small cost. The already-paid repeats in \(m\) and these powers do not affect the strict gap.

## 4. Positive mass and signed normalization

Let \(C_4\) be the unordered four-prime exponent density on
\[
                   t_i\in[.120,.450],\qquad \sum_i t_i=1 .
\]
The actual \(a_m\) mass over \(N-I\) is \((C_4+o(1))x/(2L)\). This is the ordinary PNT product calculation: for fixed first three primes of exponents \(t_1,t_2,t_3\), sum the fourth prime across the \(m\)-interval of width \(x/2\) divided by their product, with main \(x/(2 L p_1p_2p_3 t_4)\) on any fixed compact subregion of the exponent domain; then sum the first three harmonic prime factors. Thin boundaries contribute \(o(x/L)\) by finite box approximation, since all \(t_i\ge .120\). Divide the ordered integral by \(24\). Removing fixed \(s\)- and \(N\)-nonunits in this total is uniform power-small compared to \(x/L\): if a prime factor divides \(sN\) it is at least \(x^{.120}\), and there are \(O(L)\) such candidates. Since \(a_m\le1\), the physical total is bounded by the number of their multiples in \(N-I\).

Explicitly \(1/\prod_i t_i\ge4^4=256\). After shifting \(t_i\) by .120, the simplex has sum .52 and each new coordinate at most .330. The four excluded corners do not overlap, since \(2\cdot.330>.52\), and each corner has simplex scale .190. Thus
\[
 C_4\ \ge\ \frac{256}{24\cdot 6}\bigl(.52^3-4(.19)^3\bigr)
        =\frac{9431}{46875}>.201 .
\tag{8}
\]
The continuum measure uses \(t_1,t_2,t_3\) with \(t_4=1-\sum_{i\le3}t_i\); moving the eliminated coordinate to any other label preserves this three-coordinate volume.

For \(s\nmid N\), \(\mathfrak S(Ns)=\mathfrak S(N)(1+O(1/s))\). Also
\(\sum_{x^{.10}<s<x^{.14},\ s\ {\rm prime},\ s\nmid N}1/(s-1)
=\log(7/5)+o(1)>.336\),
by harmonic PNT; entries \(s\mid N\) cost power-small. Therefore the lower count from (7) and (8) is
\[
     (\Delta C_4\log(7/5)-o(1))\,\frac{\mathfrak S(N)x}{2L^2}.
\]
Use \(C^\dagger\ge .199L\) eventually from (3), \(W\ge .44\), and the negative sign from (4). The resulting negative coefficient on \(M_N\) is strictly greater in magnitude than
\[
        \frac{149}{71}\cdot\frac{9431}{46875}
                    \cdot .336\cdot .199\cdot .44
      =\frac{21532170737}{1733398437500}>.0124 .
\]
All discarded errors are \(o(M_N)\), proving the safe \(-.012M_N\) of (2).

## 5. Exact limitation of the compensation

On the **whole** row, [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md) proves \(\mathcal T_{\rm v}(P)=\mathcal T_{\rm v}(J)=O_D(xL^{-D})\), so replacing \(C\) by \(C^\dagger\) in the artificial row costs no matched main. The genuine reverse expansion with fixed \(E=x^{.080}\) in [ReverseVaughanDoubleResidual.md](ReverseVaughanDoubleResidual.md) remains valid for the new reflected \(U=\sqrt x/H^4\), since all its \(d>U\) are at polynomial scales above the fixed reverse cutoff thresholds. Thus \(\mathcal T_{\rm v}(C^\dagger)=\mathcal T_{\rm p}(C)+O_D(xL^{-D})\) globally. The sector (1) is only a part of the first of these equivalent sums, not a physical subset of the second: genuine \(q\) primes do not occur in (1). Without a new upper bound on the **complement** of (1), this negative mass cannot be promoted to a global conclusion. In particular no Goldbach positivity follows from counting those composite \(q\)'s.

[Chan's November 2026 preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) also obtains specific fourth-rank restoration terms for its different finite sieve coefficient. [Arneth’s compensation preprint](https://zenodo.org/records/23016346) treats different fixed-target weights and an explicit selected example. In contrast (2) above applies in the exact opened Vaughan row at every sufficiently large even target, and does not estimate its complement or imply a sign for the original prime-pair count.
