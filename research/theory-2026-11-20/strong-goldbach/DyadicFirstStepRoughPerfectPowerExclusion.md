# Excluding a whole first-step factor type at dyadic and very small-radical targets

Research note, 2026-11-24. Uses established theorems of Yu and Bérczes–Bugeaud–Győry–Mello–Ostafe–Sha; no priority claim for the fixed-coefficient Diophantine consequence. The input is a real prime \(p\), and the complement is the actual integer \(N-p\). No all-composite orbit or no-Goldbach hypothesis is needed.

## 1. Result with growing prime root and growing cutoff

Let \(L=\log N\) and \(W=\log L\) for a large even \(N\). In the following concrete range there is an effectively allowable constant \(\kappa>0\):
\[
 \operatorname{rad}(N)\le C_0 W^{1/16},\qquad
 p\text{ an odd prime},\quad (p,N)=1,\quad \log p\le C_1W^{1/8},
 \qquad U=\kappa\log W .
\]
Here \(C_0,C_1>0\) are fixed; \(\kappa\) may be chosen small, independently of \(N,p\). For all sufficiently large \(N\), uniformly in these true prime roots, the actual \(U\)-rough part of \(N-p\),
\[
 R_U(N-p)=\prod_{\substack{q>U\\q\ {\rm prime}}}q^{v_q(N-p)},
\]
is **greater than 1 and is not any perfect power**. Equivalently its nonempty list of positive exponents has greatest common divisor 1. More generally the proof works for fixed exponents \(a,d\ge0\) with \(a+d<1/3\), replacing \(1/8,1/16\) by \(a,d\) in the hypotheses and choosing \(\kappa\) according to the slack. The fixed multipliers allow \(a=0\) or \(d=0\).

This includes \(N=2^k\) (and indeed any even sequence supported on a fixed finite set of target primes); in particular it holds for every fixed finite set of odd unit prime roots for large enough \(k\). It excludes an arbitrary \(U\)-smooth part times a repeated power, regardless of the exponent or the base of that power. When there is only one prime outside the cutoff, it must occur to exponent **one**. In the rank-three factor type \(q^2 r\) it excludes the whole subcase \(r\le U<q\), and also both factors \(\le U\); it does not exclude \(q^2r\) with two distinct factors both outside the cutoff. No claim of squarefreeness follows from exponent gcd 1.

## 2. Exact reduction to a cubical polynomial over \(S\)-integers

Put \(S=\{\infty\}\cup\{q:q\le U,\ q\hbox{ prime}\}\) in \(\mathbb Q\), and use \(\mathcal O_S=\mathbb Z[1/\prod_{q\le U}q]\). Write \(N=A X^3\) by reducing every prime exponent of \(N\) modulo 3. This gives integers \(A,X\ge1\) with \(A\le\operatorname{rad}(N)^2\) and
\[
 h(X)=\log X=(L-\log A)/3\sim L/3,\qquad
 \log h(X)=W+O(1).
\]
The actual complement is \(F(X)\) where \(F(Z)=A Z^3-p\). This polynomial has three distinct roots (its derivative \(3AZ^2\) can vanish only at 0, and \(F(0)=-p\ne0\)). Its multiplicative height is \(H(F)=\max(1,A,p)\), so \(\log H(F)\ll W^a+\log W\). Let \(s=|S|\) and \(Q_S=\prod_{q\le U}q\). Ordinary effective Chebyshev bounds yield \(s\ll U/\log U\) and \(\log Q_S\ll U\) for large \(U\); also \(s\log(2s)\ll U\).

Suppose the rough part is nontrivial and has an \(m\)-th root in the integers, \(m\ge2\). Start from \(N-p=b_0 y_0^m\) with \(b_0\) the \(U\)-smooth part and \(y_0\ge2\) the \(m\)-th root of the rough part. For each \(q\le U\), reduce the exponent of \(q\) in \(b_0\) modulo \(m\), moving the corresponding \(m\)-th power into the base. The result is
\[
 F(X)=N-p=b y^m,\qquad b=\prod_{q\le U}q^{u_q}\ge1,\quad 0\le u_q<m .
\]
Here \(b\) is an \(S\)-unit, \(y\ge2\) is **not** an \(S\)-unit (it retains a prime factor \(>U\)), and \(m\log y<L\). The reduction of \(u_q\) is crucial: it prevents the coefficient height in the \(p\)-adic logarithmic form from being of order \(L\). The smooth-only case is handled separately below.

## 3. Uniform logarithmic-form bound in the actual variable support

Choose \(\ell\mid N\) maximizing \(v_\ell(N)\log\ell\). Then
\[
 v_\ell(N)\ge\frac{L}{\omega(N)\log\ell}
            \gg\frac{L}{(\log W)^2},\qquad
 \ell\le\operatorname{rad}(N)\le C_0 W^d .
\]
Since \(p\) is a unit modulo \(N\), so is \(N-p\); thus every positive-exponent \(q\) in \(b\) and every prime divisor of \(y\) is prime to \(\ell\). If \(\ell\in S\), its exponent \(u_\ell=0\), so it is omitted. Apply [Kunrui Yu, *p-adic logarithmic forms and group varieties II*, Acta Arith. 89 (1999), 337–378](https://doi.org/10.4064/aa-89-4-337-378), [scanned original](https://bibliotekanauki.pl/articles/1390501.pdf), Theorem 1, (1.8)–(1.10), to the nonzero expression
\[
 \Xi=(-p)\,y^{-m}\prod_{q\le U}q^{-u_q}-1=-\frac{N}{N-p},
 \qquad v_\ell(\Xi)=v_\ell(N).
\]
The coefficient bound is \(\mathcal B=\max(3,m)\). The number \(n\) of bases is at most \(\pi(U)+2\); no multiplicative-independence hypothesis (1.11) is used, and \(y\) can be composite. Use the auxiliary field \(\mathbb Q\) when odd \(\ell=3\bmod4\), \(\mathbb Q(i)\) with its split place when odd \(\ell=1\bmod4\), and \(\mathbb Q(\zeta_3)\) when \(\ell=2\) (unramified inert). Thus (1.2) is met, ramification is 1, degree is at most 2, and residue degree \(f\) is one at odd \(\ell\), two at 2. In particular \(\ell^f\le 4\operatorname{rad}(N)\) and the ideal valuation on rationals is \(v_\ell\).

The original coefficient (1.10) is at most \(\ell^f\exp(O(n\log(n+2)))\) in these fields, with absolute implied constant. For example, use \(\ell^{\kappa_{\rm Yu}}\le4\), \(\Phi(\mathfrak p)\le\ell^f\), \(\omega_q(n)\le n!/2^{n-1}\), \(f\log\ell\ge\log2\), and the bounded field degrees in the displayed coefficient; the prefactor max of nonpositive powers is at most one. The same size bound follows directly from the introductory displayed estimate on p. 337. Since \(n\log(n+2)\ll U\), only \(\exp(O(U))\) is lost here.

By the modified heights (1.5), each \(q\le U\) contributes at most \(O(\max(\log U,\log\ell))=O(\log W)\). Their product is \(\exp(O(n\log\log W))=\exp(O(U))\) for \(U=\kappa\log W\). To choose the constant \(\kappa\) without a circular dependence in this statement, use \(\log\log W\le2\log U\) for all sufficiently large \(W\) for any fixed \(0<\kappa\le1\); its threshold can depend on \(\kappa\) but the coefficient in the \(O(U)\) does not. The two other height factors are \(\ll W^a\log W\) for \(-p\) (also valid when \(a=0\)), and \(\ll(\log y)(\log W)\) for \(y\). Therefore the lower and upper valuation bounds give, with an absolute effective \(C_*\) and harmless fixed powers of \(\log W\),
\[
 m \ll W^{a+d} e^{C_* U}(\log W)^4 \log\max(3,m).
\]
Here we used \(\log y < L/m\) and canceled \(L\). The estimate holds uniformly for the moving local divisor \(\ell\).

The function \(m/\log m\) is increasing for \(m>e\); equivalently \(m\le A_0\log\max(3,m)\) implies \(m\ll A_0\log(2A_0)\) for \(A_0\ge2\). Thus \(m\le W^{a+d+C_*\kappa+o(1)}\). In the concrete range \(a+d=3/16\), choose \(C_*\kappa<1/32\); then \(m\le W^{1/4}\) for all sufficiently large \(N\). In general choose \(\kappa\) and then \(\rho\) so that \(a+d+C_*\kappa<\rho<1/3\), giving \(m\le W^\rho\).

## 4. Effective height contradiction, including smooth-only complements

Use [Bérczes, Bugeaud, Győry, Mello, Ostafe and Sha, *Explicit bounds for the solutions of superelliptic equations over number fields*, Forum Math. 37 (2025), 135–158](https://doi.org/10.1515/forum-2023-0381), [full text](https://arxiv.org/pdf/2310.09704), Theorem 2.1, cases (i) and (ii), equations (2.8) and (2.9). For our three simple roots, the LeVeque indices are \((m,m,m)\): all three are 2 when \(m=2\), and for \(m\ge3\) two have gcd \(m\ge3\). The \(S\)-norm \(N_S(b)=1\) exactly, regardless of the ordinary height of \(b\). The field is \(\mathbb Q\), its discriminant is 1, and \(F^*=F\). Taking the logarithm of each displayed bound for \(h(X)\) yields
\[
 \log h(X)\ll
 \begin{cases}
  s\log(2s)+\log H(F)+\log Q_S,&m=2,\\
  m^3s\log(2s)+m^2(\log H(F)+\log Q_S),&m\ge3.
 \end{cases}
\]
One can check the \(m^3\) term in (2.9) from the factor \((6rs)^{14m^3r^3s}\) with \(r=3\), while the powers of \(H(F)\) and \(Q_S\) are \(O(m^2)\). Using \(m\le W^\rho\), \(3\rho<1\) and \(a\le\rho\), the second right side is \(O(W^{3\rho}\log W+W^{2\rho+a})=o(W)\); the \(m=2\) right side is also \(o(W)\). Both contradict \(\log h(X)=W+O(1)\).

If \(N-p\) is \(U\)-smooth, put \(b=N-p\), \(y=1\) and \(m=2\) in \(F(X)=b y^m\). Theorem 2.1(i) applies to this solution with three simple roots just as before, imposes **no** nonunit restriction on \(y\), and its uniform \(N_S(b)=1\) bound again gives \(\log h(X)=o(W)\). Thus neither exceptional type remains. The nonunit hypothesis belongs to Theorem 2.2 (bound on variable exponent), not to our application of Theorem 2.1(i). We used Yu instead of 2.2 to improve the growth of \(m\) when \(S,p\) vary.

## 5. Fixed-input variants and scope in the original project

For fixed \(p\), fixed finite dictionary \(S\), and \(N=2^k\), a shorter proof uses the same source Theorem 2.2 with \(N_S(b)=1\) to bound \(m\) uniformly in the multiplier \(b\) whenever \(y\notin\mathcal O_S^\times\). Write \(k=3j+r\), \(r=0,1,2\), and take \(F(Z)=2^r Z^3-p\), \(X=2^j\). Then Theorem 2.1(i)/(ii) bounds \(X\), with the smooth-only case still \(m=2,y=1\). For \(m=2\) one can write the three (when the multiplier is fixed) elementary Mordell transformations as \(A=2^r\), \(Z=A X\), \(Y=A y\) when \(b=1\): \(Y^2=Z^3-A^2 p\), with constants \(-p,-4p,-16p\). For a general fixed \(b\) replace \(Z\) by \(AbX\) and \(Y\) by \(Ab^2 y\), yielding \(Y^2=Z^3-A^2b^3p\). This is an established effective superelliptic/Pillai-type application, not an assertion of new priority on \(2^k-p=x^m\).

The elementary shared-index shortcut is independent: \(2^k-p=x^m\) with \(d_0=\gcd(k,m)>1\) forces \(p=A_0^{d_0}-B_0^{d_0}\), \(A_0=2^{k/d_0}\), \(B_0=x^{m/d_0}\); primality yields \(A_0-B_0=1\) and \(p>A_0^{d_0-1}\ge\sqrt N\), excluding all low roots. When \(N=2^{2t}\), any square complement to a prime has root \(2^t-1\), and \(p=2^{t+1}-1\). For \(t\ge3\), primality forces \(t+1\) prime and \(t\) even, so the square root factors into the coprime odd integers \(2^{t/2}-1\) and \(2^{t/2}+1\), both \(>1\). Thus the only prime-square complement for even \(k\) is \(N=16,p=7,3^2\); a square with composite base at larger targets is not excluded for arbitrary macroscopic roots.

The old repository theorem EACThreeTwoAndThreePowers.md concerns three-label exceptional autonomous components at all dyadic centers (and twice powers of three), with unrestricted labels and whole closed-factor-graph hypotheses. This note concerns actual **single first rows** with quantitative small-root and radical restrictions and requires no component; neither result implies the other. The repository checks and literature search disclosed no reason to assert priority for the fixed-shift perfect-power conclusion. All bounds are effective in principle but no numerical cutoff \(N_0\) was computed. A surviving squarefree complement or a non-perfect-power composite with exponents gcd 1 is entirely compatible with the theorem. It neither proves a Goldbach representation nor claims a significant measure gain in the central near-full positive bank.
