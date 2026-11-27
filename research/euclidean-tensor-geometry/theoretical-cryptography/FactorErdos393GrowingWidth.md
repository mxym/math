# The minimum spread in a factorial factorization is asymptotic to n in density

For \(n\ge2\) let \(f(n)\) be the least spread \(a_r-a_1\) over all factorizations
\[
n!=a_1a_2\cdots a_r,\qquad 1\le a_1<\cdots<a_r,\quad r\ge2.
\]
This is the function in [Erdős Problem 393](https://www.erdosproblems.com/393), from [Erdős–Graham, *Old and New Problems and Results in Combinatorial Number Theory*, p. 76](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf). We prove the unconditional normal order \(f(n)\sim n\) in natural density, with a quantitative one-sided error outside a power-sparse exceptional set. This does not establish \(f(n)\to\infty\) along all integers, or finiteness of the width-one case.

**Theorem.** Fix \(\rho,\theta>0\) with
\[
2\rho<\theta,\qquad 120\rho+35\theta<1.
\]
Then
\[
\boxed{\quad
\#\{2\le n\le X:f(n)\le n-10n^{1-\rho}\log n\}
 \ll_{\rho,\theta} X^{1-\theta+2\rho}.
\quad} \tag{1}
\]
For example, outside \(O(X^{999/1000})\) exceptions up to \(X\) we have \(f(n)=n-O(n^{199/200}\log n)\), using \(\rho=1/200,\theta=11/1000\). One may instead use \(\rho=1/1000,\theta=1/50\) to get \(O(X^{491/500})\) exceptions and \(f(n)=n-O(n^{999/1000}\log n)\). In particular \(f(n)/n\to1\) in natural density. Some power saving in the exceptional-set count holds for every \(\rho<1/190\).

In fact, the proof gives a stronger statement for a prescribed number of factors. Put
\[
b=\tfrac{15}{2}(\theta+4\rho),\qquad
B=\tfrac32-\tfrac52\theta-b.
\]
If \(0<\sigma<1/2\) and \((1-2\sigma)B>1+b\), the same exponent \(1-\theta+2\rho\) bounds the number of \(n\le X\) admitting a factorization with
\[
2\le r\le 2n^\rho,\qquad a_r-a_1\le (n!)^{\sigma/r}. \tag{2}
\]
For instance \((\rho,\theta,\sigma)=(1/1000,1/50,1/50)\) gives the count \(O(X^{491/500})\) for (2).

## 1. The arithmetic centre is uniform over the factor pattern

Let \(y=\sum_i a_i\), \(m=y/r\), \(g=(n!)^{1/r}\), and \(J=a_r-a_1\). Since \(m,g\in[a_1,a_r]\), if \(g\ge4J\) then \(m\asymp g\) and \(|a_i/m-1|\le1/2\). Expanding the logarithm and using the exact cancellation of the linear terms gives
\[
\log(g/m)=\frac1r\sum_i\log(1+(a_i-m)/m)
         =O(J^2/m^2).
\]
In particular,
\[
y=rg+O(rJ^2/g) \tag{3}
\]
with an absolute implied constant. No offset set is fixed. The integrality of \(y\), rather than that of the mean \(m\), is what will be used for rational approximation.

Work on \([N,2N)\), put \(M=\lfloor N^\theta\rfloor\), and fix \(r\le 2(2N)^\rho\). Let \(\beta_1,\beta_2\) be positive multiples of \(r\) with \(r\le\beta_1<\beta_2\le M\). Suppose \(n,n-\beta_1,n-\beta_2\) all belong to this dyadic interval and all have factorizations satisfying (2) with this \(r\), possibly with completely different factor patterns. Select one witness per index; let \(y(s)\) be its factor sum and \(g(s)=(s!)^{1/r}\). Write
\[
q=y(n),\qquad p_i=n^{\beta_i/r}y(n-\beta_i),\qquad
\omega_i(z)=\prod_{j=1}^{\beta_i-1}(1-jz)^{-1/r},\qquad \omega_0(z)=1.
\]
The \(p_i,q\) are integers and
\(\omega_i(1/n)=n^{\beta_i/r}g(n-\beta_i)/g(n)\).
All geometric means here tend to infinity uniformly, and \(J\le g(s)^\sigma\), so (3) applies. Also
\(g(n-\beta_i)\ge (2N)^{-M/r}g(n)\) and \(\omega_i(1/n)=O(1)\), since \(\log\omega_i(1/n)\ll M^2/(rN)\). It follows from (3) that
\[
\left|\omega_i(1/n)-\frac{p_i}{q}\right|
 \ll (2N)^{2M/r} g(n)^{-2+2\sigma}. \tag{4}
\]
For any box \(\mathcal N\le n<\mathcal N+\lfloor N/\log N\rfloor\) with \(\mathcal N\in[N,2N)\), put \(G=(\mathcal N!)^{1/r}\). Uniformly for all these witnessed triples in the box,
\[
q=G^{1+o(1)}, \qquad
\max_{i=1,2}\left|\omega_i(1/n)-p_i/q\right|
 \le G^{-2+2\sigma+o(1)}. \tag{5}
\]
Indeed \(\log G\asymp N\log N/r\); the factorial changes its logarithm by \(O(N)\) on the box; and \(M\log(2N)/r=o(\log G)\). All these estimates are relative to \(\log G\), even when \(r\) grows.

## 2. Uniform Padé obstruction to too many triples

We use the explicit algebraic Padé lemmas of [Bui–Pratt–Zaharescu, *Advances in Mathematics* 422 (2023), 109021](https://doi.org/10.1016/j.aim.2023.109021), with their [full arXiv text](https://arxiv.org/pdf/2204.08423) as a second copy. Precisely, we use Lemmas 4.4, 5.2, 5.6, 6.3, and 6.4, concerning \(\omega_i\) and the variable-degree Padé polynomials, not Proposition 3.2 for a fixed input polynomial. Their bounds involve the displayed \(r,M,D\) explicitly; the factorial witness does not enter these algebraic lemmas. In those lemmas \(M\) only needs to be an integer upper bound for the gaps, with the displayed degree and size inequalities; their proofs do not require a lower restriction on the power defining \(M\). We record the interface and estimates so the dependence on the growing \(r\) can be checked.

For fixed \(r,\beta_1,\beta_2,\mathcal N\), suppose more than \(N/(M^3\log N)\) indices \(n\) in the box have the witnesses in §1. Choose a fixed real \(\zeta>0\) satisfying
\[
\frac1B<\zeta<\frac{1-2\sigma}{1+b},
\]
and let \(D=\lceil\zeta\log G/\log N\rceil\). We have \(D\asymp N/r\), hence \(D\gg M\) uniformly. Take the source's \(\epsilon_0=1/2\) and define \(Q(z)=\sum_{i=0}^2 P_i(z)\omega_i(z)\), where \(P_i\in\mathbb Z[z]\) are the Padé polynomials of degree at most \(D\) from Lemma 4.4. Put \(T(z)=r\prod_{j=1}^{M}(1-jz)\). With \(\mathcal O=\lfloor(5/2)D\rfloor\), that lemma gives \(Q(z)=\sum_{v>\mathcal O}c_vz^v\) with
\[
|c_v|\le e^{O(M)} (4r^4 M)^{(15/2)D}(2M)^v. \tag{6}
\]
The factor \(e^{O(M)}\) absorbs the source's explicit factor depending on \(M,\epsilon_0\); with fixed \(\epsilon_0\) the implied constant is absolute.

The derivative determinant \(\Delta(z)\) of Lemma 5.6 is nonzero (its explicit requirement is \(D>(M+2)/(1-\epsilon_0)\)) and has degree at most \(3D+3M\) by Lemma 5.2. Counting its roots with multiplicity at the distinct points \(1/n\), there is one witnessed \(n\), with \(\alpha=1/n\), such that
\[
a:=\operatorname{ord}_{\alpha}\Delta
 \le (3D+3M)\frac{M^3\log N}{N}.
\]
Set \(K=a+2\). We have \(K=O(M^3\log N)\le M^4\) for large \(N\). In particular \(KM=o(D)\), because \(5\theta+\rho<1\) follows from the hypotheses. Also \(T(\alpha)\ne0\).

For \(k\ge0\) the alternate derivative rows of the source are
\[
A_{k,i}=\frac{T(\alpha)^k}{k!\,\omega_i(\alpha)}
             (P_i\omega_i)^{(k)}(\alpha)\qquad(i=0,1,2).
\]
By Lemma 6.3 these rows for \(k\le K\) span dimension three. Lemma 6.4 says their denominators divide \(r^k n^{D+kM}\) and
\[
|A_{k,i}|\le (2rN)^k e^{O(M)} (4r^4M)^{(15/2)D}.
\]
Thus \(Z=r^K n^{D+KM}\) clears all denominators. For the approximation residual, (6), \(|T(\alpha)|\le r\), and \(\binom vk\le 2^v\) give
\[
\begin{split}
\left|\sum_i A_{k,i}\omega_i(\alpha)\right|
 &=\left|\frac{T(\alpha)^k}{k!}Q^{(k)}(\alpha)\right|\\
 &\le (2rN)^k e^{O(M)}(4r^4M)^{(15/2)D}
          \frac{(4M/N)^{\mathcal O+1}}{1-4M/N}.
\end{split} \tag{7}
\]
The estimates are uniform over \(k\le K\). The coefficients satisfy \(\log(4r^4M)\le(\theta+4\rho+o(1))\log N\), so they give
\[
Z\le G^{\zeta+o(1)},\qquad
|A_{k,i}|\le G^{\zeta b+o(1)},\qquad
\left|\sum_i A_{k,i}\omega_i(\alpha)\right|
 \le G^{-\zeta(1+B)+o(1)}.
\]
In the last exponent we used \(b-\frac52(1-\theta)=-(1+B)\). The \(o(1)\) terms here are uniform because \(K\le M^4\), \(M^5=o(D)\), and \(D\asymp N/r\).

For some \(k\le K\) the row pairing with \((q,p_1,p_2)\) is nonzero, by full rank. Consequently \(Z\sum_i A_{k,i}p_i\) with \(p_0=q\) is a nonzero integer. But (5) and (7) give the upper bound
\[
\left|Z\sum_i A_{k,i}p_i\right|
\le G^{1-\zeta B+o(1)}
   +2G^{-1+2\sigma+\zeta(1+b)+o(1)}=o(1).
\]
Both exponents are negative by the choice of \(\zeta\), a contradiction. This proves the bound \(N/(M^3\log N)\) for the number of witnessed centres of any fixed triple pattern in a box.

## 3. Counting all indices

For each \(r\le 2(2N)^\rho\) and each of its residue classes modulo \(r\), order the indices in \([N,2N)\) with a witness for (2). There are at most two initial indices. For each later index, use it and its two predecessors as a triple. If the span exceeds \(M\), there are \(O(N/M)\) such endpoints: when the ordered index of the endpoint has fixed parity, the two-step gaps telescope to a total at most \(N\). Otherwise the differences are a legitimate \((\beta_1,\beta_2)\). There are \(O(M^2)\) difference pairs and \(O(\log N)\) boxes. The uniform bound of §2 gives \(O(N/M)\) such endpoints per residue class. Summing over classes and then over the factor count gives
\[
\ll \frac{N}{M}\sum_{r\le 2(2N)^\rho}r\ll N^{1-\theta+2\rho}.
\]
Dyadic summation proves the asserted bound for (2).

## 4. From few factors to the normal order of the minimum spread

We now use the 2-adic capacity idea from [Terence Tao's discussion of Problem 393](https://www.erdosproblems.com/forum/thread/393), the starting point of [Turturean's separately stated abc-conditional approach](https://www.overleaf.com/read/rsncpywwwbqf). No radical bound or abc assumption is needed here.

Suppose a representation has spread \(J\ge 1\) and maximum factor \(a_r\). For \(j\le\lfloor\log_2 J\rfloor\), at most \(\lfloor J/2^j\rfloor+1\) factors can be multiples of \(2^j\). For larger \(j\) at most one factor can be such a multiple, and none for \(j>\lfloor\log_2 a_r\rfloor\). Summing on \(j\), the unit terms from the two ranges total at most \(\lfloor\log_2 a_r\rfloor\), while the sum of the \(J/2^j\) terms is at most \(J\). Thus
\[
v_2(n!)=\sum_i v_2(a_i)\le J+\lfloor\log_2 a_r\rfloor.
\]
On the other hand Legendre's formula gives \(v_2(n!)=n-s_2(n)\), where the binary digit sum \(s_2(n)=O(\log n)\). If \(d=n-J\ge10n^{1-\rho}\log n\), this gives \(\log a_r\ge(d-O(\log n))\log 2\). In particular \(a_r\) grows much faster than \(n\), so \(a_1=a_r-J\ge a_r/2\) for large \(n\), and then \(\log a_1\ge(d/2)\log 2\). Since \(a_1^r\le n!\le n^n\),
\[
r\le\frac{2n\log n}{d\log 2}\le 2n^\rho.
\]
Also \(J\le n\le(n!)^{\sigma/r}\) for large \(n\) and any fixed positive \(\sigma\) since \(r\le 2n^\rho\). The condition \(120\rho+35\theta<1\) is exactly \(B>1+b\), so sufficiently small fixed \(\sigma>0\) meets the condition in (2). Applying the few-factor result to a minimizing representation proves (1). The reverse bound \(f(n)\le n-2\) for \(n\ge3\) follows from \(2\cdot3\cdots n=n!\).

For comparison with the fixed-degree exponent, for every fixed \(A>0\) and \(\varepsilon>0\) the same proof also gives
\[
\#\{3\le n\le X:f(n)\le n-n/(\log n)^A\}
 \ll_{A,\varepsilon} X^{12\sqrt2-16+\varepsilon}. \tag{8}
\]
Indeed, that deficit forces \(r=O_A((\log n)^{A+1})\) by the same 2-adic bound. In §2 use the source's optimized \(\epsilon_0=2-\sqrt2\), replacing \(5/2\) by \(s=3-\epsilon_0\) and \(15/2\) by \(d_0=(2-\epsilon_0)(3-\epsilon_0)/\epsilon_0\). Since \(\log r=o(\log N)\), take \(b=d_0\theta\), \(B=s(1-\theta)-1-b\); the same rank, size and remainder estimates apply. The strict condition \(B>1+b\) now holds exactly when \(\theta<(s-2)/(s+2d_0)=17-12\sqrt2\). Choose \(\theta\) sufficiently close to that value, then small enough fixed positive \(\sigma\). Summing over the stated \(r\) costs only a power of \(\log N\); the \(N^{1-\theta}\) count absorbs it with the given \(\varepsilon\).

## Scope and comparison

The fixed-polynomial theorem of Bui–Pratt–Zaharescu gives \(O_H(X^{33/34})\) for fixed spread \(H\), by a finite union over offset sets. This note is a uniform adaptation of their Padé method, not a new Padé construction or an improvement to their exponent for a fixed polynomial. The distinction is that we use the integer sum of factors and apply the Padé comparison across different patterns with the same \(r\). There is no factor \(2^{H}\) from enumerating shapes, and the estimates remain explicit when \(r\) and \(H\) vary.

[verify_factor_erdos393_growing_width.js](verify_factor_erdos393_growing_width.js) uses exact integer checks for the central cancellation, factorial ratio, triple grouping, and parameter margins. The cited Padé lemmas and the higher-range argument, not the finite checks, prove the result.
