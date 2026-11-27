# Uniform bounds for dyadic-divisor gaps (Erdős #693)

For an integer \(n\ge3\), let \(\mathcal A_n=\{t\ge1:\text{some divisor of }t\text{ lies strictly in }(n,2n)\}\), and let \(G(n,k)\) be the largest internal consecutive gap of \(\mathcal A_n\cap[n,n^k]\).

**Results.**
1. For every fixed \(0<c<1/2\) and every sufficiently large \(n\), there are \(n^{1-2c+o(1)}\) explicit, distinct internal gaps of length at least \(c\log n\) in \(\mathcal A_n\cap[n,n^k]\), for every \(k\ge2\). Their left endpoints are \(\sim 2c n\log n\). In particular \(\liminf_{n\to\infty}G(n,k)/\log n\ge1/2\).
2. For each fixed \(k\ge3\) and \(\varepsilon>0\),
\[
 G(n,k)\ll_{k,\varepsilon}n^{1-\eta_k+\varepsilon},
 \qquad
 \eta_3=\frac{16}{97},\quad \eta_4=\frac{16}{207},\quad
 \eta_k=\frac{1}{k(k-1)+1}\quad(k\ge5).
\]
More precisely the sum of the numbers of admissible divisor representations in **every** window \((x,x+H]\) with \(\tfrac12 n^{5/3}\le x\le x+H\le 2n^k\) is
\[
 H\sum_{n<d<2n}\frac1d+O_{k,\varepsilon}(n^{1-\eta_k+\varepsilon}).
\]
The asymptotic applies to representations counted with multiplicity, not directly to the unweighted number of distinct integers. The sharper known \(O(\sqrt n)\) gap bound for \(k=2\) is not improved here.

## 1. Many gaps for every \(n\)

Fix \(c\) and put \(a=\lceil2c\log n\rceil+2\), \(L=\operatorname{lcm}(1,\ldots,a)\). By the prime number theorem for the Chebyshev function, \(\log L=\psi(a)=(1+o(1))a\), so \(L=n^{2c+o(1)}\). Take as anchors the multiples \(x\) of \(L\) in
\[
 an<x\le (a+1/2)n.
\]
There are \(n/(2L)+O(1)=n^{1-2c+o(1)}\) such \(x\). Every anchor itself belongs to \(\mathcal A_n\): \(a\mid x\) and \(n<x/a<2n\).

If \(1\le t\le\lfloor a/2\rfloor\) and \(x+t=qd\) with \(n<d<2n\), then
\[
 q>\frac{x+t}{2n}>\frac a2,\qquad
 q<\frac{x+t}{n}\le a+\frac12+\frac{\lfloor a/2\rfloor}{n}<a+1.
\]
Hence \(q\le a\), so \(q\mid L\mid x\). But \(q>t>0\), contradicting \(q\mid x+t\). Thus all \(\lfloor a/2\rfloor\) integers just after the anchor are missing. There is an admissible integer after \(\lfloor a/2\rfloor+x\) below \(n^2\), since the next multiple of \(n+1\) lies at most \(n+1\) further on. Consequently each anchor is the left endpoint of a distinct internal consecutive gap of length at least \(\lfloor a/2\rfloor+1\). This gives both the count and the claimed liminf.

## 2. Local upper bound beyond the square range

Use \(e(t)=e^{2\pi i t}\), \(\widetilde\psi(t)=\{t\}-1/2\), and write
\[
 S_n(u)=\sum_{n<d<2n}\widetilde\psi(u/d),\qquad
 T_h(u)=\sum_{n<d<2n}e(hu/d).
\]
The Erdős–Turán discrepancy inequality and integration in the fractional-part variable imply
\[
 |S_n(u)|\ll \frac{n}{J}+\sum_{h=1}^J\frac{|T_h(u)|}{h}\qquad(J\ge1).
 \tag{1}
\]
Indeed the left side is bounded by the discrepancy in the counts of the points \(\{u/d\}\) in the intervals \([v,1)\), integrated over \(0\le v\le 1\).

**Low band.** If \(\tfrac12 n^{5/3}\le u\le n^2\), then the second-derivative test on \((n,2n)\), with \(|(hu/t)''|\asymp hu/n^3\), yields
\[
 |T_h(u)|\ll h^{1/2}n^{1/2}+h^{-1/2}n^{2/3}.
\]
Take \(J=\lfloor n^{1/3}\rfloor\) in (1). Summing \(h^{-1/2}\) and \(h^{-3/2}\) gives \(S_n(u)=O(n^{2/3})\).

**Bands of powers three and four.** An exponent pair \((\kappa,\lambda)\) for the phase \(f(t)=-hu/t\) gives
\[
 |T_h(u)|\ll (hu/n^2)^\kappa n^\lambda
 \quad\text{if }u\ge n^2,\ h\ge1.
\]
The first derivative is exactly \(hu\,t^{-2}\), so the monomial derivative condition holds, with parameter \(hu\ge n^2\). The sign is immaterial by conjugation. For \(n^{r-1}\le u\le 2n^r\) and \(r\in\{3,4\}\), this is at most a constant times \(h^\kappa n^{\lambda+(r-2)\kappa}\). Put
\[
 \eta=\frac{1-\lambda-(r-2)\kappa}{1+\kappa}.
\]
For \(\eta>0,\ \kappa>0\), \(J=\lfloor n^\eta\rfloor\) in (1) gives \(S_n(u)\ll n^{1-\eta}\), since \(\sum_{h\le J}h^{\kappa-1}\ll_\kappa J^\kappa\).
For \(r=3\), use Bourgain's pair \((13/84,55/84)\) with arbitrarily small positive losses. For \(r=4\), its image under the standard A-process is \((13/194,76/97)\), also with arbitrarily small losses. In (1) these give \(S_n(u)=O_\varepsilon(n^{1-\eta_r+\varepsilon})\) for \(\eta_3=16/97\) and \(\eta_4=16/207\). The same two pairs (and the A-process for the second) are listed in Weingartner's Table 1.

**Higher bands.** Fix \(r\ge5\) and \(n^{r-1}\le u\le 2n^r\), and set \(\eta_r=1/(r(r-1)+1)\). For \(1\le h\le J=\lfloor n^{\eta_r}\rfloor\), the magnitude of the \(r\)-th derivative of \(hu/t\) is comparable, with constants depending only on \(r\), to \(\Lambda=hu/n^{r+1}\). This derivative has fixed sign, so [Heath-Brown's Theorem 1](https://arxiv.org/pdf/1601.04493) applies (conjugate the sum if needed). It gives
\[
 |T_h(u)|\ll_{r,\varepsilon}
 n^{1+\varepsilon}\left(
  \Lambda^{1/[r(r-1)]}
  +n^{-1/[r(r-1)]}
  +(n^r\Lambda)^{-2/[r^2(r-1)]}
 \right).
\]
To apply the theorem literally on \([0,n]\), shift the left endpoint to 0 and drop the single \(d=2n\) term at a cost of at most 1. The first term in parentheses is \(O_r(n^{-\eta_r})\), since \(\Lambda\le 2n^{-1+\eta_r}\). The middle term saves more. For the last term, \(n^r\Lambda=hu/n\ge n^{r-2}\); moreover \(2(r-2)/[r^2(r-1)]\ge1/[r(r-1)]\) for \(r\ge4\). Substitute in (1), absorbing the harmonic sum into an arbitrarily small increment of \(\varepsilon\). This proves \(S_n(u)=O_{r,\varepsilon}(n^{1-\eta_r+\varepsilon})\).

Together these bands cover \(\tfrac12 n^{5/3}\le u\le 2n^k\), and the savings \(\eta_r\) decrease with \(r\). Subtract the identities for \(\sum_{n<d<2n}\lfloor u/d\rfloor\) at \(u=x+H\) and \(u=x\). This gives the stated local asymptotic, with its error uniform in both endpoints.

**Passing to internal gaps.** Since \(\sum_{n<d<2n}1/d\to\log 2\), the local asymptotic gives an element of \(\mathcal A_n\) in every such window whose length is at least a sufficiently large multiple of \(n^{1-\eta_k+\varepsilon}\). If the window from the left endpoint of an internal gap goes past \(n^k\), the gap is already at most the window length. For a gap starting below the analytic range, it suffices to treat integers \(m\le n^{5/3}\) and find an admissible \(y\ge m\) at distance \(O(n^{2/3})\), applying this with \(m\) one more than the left endpoint. For \(n\le m\le 2n+1\) this follows directly from \(n+1,\ldots,2n-1,2(n+1)\in\mathcal A_n\). Otherwise take
\[
 q=\left\lceil m/(2n-1)\right\rceil,\qquad
 d=\left\lceil m/q\right\rceil,\qquad y=qd.
\]
For \(m\ge2n+2,\ n\ge3\), the bound \(m/(2n-1)+1<m/n\) shows that \(q<m/n\), so \(n<d\le2n-1\). Also \(0\le y-m<q\ll n^{2/3}\). This proves the claimed gap bound.

## Literature comparison and limits

* This is the strict-endpoint version of [Erdős #693](https://www.erdosproblems.com/693), from Erdős, [*Some unconventional problems in number theory*](https://numdam.org/item/AST_1979__61__73_0.pdf), Astérisque 61, 1979. The July 2026 [working report](https://erdosproblemaday.com/report/693) writes the floor-sum identity and proves a power saving for \(k=2\); the October 2026 [we-solve manuscript](https://we-solve.github.io/contributions/erdos-problem-693-713b93d3/attempt-3/r1/) gives \(G(n,2)\le(12/5)\sqrt n+3\) and the stronger bound \(\limsup G(n,k)/(\log n\,\log_2n/\log_3n)\ge1/2\). Its latter construction uses a subsequence, whereas Section 1 gives many distinct locations for every large \(n\). Neither lower result rules out a power of \(\log n\) larger than the first power.
* The analytic mechanism is not new: see Andreas Weingartner, [*Somewhat smooth numbers in short intervals*](https://arxiv.org/pdf/2105.13568), Eq. (1), Eq. (4), and Table 1, for the same dyadic reciprocal sums in the overlapping range \(n\le\sqrt u\). In particular a fixed-\(k\) power saving already follows by applying his bound to this range; we do not claim otherwise. In the top band \(u\asymp n^k,\ k\ge5\), using the derivative theorem directly improves on the saving from Weingartner's explicitly listed Heath-Brown exponent-pair choice \((\kappa_k,\lambda_k)\) in Eq. (3) and the following example \(a=1-1/k\). That choice saves \((k^2-k+2)/(k(k^3-3k+4))\) as a power of \(n\), while the direct bound saves \(1/(k(k-1)+1)\); their cross-multiplied difference has positive numerator \((k-1)(2k-1)(k-2)\). This does not assert optimality over all analytic methods or all known pairs.
* Analytic inputs: the standard Erdős–Turán inequality, the second-derivative test, [Bourgain, Theorem 6](https://arxiv.org/pdf/1408.5794) and the standard A-process, and [Heath-Brown, Theorem 1](https://arxiv.org/pdf/1601.04493). No analytic hypothesis beyond these theorems is assumed. A polylogarithmic upper bound remains open.

The companion Node.js script checks the finite strict-endpoint gap certificate, agreement of two representation counts, and the rational exponent comparisons. It does not test the asymptotic theorems.
