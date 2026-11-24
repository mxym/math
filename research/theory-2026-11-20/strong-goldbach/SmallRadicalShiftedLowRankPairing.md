# Low-rank shifted high chambers: real mass and a signed reflection cancellation

Use [the translated first-cover setup](SmallRadicalTranslatedTagTypeI.md) and [the smooth high coefficient](SmallRadicalShiftedHighChambers.md). This proves (i) genuine large unsigned coefficient mass in several remaining low-rank chambers and (ii) cancellation on a **bilateral opposite-parity** low-rank chamber by reflection, without any estimate for the general shifted Type II or \(\Gamma\).

Let the sufficiently large prescribed even target be \(P\), \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(I=PJ\) for fixed nondegenerate compact \(J\subset(0,1)\), \(m=P-n\), \(y=\exp(L^\delta)\) for fixed \(0<\delta<.1\). Use \(U_-=P^{1/4}e^{-2H}\), \(U_+=P^{1/4}e^{-H}\), \(H=L^{3/5}\), \(R_+=P^{1/4}\) and the same cutoff \(g\) as the smooth source chambers. After squareful source and proper-power corrections, the high coefficient on squarefree composite source \(n\) is
\[
T(n)=-\left(\sum_{\substack{r\mid n\\r>R_+}}\log r\right)
                \sum_{d\mid b(n)}\mu(d)g(\log d),
\quad b(n)=\prod_{\substack{p\mid n\\p\le U_+}}p.
\]
These preliminary errors are already smaller than any fixed logarithmic target. The shifted high signed sum has summand \(T(n)\lambda(m)1_{\{P^-(m)>y\}}\,C(n)\), where \(C(n)\in\{0,1\}\) is exact coverage by the union of all offset/family tags. This uses the exact sum of the first-cover assignments at every integer \(n\), not a model of tag multiplicity. There is no further \(\log n\) outside \(T(n)\). Let \(V_y(P)\sim e^{-\gamma}S(P)L^{-\delta}\) be the rough complement's prime-model factor.

## 1. Last genuine prime: uniform rough mass and missed coverage

Fix \(d_0\) equal to a product of one or two prescribed large primes, each a fixed positive power of \(P\), and write \(n=d_0 q\) with final genuine prime \(q\in I/d_0\). Assume \(P/d_0\ge P^\epsilon\) for fixed \(\epsilon>0\), and all prime factors of \(d_0\) exceed the packet primes and \(y\), as they do in every use below. Ordinary prime-log BV with actual endpoint scale \(X=P/d_0\) gives, uniformly in \(d_0\),
\[
\sum_{\substack{q\in I/d_0,\ q\ {\rm prime}\\P^-(P-d_0q)>y}}\log q
  =\frac{|I|}{d_0}V_y(P)+O_A\!\left(\frac{P}{d_0}L^{-A}\right).
\tag{1}
\]
For \(\ell\le y\), \(\ell\nmid P\), the actual forbidden progression is \(q\equiv P d_0^{-1}\pmod\ell\); it is one reduced class. If \(\ell\mid P\), a genuine \(q\) on its positive-power scale never equals \(\ell\le y\), and \(d_0\) is also a unit, so this prime contributes no constraint. The sieve moduli, using depth \(D\log L\) (or \(L^{.1}\)), are \(P^{o(1)}\). The two endpoints of \(I/d_0\) are both \(\asymp_J X\). BV's maximal error in a reduced residue applies to these actual endpoints for each \(d_0\) independently, so there is no fixed-residue or common-endpoint assumption across different \(d_0\). The model is the usual local product, with arbitrarily log-small factorial tails.

In the same sum, the contribution from \(C(d_0q)=0\) is at most
\[
O\!\left(\frac{P}{d_0}V_y(P)L^{-M/200}\right)
  +O_A\!\left(\frac{P}{d_0}L^{-A}\right).
\tag{2}
\]
Indeed the multi-offset proof applies to the final \(q\)-variable with forbidden classes \(q\equiv jP d_0^{-1}\pmod\ell\) for each packet prime \(\ell\) forced empty at offset \(j\). They are nonzero and distinct because \(\ell>M+1,\ \ell\nmid P d_0\). The local factor with \(t\) forbidden offsets is \(1-t/(\ell-1)\), and the rough primes \(\ell\le y\) are disjoint from packets. Greedy interval covering, the fixed-\(M,K\) union, and weighted prime BV pay exactly as before, with \(X=P/d_0\) rather than \(P\). Since \(X\ge P^\epsilon\), their errors remain uniform arbitrary log powers.

## 2. Actual positive and negative source libraries

For any fixed angular interval \([\alpha,\beta]\subset(0,1)\), prime reciprocal sums in \([P^\alpha,P^\beta]\) converge to \(\int_\alpha^\beta dt/t\), and the same holds with a fixed smooth angular weight (PNT and partial summation). Combining this with (1)–(2) gives the following actual **covered** asymptotics. Each chamber is squarefree and source factorization is uniquely labeled by the stated disjoint bands; the conditional \(q\)-interval is \(I/d_0\). Write \(t_p=\log p/L\).

* Rank two, \(n=rq\), \(t_r\in[.28,.30]\), \(d_0=r\). Both true factors exceed \(R_+\), so \(b(n)=1,\ T(n)=-\log n\). At fixed \(r\), \(\log n/\log q=(1-t_r)^{-1}+O(1/L)\) on the actual interval. Hence
\[
\sum_{\mathrm{chamber},\ m\ {\rm rough},\ C(n)=1}(-T(n))
\sim |I|V_y(P)\int_{.28}^{.30}\frac{dt}{t(1-t)}.
\]
* Rank three, \(n=rsq\), \(t_r\in[.26,.27]\), \(t_s\in[.29,.30]\), \(d_0=rs\). The last prime has exponent around \(1-t_r-t_s>.4\); all factors exceed \(R_+\). The coefficient is again \(-\log n\), and the unsigned main constant relative to \(|I|V_y(P)\) is
\(\int_{.26}^{.27}\int_{.29}^{.30}\frac{dt\,du}{tu(1-t-u)}>0\).
* Rank three with two small factors, \(n=rsq\), \(t_r\in[.13,.14]\), \(t_s\in[.15,.16]\), \(d_0=rs\). Both lie below \(U_-\), while their product exceeds \(U_+\) and the final prime \(q\) exceeds \(R_+\). Thus \(b(n)=rs\) and \(D_g(b)=1-1-1=-1\). Here \(T(n)=+\log q\) exactly, and the positive coefficient mass relative to \(|I|V_y(P)\) tends to \(\log(.14/.13)\log(.16/.15)>0\).

Indeed the pointwise errors from (1)–(2) sum over these \(d_0\)'s using their bounded prime reciprocal masses. This establishes both signs of the **Vaughan coefficient** \(T\) on actual rows with true mass \(\asymp PV_y\); it says nothing about the corresponding Liouville signs of their \(m\)'s. In particular no bound on absolute weights below \(PV_y/L\) can discard those complete source chambers, and equality or comparability of their unsigned masses cannot imply a signed cancellation.

## 3. A bilateral signed chamber that really cancels

Now assume \(J=1-J\) (otherwise restrict to its symmetric intersection with nonempty interior). Consider rows for which **both** \(n,m\) are squarefree, of ranks 2 and 3 in either order, and all prime factors on both sides exceed \(U_+\). We prove
\[
\sum_{\mathrm{bilateral\ chamber}} C(n)T(n)\lambda(m)
=o(PV_y(P)/L),
\tag{3}
\]
for \(M>200\), fixed; this sum is over genuine integer factorization rows, not a signed average over targets.

First replace \(C(n)\) by \(1\). For each rank-two or rank-three source with all factors \(>U_+\), fix its smallest one or two primes as \(d_0\) and let its largest true prime be \(q\). Then \(d_0=O(P^{2/3})\), \(P/d_0\gg P^{1/3}\), and \(\sum_{d_0}1/d_0\ll1\) by Mertens over primes \(>U_+=P^{1/4-o(1)}\). There is no need to impose the opposite rank in bounding the missed coverage: each opposite \(m\) in the chamber is \(y\)-rough. Use (2) and \(|T(n)|\le L\ll\log q\) for the last prime, to obtain absolute error \(O_A(PV_y L^{-M/200}+PL^{-A})=o(PV_y/L)\).

Next discard rows for which either side has a genuine factor in the narrow band \(\mathcal D_0=(U_+,R_+]\), with reciprocal prime mass \(O(H/L)\) by PNT partial summation. A factor in this band cannot be the largest in rank two or three on a fixed central interval (the largest is \(\gg P^{1/3}\)), so it is included among the fixed \(d_0\) on that side. For each such \(d_0\), the last \(q\) is prime and the opposite integer \(P-d_0 q\) has no small factor \(\le U_+\). An elementary simultaneous upper sieve counts at most
\[
\ll S(P)\frac{P}{d_0 L^2}+O(P^{1/5})
\tag{4}
\]
choices of \(q\): use the two bad residues \(0, P d_0^{-1}\) at each prime \(\ell\le P^{1/30}\), coinciding precisely when \(\ell\mid P\). Each prime factor of \(d_0\) exceeds \(U_+\), hence no small prime \(\ell\le P^{1/30}\) divides it. The usual Selberg quadratic upper sieve with trivial remainder \(z^6\) at \(z=P^{1/30}\) and the two-dimensional Euler product gives (4); \(P/d_0\gg P^{1/3}\), so all true prime \(q\) survive this low cutoff. This is the same elementary two-linear-form upper sieve as in the central quantization note, now for arbitrary coefficient \(d_0\) with those coprimalities. Sum the floor over at most \(O(P^{2/3})\) possible \(d_0\)'s. The reciprocal main sum with at least one of the one/two fixed primes in \(\mathcal D_0\) is \(O(H/L)\). With \(|T|\le L\), the lost weight on either side (using reflection for the second) is \(O(P S(P)L^{-1}(H/L))+O(P^{13/15}L)=o(PV_y/L)\), since \(H=L^{.6}\) and \(\delta<.1\).

On the surviving domain all prime factors of both \(n,m\) exceed \(R_+\). In both orientations \(T(x)=-\log x\) by the exact high formula. The rank 2 input has \(\lambda=+1\), and rank 3 has \(\lambda=-1\). Pair the two **actual** integer rows \(n\leftrightarrow m\), which stay within the symmetric domain. For \(n\) of rank 2 and \(m\) of rank 3 their combined signed coefficient is
\[
T(n)\lambda(m)+T(m)\lambda(n)=\log n-\log m,
\]
of magnitude \(O_J(1)\), not order \(L\). Re-use (4) without the narrow restriction, with bounded reciprocal \(\sum_{d_0}1/d_0\), to get \(O(P S(P)/L^2+P^{13/15})\) total bilateral rows. Thus the paired remainder is \(o(PV_y/L)\). This proves (3) without assuming a frequency estimate, a probability law for those actual factor patterns, or equality of unsigned sector sizes.

The same-parity bilateral rows do **not** cancel: under the same all-large restriction rank 2 plus rank 2 has negative coefficient in both orientations, and rank 3 plus rank 3 positive in both. These need true coupled estimates. Rows outside the bilateral rank restriction are also unaccounted for. No claim is made about the full shifted term or binary Goldbach.
