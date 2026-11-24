# The genuine long-singleton k chamber reduces to a shifted Vaughan Type II

Written research note, 2026-11-24. This gives an exact paid/unpaid decomposition for one actual chamber of the original signed G23 additive statistic, not a cancellation claim for that chamber. It can retain the true prime-reflection test as well. Use \(P=2^j\), \(L=\log P\), actual \(n=pk\in PJ\), \(m=P-n\), \(p>P^\sigma\) true prime and \(z=e^{L^{.24}},\,y=e^{L^\delta}\) as before. Impose the fixed separated cap \(p\le P^{1/2-\varepsilon}\), with \(\sigma<1/2-\varepsilon\). Let \(z<w=P^{o(1)}\), and take the actual k-chamber
\[
 k=d t,\quad d\le P^\eta,\quad d\ {\rm z\text{-}rough,\ w\text{-}smooth},\quad
 t>w\ {\rm prime},
 \qquad 0<\eta<\varepsilon/4.
\]
Thus \(d=k_{\le w}\) and \(k_{>w}=t\) are genuine unique factors, and \(\lambda(k)=-\lambda(d)\). The restriction \(d\le P^\eta\) here is part of the statement for the signed statistic; [the analogous reduction proved only in prime energy](G23SignedSmallFactorTranche.md) does not automatically remove the remaining d-tail in this signed statistic.

Let \(\mathcal K\) be any physical k interval and \(X_t\) any upper cutoff on the true t variable. In the exact unmarked target, the genuine signed summand on this chamber is \(-\lambda(d)W(p,dt)R_y(P-pdt)\lambda(P-pdt)\), where \(W(p,k)=1_{pk\in PJ}\log(pk)/L\). One may also test any bounded variation physical weight of n. A separate version puts \(1_{m\ {\rm prime}}\) in place of \(R_y(m)\lambda(m)\), without ever substituting an integer for that reflected prime.

## 1. Exact linearization and geometry

Since \(aP\le p d t\le bP\), the true t satisfies \(t\asymp_J P/(pd)\) and in particular \(t\gg P^{1/2+\varepsilon-\eta}\). Hence \(t>w,z\) automatically. Replace the primality test for t by \(\Lambda(t)/\log t\), preserving both \(t\le X_t\) and \(R_z(t)\). The only extra supports are prime powers, whose total absolute contribution before a possible outside \(L\) factor is
\[
 \ll L^C\sum_{p\le P^{1/2-\varepsilon}}\sum_{d\le P^\eta}\sqrt{P/(pd)}
 \ll P^{3/4-\varepsilon/2+\eta/2} L^C.
\]
This uses a true count of powers with exponent at least 2; a logarithm covers all exponents and also their \(\Lambda\) weights if desired. The bound is uniform in the actual windows and prime-reflection test. Once a summed \(\Lambda(t)\)-weighted estimate has been shown uniformly in \(X_t\), ordinary partial summation divides it by \(\asymp L\) to recover \(1_{t\ {\rm prime}}\).

Choose any fixed small \(\gamma>0\) with \(2\gamma+\eta<\varepsilon\) and \(2\gamma<\sigma\), and write \(U_0=V_0=P^\gamma\). The genuine pointwise Vaughan identity is
\[
 \Lambda=\Lambda_{\le U_0}+\mu_{\le V_0}*\log
 -\mu_{\le V_0}*\Lambda_{\le U_0}*1+\mu_{>V_0}*\Lambda_{>U_0}*1.
\]
It follows directly from \(\Lambda=\mu *\log\), \(\log=\Lambda*1\), and \(\mu*1=\delta_1\). The first term vanishes in the actual t interval. Keep the literal \(R_z(t)\) in all three nonzero sums. The two short convolutions write \(t=h u\) with \(h\le V_0\) or \(h\le U_0V_0\) respectively; the long one writes \(t=b\ell\), \(b>V_0,\ell>U_0\), with coefficients \(\mu(b)\) and \(\beta(\ell)=(\Lambda_{>U_0}*1)(\ell)\le\log\ell\).

## 2. The Type I parts with true reflected Liouville are paid

In either short convolution, \(h\) is z-rough on the literal \(R_z(hu)\) support. Impose this on h first, then expand \(R_z(u)\) and \(R_y(m)\) through their proven arbitrary-log Bonferroni depths, with squarefree tests \(d_1\mid u\) and \(e\mid m\). Coefficients of the short convolutions are divisor-log bounded and contribute only powers of L to harmonic sums. In a nonempty tuple \(p d h d_1\) is coprime to e, because \(P=2^j\) and all source arguments are odd by exact target units. The resulting true residue for \(m'=m/e\) is
\[
 m'\equiv P e^{-1}\pmod{p d h d_1}
\]
with the exact oddness condition realized by doubling that modulus. Its true interval is obtained by intersecting \(\mathcal K\), \(PJ\) and \(t\le X_t\) before reflection; it has both endpoints \(\asymp_J P/e\) when nonempty. The physical modulus is
\[
 \le P^{1/2-\varepsilon+\eta+2\gamma}\exp(o(L)),
\]
strictly within the available square-root Liouville BV level at \(P/e\) with the actual endpoint loss included. Grouping the modulus costs at most a divisor power in multiplicity (p is distinguished by \(p>P^\sigma\), since d is w-smooth, h is smaller than \(P^\sigma\) and d1 uses primes \(\le z\)); all retained coefficients are divisor-log bounded. The required weighted version follows also by Cauchy–Schwarz from the unweighted arbitrary-log bound for the nonnegative maximal error \(E(q)\), since \(E(q)\le O(X/q+1)\), \(\sum_{q\le Q}\tau(q)^C/q\ll L^{O_C(1)}\), and \(X=P/e\). Partial summation treats the genuine \(\log u\) or \(\log(pk)/L\) weights. Summing over e costs its harmonic mass. The rough-shell error's reciprocal bound is factorially small per arbitrary log power; the total CRT floors are at most \(P^{1/2-\varepsilon+\eta+2\gamma+o(1)}\) even counting all \(p,d,h,d_1,e\), and log-power coefficients do not matter. Thus both actual Type I contributions with strict reflected Liouville are \(O_A(PL^{-A})\), uniformly in \(X_t,\mathcal K\).

If using the true prime-reflection variant instead, the same Type I grouping invokes ordinary prime BV at endpoint \(\asymp_J P\) and gives its genuine CRT main (not zero). For each short h, after opening only the rough variable u, the prime test is the actual reduced class \(m\equiv P\bmod pdh d_1\). Each local model factor is \(1/\varphi(pdh d_1)\). Factoring the d1 terms through \(\ell\le z,\ell\nmid P\) gives \(V_z(P)/\varphi(pdh)\), because \(pdh\) is z-rough. This identity and the exact reflected integral furnish the corresponding genuine Type I prime main; no claim is made that this prime main cancels the Type II prime term.

## 3. The remaining genuine Type II target

Apart from arbitrary-log errors in the signed reflected-Liouville version, the \(\Lambda\)-weighted true long-singleton contribution is the exact signed field
\[
-\sum_{\substack{p\ {\rm actual\ prime}\\P^\sigma<p\le P^{1/2-\varepsilon}}}
 \sum_{\substack{d\le P^\eta\\R_z(d)=1,\ P^+(d)\le w}}\lambda(d)
 \sum_{\substack{b>P^\gamma,\,\ell>P^\gamma\\
 db\ell\in\mathcal K,\, b\ell\le X_t\\pdb\ell\in PJ}}
 \mu(b)\beta(\ell)R_z(b\ell)
 \frac{\log(pdb\ell)}{L}
 R_y(P-pdb\ell)\lambda(P-pdb\ell) .
\]
This is a concrete missing Type II estimate, with no arbitrary replacements of the μ, λ, or prime variables. The signed singleton portion of the original G23 additive statistic has outside factor L and target \(o(PV_y(P)/L)\). Thus a sufficient bound for this displayed \(\Lambda\)-weighted Type II is \(o(PV_y(P)/L)\), uniformly in \(X_t\), because partial summation dividing by \(\log t\asymp L\) then yields the required \(o(PV_y(P)/L^2)\) before the outside L. An arbitrary-log saving for this field would of course suffice. To transfer the original genuine prime singleton sign to the exact translated marker it is enough to use the earlier absolute missed-row bound \(O(P\kappa_z V_y L^{-M/200})\) before multiplying by L; fixed \(M\ge400\) is enough at the stated additive budget. This marker deletion is done on the actual singleton row, not individually on Vaughan parts.

Fixing \(p,d,\ell\) does **not** reduce this to the already paid one-function BV sum: the remaining b-variable includes \(\mu(b)\) on the same lattice as the reflected \(\lambda(P-gb)\) with \(g=pd\ell\), plus the exact roughness tests. In this field \(g\ge P^{\sigma+\gamma}\), the affine intercept is the moving full \(P\), and the real length in b is \(\asymp P/g\). Even the [ordinary fixed-affine two-point theorem](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf) states a bound for fixed affine forms with constants depending on them, not this varying family under the fixed dyadic target and extra prime/rough tests. Alternatively fixing b leaves the genuine truncated divisor weight \(\beta(\ell)\), not 1. Nothing in known conditional small-prime matching controls these long factors on the same affine lattice. This note isolates exactly the remaining signed task; it establishes neither its bound nor the full singleton, full G23, or Goldbach claim.
