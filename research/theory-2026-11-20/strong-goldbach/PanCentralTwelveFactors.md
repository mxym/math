# Twelve-factor central remainder in near-critical columns

Use the notation, literal orientation and centered discrepancy of [the polynomial roughness theorem](PanPolynomiallyRoughSurvivors.md). Put \(J=[P/3,2P/3]\) and \(E_d^J(f)=E_d(1_J f)\). Suppose
\[
 1/2\le v<53/105,\qquad 0<k<(4-7v)/6.
\]
For every fixed \(A>0\),
\[
 \sum_{D<d\le2D,\,(d,P)=1}\left|E_d^J\left(a(n)1_{P^-(n)\le P^k}\right)\right|\ll_A P(\log P)^{-A},\qquad D\asymp P^v.
\]
As in (4) of the linked theorem the centered error on the remaining nonsmooth squarefree moduli and rough input is the sole surviving term of the *signed central* column (up to the same error). In particular \(v=501/1000,k=2/25\) leaves only \(\Omega(n)\le 12\). The central restriction is essential to the cited application; no sign is known for the surviving discrepancy.

**Proof.** Choose a fixed \(k_0>2v-1\) satisfying \(36k_0+33v<17\) and \(15(k_0+v)<8\); this is possible precisely over the stated range (the first bound gives \(105v<53\) and the second \(45v<23\)). If necessary truncate at the requested \(k\). The proof of the linked estimate (2) is unchanged with \(J\), by the same multiplicative meshes or smooth approximation at its two endpoints. It covers factors \(\le P^{k_0}\).

Keep the factor mask \(P^-(n)>P^{k_0}\), and for the remaining window \(P^{k_0}<\ell\le P^k\) use the identical reciprocal-multiplicity prime tagging of its §C. On writing \(n=m\ell\) the smaller-prime mask depends only on \(m\). Squared primes in the window, and the independent meshes for the true \(m\ell\in J\) and \(b'\ell>Q_0\) boundaries, have the stated negligible costs. The output is a sum of \((\log P)^{O(1)}\) discrepancies for separated \(\alpha_m\beta_\ell\), with a long divisor-bounded sequence (after division by \(\log P\)), and a prime indicator in an interval, possibly multiplied by \(\log\ell/\log P\). The latter satisfies Fouvry (1.3), including the coprimality restriction, by Siegel–Walfisz and partial summation as in the linked proof. The unrestricted real modulus signs representing the absolute values constitute a sequence of order 1; Fourier or absolute averaging over target residues is not involved.

Apply [É. Fouvry, *Autour du théorème de Bombieri–Vinogradov II*, Ann. ENS 20 (1987), Corollaire 1, pp. 618–619](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf). Its notation is \(x=4MC\) for the long and short supports \([M,2M],[C,2C]\), and its uniform common shift range is \(0<|a|\le x\). **Take \(M,C\) to be the lower endpoints of the actual independent fine mesh intervals**, not the lower endpoints of their coarse containing dyads. The supports fit these new dyads. In every kept box \(MC\ge (P/3)(1-o(1))\); thus \(a=P<x\) strictly. The two modulus constraints of Corollaire 1, with an arbitrarily small fixed exponent margin, are
\[
 D x^\epsilon\le (xC)^{1/2},\qquad D x^\epsilon\le x^{4/7}C^{-6/7},\qquad C\ge x^\epsilon.
\]
For \(k_0\le\log C/\log P\le k+o(1)\) the first two follow respectively from \(k_0>2v-1\) and \(k<(4-7v)/6\). Fouvry's constants in this corollary are independent of \(a\). Summing the mesh boxes with extra log savings proves the estimate. Centering the complete signed mean and removing smooth moduli use the linked §§A,D, now with the additional indicator of \(J\); this does not assert cancellation of a mean on an arbitrary partial modulus mask. The original domain outside \(J\) is not estimated here. Fouvry himself specifically related his corollaries to Goldbach-type sieve applications (pp. 619–620); no new underlying dispersion estimate is claimed.

For a different 2026 use of genuine prime-product masks and rough comparisons, see [Pham Van Khanh, Appendix F, v1](https://www.preprints.org/manuscript/202610.3061), which retains an exceptional target set in its comparison. The present result is confined to a particular signed centered column and makes no priority claim.
