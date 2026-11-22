# Bilateral subpower rough Möbius and Liouville signs at a prescribed small-radical target

Fix \(B>0\), \(0<\gamma<3/20\), and a compact interval \(J\subset(0,1)\) of positive length. At each sufficiently large individual **even** integer \(N\) with \(\operatorname{rad}(N)\leq(\log N)^B\), put
\[
 L=\log N,\qquad w=\exp(L^\gamma),\qquad
 \mathscr R=\{n\in NJ:P^-(n)>w,\ P^-(N-n)>w\},
\]
\[
 D_w(N)=\prod_{\ell\leq w}
        \left(1-\frac{2-1_{\ell\mid N}}{\ell}\right).
\]
Then, for either \(f=\lambda\) or \(f=\mu\), and for each specified pair \((\sigma,\tau)\in\{-1,1\}^2\),
\[
  \#\{n\in\mathscr R:(f(n),f(N-n))=(\sigma,\tau)\}
  = (1+o_{B,\gamma,J}(1))\,\frac{|J|N}{4}\,D_w(N).
  \tag{1}
\]
In the Liouville case both operands may also be required to be squarefree with the same asymptotic; the Möbius case already requires this. These are literal prescribed-target ordinary counts, not a target average and not a result conditional on a fixed Dirichlet zero-free half-plane. The eventual threshold may be ineffective. The same conclusion holds on the whole interval \(1\leq n<N\) with \(|J|=1\).

The exact local factor counts one forbidden residue \(0\bmod\ell\) when \(\ell\mid N\) and two residues \(0,N\bmod\ell\) otherwise. It is positive since \(N\) is even. Uniformly on these targets,
\[
  D_w(N)=(1+o(1))\,\frac{e^{-2\gamma_{\!E}}\mathfrak S(N)}{(\log w)^2},
  \tag{2}
\]
with \(\gamma_{\!E}\) Euler's constant and \(\mathfrak S(N)\) the ordinary binary singular series (including its factor \(2\) at \(2\)). Indeed the quotient by \(\prod_{\ell\leq w}(1-1/\ell)^2\) is precisely the truncated singular series; all target primes lie below \(w\) eventually and the residual Euler product is \(1+O(1/w)\). The uniform lower bound \(D_w(N)\gg L^{-2\gamma}\) will suffice below.

This extends the companion [small-radical affine reflected estimate](Proof.md) to a much sparser bilateral sample. The new work is the relative log-derivative truncation and removal of the genuinely present tags on that sample. The packet estimate remains the same one-prime-slot full-target comparison; both roughness tests below it are actual prime-divisor conditions.

## 1. Literal CRT density with permitted marks

Use the tag banks \(\mathcal B_j\), tag products \(\mathcal A_j\) and weights \(Z_j(n)\) of (7) in the companion note, with \(P=N\). Choose all band exponents strictly above \(\max(.1,\gamma)\), below \(.2\), with adjacent exponents separated by at least \(1/(20K)\) within each family. This is possible even for arbitrarily large fixed \(K\): the required span is less than \(1/20\), while the available width is \(>.05\) because \(\gamma<3/20\). Choose separated centers with some fixed room for a small neighborhood of each center, depending only on \(\gamma,K\). Within the neighborhoods move each band's exponent by steps \((\log 4)/\log L\) to make \(s\asymp_{\gamma,K}\log L\) different families, whose individual prime intervals are disjoint across all families. These steps multiply the lower logarithmic endpoint by \(4\), whereas each prime interval's upper logarithmic endpoint is only twice its lower one. The prime number theorem modulo \(4\) gives reciprocal masses \(\tfrac12\log2+o(1)\) for the full \(1\bmod4\) bands and hence the admissible range. All banks are disjoint from the roughness primes \(\ell\leq w\), and are target units.

Let \(M=|J|N D_w(N)\). The exact CRT model gives
\[
\begin{split}
 |\mathscr R|&=M+O_A(NL^{-A}),\\
 \sum_{n\in\mathscr R}Z_j(n)&=M+O_A(NL^{-A}),\\
 \sum_{n\in\mathscr R}Z_i(n)Z_j(n)&=M+O_A(NL^{-A})\quad(i\ne j),\\
 \sum_{n\in\mathscr R}Z_j(n)^2&\ll_K M+O_A(NL^{-A}).
\end{split}
\tag{3}
\]
For clarity, the arbitrary-log accuracy here follows by a single elementary truncation. Fix zero, one or two tag obligations, with lcm \(u\). They impose \(n\equiv N\bmod u\), so the bank avoidance at any prime of \(u\) is automatic; discard those redundant conditions. Open all other zero-residue bank exclusions and the exclusions \(0,N\bmod \ell\) at \(\ell\leq w\), using upper and lower Bonferroni at successive orders near \(r=\lfloor L^{.1}\rfloor\). The sum of the individual model forbidden probabilities is \(O_K(\log L)\), so the first omitted total reciprocal mass, with the tag \(1/u\) factored off, is at most \((C_K\log L)^r/r!\). Each chosen prime contributes one or two separate literal residue prescriptions. Their moduli are pairwise coprime, and coprime to \(u\), so CRT supplies each \(O(1)\) floor error. The number of terms including choices of obligations is at most \(\exp(O_K(L^{.3}))\), using the maximum logarithmic bank-prime size \(O(L^{.2})\); the small roughness primes obey the same upper bound. The total floor error and the total reciprocal error after summing the tag obligations are therefore \(O_A(NL^{-A})\) for any fixed \(A\). For repeated tag obligations the total reciprocal lcm mass is \(O_K(1)\) by the same finite Euler calculation as in (8) of the companion.

For the main term the disjoint small-prime exclusions supply exactly \(D_w(N)\) before any bank factor. The latter factors, including the double-tag lcm and source-bank avoidance, are precisely the means and second moments (7)–(8) in the companion. This proves (3). In particular with \(\bar Z=s^{-1}\sum_j Z_j\),
\[
 \sum_{n\in\mathscr R}|\bar Z(n)-1|^2
 \ll_K M/s+O_A(NL^{-A}).
 \tag{4}
\]
This is a **relative** bound on the rare sample, not removal by an unrestricted variance divided by a smaller scale.

## 2. Relative truncation of the source log derivative

Let \(F\) be either \(\mu\) or \(\lambda\) on the source \(n\), and \(G\in\{\mu,\lambda,\mu^2,1\}\) on \(N-n\). With the exact identity (6) in the companion, keep only the \(e=1\) prime term with \(N^\varepsilon\leq p\leq N^{1-\varepsilon}\), for fixed \(0<\varepsilon<1/4\) chosen first. Divide by \(\log n\); denote the truncated coefficient by \(F_\varepsilon(n)\). It has absolute value at most one. The discarded part in the **unmarked bilateral sum** is \(O_J(\varepsilon M)+o(M)\), with the first implied constant independent of \(\varepsilon\), as follows.

If \(p^e\mid n\) on \(\mathscr R\), necessarily \(p>w\). CRT–Bonferroni as in §1, with an added progression \(n\equiv0\bmod p^e\) coprime to all the roughness moduli, gives uniformly
\[
 |\mathscr R\cap\{p^e\mid n\}|
 = |J|N D_w(N)/p^e + O_A((N/p^e)L^{-A}+N^{o(1)}).
 \tag{5}
\]
The \(N^{o(1)}\) bound can be taken \(\exp(O(L^{.1+\gamma}))\) after allowing the two residues per prime. Use (5) over the proper powers and the primes \(p<N^\varepsilon\). Summing the former errors over at most \(N^{1/2+o(1)}\) powers is negligible; the former main terms cost \(O(M/L)\) by \(\sum_{p,e\geq2}\log p/p^e\ll1\). This also bounds the alternating \(\lambda\)-power terms in absolute value. For the small primes use \(\sum_{p<N^\varepsilon}\log p/p\ll\varepsilon L+1\); their aggregated floor error after division by \(\log n\asymp_J L\) is at most \(N^{\varepsilon+o(1)}\). Choose \(A\) large enough relative to the density bound in (2).

For the upper endpoint \(p>N^{1-\varepsilon}\), write \(n=pv\). Necessarily \(v\leq N^\varepsilon\) and \(P^-(v)>w\), allowing \(v=1\). At a prime \(\ell\leq w\) dividing \(N\), the reflected integer \(N-pv\) is already a unit since \(p,v\) are units there. At every other \(\ell\leq w\) one must exclude the **one reduced residue**
\[
       p\equiv N\bar v\pmod\ell .
\]
Write
\[
 E_w(N)=\prod_{\substack{\ell\leq w\\ \ell\nmid N}}
             (1-1/(\ell-1)),\qquad
 V_w=\prod_{\ell\leq w}(1-1/\ell).
\]
There is no \(\ell=2\) in \(E_w\). For a fixed \(v\), upper Bonferroni at the same depth gives the true prime bound
\[
 \sum_{\substack{N^{1-\varepsilon}<p\le N/v\\
                    P^-(N-pv)>w}}\log p
 \ll (N/v)E_w(N)+O_A((N/v)L^{-A}).
 \tag{6}
\]
The sum may omit \(N-pv=0\), since our original interval is central. To verify (6), each system of excluded residues is reduced modulo the product of its chosen primes. All such moduli are \(\leq\exp(O(L^{.1+\gamma}))\), so the ordinary Bombieri–Vinogradov theorem for prime weights applies at the common endpoint \(X=N/v\geq N^{1-\varepsilon}\) for this fixed \(v\). Those moduli appear once in the Bonferroni expansion, and the max-over-reduced-classes absolute error is \(O_A(XL^{-A})\). The main weights are exactly \(1/\varphi(q)\) and their omitted tail is again bounded by \((C\log L)^r/r!\). Extending the nonnegative upper sieve sum to all prime \(p\leq X\) is harmless, even at \(p\leq w\); alternatively their direct total weight is subpower. One can use the log-weighted prime version of BV, or use the von Mangoldt version and remove powers at a negligible aggregate error (the modulus range is subpower). This is an application at a separate fixed endpoint for each \(v\), not a short interval theorem or a summed max over unrelated endpoints at a single modulus.

By the elementary reciprocal Euler bound and Mertens,
\[
 \sum_{\substack{v\leq N^\varepsilon\\P^-(v)>w}}\frac1v
 \leq\prod_{w<\ell\leq N^\varepsilon}(1-1/\ell)^{-1}
 \ll \varepsilon L V_w.
\]
The bound applies since \(N^\varepsilon>w\) eventually for each fixed \(\varepsilon>0\). The exact local cancellation is
\[
                   E_w(N)\, V_w=D_w(N).
\]
For \(\ell\nmid N\) it is \((1-1/\ell)(1-1/(\ell-1))=1-2/\ell\), and for \(\ell\mid N\) the \(V_w\) factor alone remains. Sum (6) over the permissible \(v\), then divide by \(\log n\asymp_J L\). This gives \(O_J(\varepsilon N D_w(N))\) even at the actual sparse bilateral scale, as required. This step cannot be replaced by dropping the opposite roughness condition when summing over large \(p\).

## 3. Signed packet and the final counts

Because \(|F_\varepsilon|,|G|\leq1\), (4) inserts the average \(\bar Z\) in any truncated signed sum over \(\mathscr R\) with relative error \(O_K(s^{-1/2})+o(1)\). For a fixed family the truncated log derivative yields the literal source \(n=pv\), with the actual polynomial prime \(p\) outside the bank and above \(w\). Thus \(P^-(n)>w\) is exactly \(P^-(v)>w\), and bank avoidance is also separable. The other endpoint \(N-pv=u h\) is \(w\)-rough exactly when \(h\) is \(w\)-rough since every tag prime is \(>w\). Remove tags in \(G\) as in the companion note, accounting for repeated marked primes for \(\mu,\mu^2\) by the negligible integer estimate \(O(N\exp(-cL^{.1}))\) before fixed-log weights.

Apply the reflected bilinear packet bound (4) of the companion. Its proof allows the source \(v\) coefficient to omit *any* set of primes below \(\exp(2L^{.2})\), including all primes \(\leq w\): the real minor proof only needs the bank avoidance, prime slot and target units, and the long-slot major proof already bounds the reciprocal mass and tail of the inverse Euler factors by the full \(\exp(2L^{.2})\)-smooth indicator. Thus the enlarged omission does not add a major-arc estimate or a CRT loss. The residual function \(G(h)1_{P^-(h)>w}\) is bounded by one. Mesh and endpoint errors are paid to any fixed log power exactly as there, before unweighting. Taking the packet saving large compared to \(2\gamma\) gives \(o(M)\) for the marked truncated sums, for \(K\) sufficiently large after fixed \(\varepsilon\). The true unmarked sum is therefore \(O(\varepsilon M)+o(M)\); let \(\varepsilon\downarrow0\) only after the large-target limit. We have proved
\[
   \sum_{n\in\mathscr R} F(n)G(N-n)=o(M).
   \tag{7}
\]
The same estimate after interchanging the roles follows by replacing \(J\) by \(1-J\).

For \(\lambda\) expand the two signs using \((1+\sigma\lambda(n))/2\) and use (3), (7). In \(\mathscr R\), non-squarefree \(n\) or \(N-n\) requires a prime-square divisor \(\ell^2\) with \(\ell>w\). The set of such rows has size \(O(N\sum_{\ell>w}\ell^{-2})=O(N/w)=o(M)\), so it can be removed without affecting any count. On the remainder \(\lambda=\mu\), which gives (1) also for the nonzero Möbius signs. The full interval follows either by covering compacts and trimming, or directly from the first CRT count over the two short end intervals: for fixed \(\eta>0\) their bilateral rough mass is at most \(2\eta N D_w(N)+O_A(NL^{-A})\), not merely \(2\eta N\). Then let \(\eta\to0\).

## Comparison and exact scope

In the author's indexed [October 9 repository description of *Sums of two rough numbers with prescribed Liouville signs*](https://github.com/aster2024/openai-math-followups), Guo reports a positive lower bound for each pattern at arbitrary even targets in a central interval, with \(w=\exp((\log N)^{1/10})\), optional squarefree operands of bounded logarithmic factor count, and a fixed Dirichlet zero-free half-plane as input. The underlying repo/PDF was not retrievable directly at this audit. The present result uses the unconditional small-radical Iwaniec bounds for a restricted target family and gives a relative density and explicit local product for its literal bilateral sample. Comparison to ordinary unrestricted sign existence and to Guo's October 8 full-interval Liouville report is in [the companion note](Proof.md). No priority claim is made.

Here \(w=N^{o(1)}\) and never a fixed positive power of \(N\). In particular a negative-negative row can consist of two odd-rank composites; no bounded-rank or binary Goldbach assertion follows. The proof cannot replace \(w\) by \(N^\delta\) since then its actual auxiliary marks would all be absent. A stronger rough cutoff would need new arithmetic rather than a change of the character or CRT normalizations.
