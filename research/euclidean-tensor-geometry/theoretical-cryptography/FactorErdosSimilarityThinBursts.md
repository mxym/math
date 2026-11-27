# Thin logarithmic bursts in the Erdős similarity problem

**Scope.** This extends the published local-annulus criterion of [Zhang, *Positive-measure avoidance with growing logarithmic gaps* (2026), DOI 10.5281/zenodo.23305280](https://doi.org/10.5281/zenodo.23305280) ([source](https://github.com/mxym/math/blob/main/preprints/erdos-similarity-growing-gaps-2026-10/paper.tex)). It uses the same random finite tree and open repair, but counts continuum-parameter complexity by the **width of the input burst**, not its absolute position, then pays for a shrinking family of exponent sectors in proportion to their widths. It does not settle arbitrary null sequences, \(2^{-n^2}\), or \(2^{-2^n}\). The fixed-geometric case was already proved by [OpenAI Mathematics](https://github.com/openai/math/tree/main/preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026).

Let \(a_n\downarrow0\) be positive, strictly decreasing, and write \(z_n=-\log_2 a_n\). By a \((X,H,D)\) burst we mean that every closed interval of length \(D\) contained in \([X-H,X+H]\) contains some \(z_n\). All unspecified logarithms are natural. Suppose there are bursts \((X_j,H_j,D_j)\) with \(X_j,H_j\to\infty\), \(1\le H_j\le X_j/8\), and \(D_j\ge1\).

**Theorem.** The following assertions hold.

* **Prescribed powers.** If \(D_j=o(\log\log H_j)\), there is, for any \(0<\varepsilon<1\), a closed one-periodic set \(E\subset\mathbb R\) of measure greater than \(1-\varepsilon\) per unit interval that avoids the prescribed sequence for any fixed power \(s>0\). One can prescribe countably many such pairs of sequences and powers at once. No lower bound on the relative widths \(H_j/X_j\) is needed.
* **All powers at once.** Put \(\rho_j=H_j/X_j\). If
  \[
  \sum_j\rho_j=\infty,\qquad
  \frac{D_j}{\rho_j\log\log H_j}\longrightarrow0, \tag{1}
  \]
  then the same \(E\) works for all real \(s>0\) simultaneously, even if \(\rho_j\to0\). Countably many sequences satisfying (1) can be prescribed.

Here avoidance means the following stronger assertion: whenever \(y\in\mathbb R\), \(c\ne0\), \(\alpha>0\), \(M<\infty\), and
\[
|f(a_n)-(y+c a_n^s)|\le M a_n^{s+\alpha}
\]
on a tail, infinitely many distinct values \(f(a_n)\) on that tail are outside \(E\). In particular the prescribed-power assertion with \(s=1\) yields affine non-universality, and \(E\cap[0,1]\) is compact. In any nonempty application \(E\) is nowhere dense, since an interval inside it would contain a sufficiently small translated copy for one of the prescribed powers.

## 1. A width-local entropy estimate

We use Zhang's finite blocker (Lemma 5), retaining its notation and all its guards except the final entropy guard, which is checked in a more local form. For clarity, \(p\) is its density budget, \(B\) its branching degree (instead of the source's \(b\)), \(d\) its depth, \(g\) the gap between edge windows, \(L\) the leaf-window length, \(U\) the integer start, and \(T\) the total template span. The selected logarithms are \(\zeta_i\); for integer coefficient band \(k\), the active logarithm is \(s\zeta_i-k\). The dilation ranges over \(2^k t\), \(1\le t\le2\), and the good errors have \(|e(b_i)|\le q b_i^{s+\alpha_0}\) with \(b_i=2^{-\zeta_i}\), \(q\) fixed, \(\alpha_0>0\) fixed.

Suppose every potentially active \(\zeta_i\), for every allowed \(s\) in a compact interval of exponents, lies in the same burst of width \(2H\), and the selected logarithms are separated by more than a fixed \(\delta>0\). Then at a designated first-default vertex the number \(P\) of candidate edge–input pairs has the uniform bound
\[
P\le (B-1)(1+2H/\delta). \tag{2}
\]
Indeed there are \(B-1\) nondefault edges there and at most \(1+2H/\delta\) selected inputs in that entire burst. In the source proof this count was bounded by the much larger quantity \(B(U+T+|k|+2)\), but the starts and endpoints of the grids are unchanged here.

For completeness, the local probability calculation uses only (2) in the following way. An edge window of length \(\ell\) and its child subtree span at most \(2\ell\). For each candidate input, the two activation lines and the local finest-grid boundary lines in the \((s,\log t)\)-plane number at most \(3+2^{2\ell+3}\). At a fixed center their signs, including zero signs, specify activation and actual grid addresses. The source's elementary line-arrangement bound and conditional first-default miss estimate consequently give a pointwise miss bound at most
\[
5120P^2\exp(-\kappa\ell),\qquad
\kappa=\frac{p(B-1)}{4D_*}-4\log2,
\]
where \(D_*\) bounds the output-log gaps in the active region (so the sampling constant is \(\eta=1/(2D_*)\)). This follows by applying the source calculation with \(P\) as the actual candidate-pair count; the sign patterns are independent of the unexposed random entries. If \(P=0\), a vertex with the required sampling lower bound cannot occur. The exposure of the center and independence of its unexposed test entries, including distinct terminal addresses, are exactly those in the finite blocker proof.

Thus its entropy guard can be replaced by
\[
C B^2(H+1)^2 e^{-\kappa L}<p,\qquad
C=5120\max(1,2/\delta)^2. \tag{3}
\]
No other part of that proof uses the old candidate bound: the selector default, center-stability bound, local sampling, finest-grid thickening, closed exceptional-center projection, and repair by an arbitrarily late input are retained. The conclusion is an open one-periodic blocker of density less than \(6p\). In particular (3) is a bound on the complexity of the continuum of \(s,t\), not a restriction to finitely many parameters that depend on the sampled tables.

## 2. Fitting the tree into the same thin burst

Fix a compact exponent range \([s_0,s_1]\subset(0,\infty)\), and take \(\delta=4/s_0\). We first work with one burst \((X,H,D)\) and one budget \(p\in(0,1/12)\). For a fixed power use the degenerate interval \([S,S]\subset[s_0,s_1]\). For a variable sector use
\[
I=[S,S(1+\rho/16)]\subset[s_0,s_1],\qquad \rho=H/X,
\]
and choose \(U=\lfloor SX-k\rfloor\). We show that arbitrarily late bursts admitting
\[
D/p=o(\log\log H) \tag{4}
\]
supply a blocker uniformly on their indicated sector, with all other fixed parameters and the requested input tail held fixed. Constants below are uniform for \(S\) and the sector inside the compact exponent range.

Choose the parameters
\[
\begin{split}
D_*&=s_1(\delta+D+2),\qquad B=1+\lceil 24D_*/p\rceil,\\
d&=\lceil 2^{B-1}\log(2/p)\rceil,\qquad K=\sum_{r=1}^d B^r,\\
g&=1+\lceil\log_2(8K/p)\rceil,\qquad
\kappa=p(B-1)/(4D_*)-4\log2,\\
L&=\max\left\{g,\ \lceil2D_*\rceil,\ 2,\
\left\lceil\frac{4\log(H+2)+\log(CB^2/p)+1}{\kappa}\right\rceil\right\}.
\end{split}
\]
Then \(\kappa>3\); the no-default and unstable-center probabilities satisfy the source's bounds \((1-2^{1-B})^d<p\) and \(K2^{3-g}<p\); and (3) follows directly. This scheduling is valid even when \(p\) changes with the burst.

To check the last point and the span, set \(t=\log H\), \(h=\log t\). Equation (4) gives \(B=o(h)\) and \(p^{-1}=o(h)\), using \(D\ge1\); also \(D_*/p=o(h)\). Consequently \(\log d=o(h)\), \(d\log(2B)=t^{o(1)}\), and \(g=O(d\log(2B)+\log(1/p)+1)=o(t)\). Thus \(L=O(t)\). By the source's tree-span recurrence,
\[
T\le (2B)^d(L+2g)=H^{o(1)}=o(H). \tag{5}
\]
In particular \(T\le U\) for large bursts since \(U\asymp X\). The source's finest-grid thickening guard involves \(N=2^{U+T+2}\) and
\[
r_U=(q2^{-k}+1)2^{-U}2^{-\alpha_0(U+k)/s_1}.
\]
It holds because \(\log(4Nr_U/p)\le -cX+O(T+\log(1/p)+1)\to-\infty\) for some \(c>0\), by (5), \(H\le X/8\), and (4). All other standing size guards hold eventually.

It remains to check that the samples actually serve the chosen template. Start with a logarithm in \([X-H,X-H+D]\), then repeatedly take the first logarithm strictly greater than the preceding selected one plus \(\delta\). Continue through the entire remaining sequence, not just inside the burst. While crossing the interior, every consecutive gap is at most \(\delta+D+1\): apply filling on a length-\(D\) interval starting half a unit after the threshold \(\zeta+\delta\), provided the interval is still inside the burst. For \(s\in I\) and \(U\le w\le U+T\),
\[
\left|\frac{w+k}{s}-X\right|
 \le X|S/s-1|+\frac{T+1}{s_0}
 \le \frac{H}{16}+\frac{T+1}{s_0}<\frac H4
\]
for all sufficiently late bursts. The same holds for fixed \(s=S\). Because \(D+\delta=o(H)\), the first selected sample precedes \(U\) at every \(s\), and all successive sample gaps needed to cross the template are bounded by \(D_*\) in output-log coordinates. To see that crossing cannot skip the interior, choose the last selected point below an interior endpoint; its first eligible successor is before the right boundary by the preceding greedy-gap inequality. If the very first sample were the last point below, the same inequality would apply because it lies within \(D\) of the left boundary. Iterating covers each required endpoint.

The active sample spacing exceeds \(s_0\delta=4\). Every open template window of length \(\ell\ge 2D_*\) contains at least \(\ell/(2D_*)\) interior active samples: the bracketing, possibly boundary, selected points are at distance at least \(\ell\), and their successive gaps are at most \(D_*\). This is the source's local-sampling guard, including when a sample coincides with an endpoint. Every potentially active input comes from \([X-H,X+H]\), so (2) applies. All selected inputs are beyond the prescribed input cutoff eventually. At a closed exceptional center the source's repair uses convergence through the **full** later selected tail, which was retained even though only the burst counts for (2).

This proves the thin-burst blocker for each prescribed coefficient band, power sector, error exponent and constant, and input tail.

## 3. Paying for the power continuum

For a fixed power and desired removal budget we can keep \(p\) fixed; the prescribed-powers hypothesis implies (4), regardless of how small \(\rho\) is.

For the simultaneous version first fix a compact range \([a,b]\) with \(0<a<b\), and a total density budget \(w>0\), with all other parameters and input tail fixed. Enlarge the ambient compact range to \([a,2b]\). Use sectors \([S,S(1+\rho_j/16)]\), one for each burst picked below, and pay \(p_j=\tau\rho_j\). Choose \(\tau>0\) small enough that \(p_j<1/12\) for every \(j\) and
\[
6\tau\big(32\log(b/a)+1/8\big)<w.
\]
For this fixed \(\tau\), assumption (1) implies (4). Discard a finite prefix of bursts to ensure the uniform guards above and the requested input tail. Starting at \(a\), place the subsequent sectors consecutively (their endpoints may coincide), always taking the preceding right endpoint as the next \(S\). Because \(\log(1+\rho/16)\ge \rho/32\) when \(0<\rho\le1/8\), the divergent sum of relative widths ensures that a finite initial batch reaches \(b\). Before the last step the right endpoint is less than \(b\), so the used sum of \(\rho_j\) is at most \(32\log(b/a)+1/8\). The final endpoint is less than \(2b\) as assumed. The union of their blockers therefore has density less than \(w\) and covers **every** power in \([a,b]\). The proof does not make an uncountable selection of exceptional sets. If the widths are summable, this particular late-sector tiling cannot cover a fixed nondegenerate exponent interval, since the sum of its logarithmic sector lengths from any sufficiently late index tends to zero. This is a limitation of the tiling, not an obstruction to avoidance itself.

Now enumerate the countably many tasks: a prescribed sequence, fixed power or compact exponent range, integer dilation band \(k\), integer error constant \(q\ge1\), error exponent \(1/m\), and input cutoff \(a_n<2^{-h}\). Choose the sum of deletion budgets, including reflected copies for negative dilations, less than \(\varepsilon\), and take the complement of the union of the open periodic blockers. Any specified nonflat germ on a tail fits some band and error bound on sufficiently late inputs (take \(1/m\le\alpha\)). For every input cutoff it has an output outside the complement. These are infinitely many distinct outputs: they converge to \(y\) and, by \(c\ne0\) and the smaller-order remainder, are eventually different from \(y\). This proves both assertions.

## 4. Strictly thinner than the published multiplicative-annulus class

The earlier property W implies (1): use its annuli for the single choice \(R=2\), then restrict to the centered bursts \(X_j=U_j\), \(H_j=U_j/8\). The relative widths are constant and \(\log\log H_j\sim\log\log U_j\). The following example establishes strictness.

For \(j\ge2\) let
\[
X_j=2^{2^{j^4}},\qquad H_j=\left\lfloor\frac{X_j}{32j}\right\rfloor .
\]
Let the \(z_n\) be the increasing enumeration of the successive finite progressions
\[
X_j-H_j,\ X_j-H_j+j,\ \ldots,\
X_j-H_j+j\left\lfloor\frac{2H_j}{j}\right\rfloor.
\]
Then \(D_j=j+1\) fills the indicated burst, \(\rho_j\sim1/(32j)\), and \(\log\log H_j\sim (\log 2)\,j^4\), so both conditions (1) hold. This yields a compact near-full-measure avoiding set for the corresponding \(a_n=2^{-z_n}\), simultaneously for every positive power and the stated remainders.

Nevertheless, the earlier property \(W\) fails even for any one fixed \(R\ge2\). The ratio of consecutive burst centers tends to infinity. For sufficiently large \(U\), \([U/R,RU]\) intersects at most one burst, whose center, if present, is comparable to \(U\). That burst has width \(o(U)\), leaving an unoccupied interval of length \(\gg_R U\). Thus the published hypothesis requiring all subintervals of length \(o(\log\log U)\) on those multiplicative annuli to be hit cannot hold. Consecutive logarithmic gaps here tend to infinity even within the bursts, so \(a_{n+1}/a_n\to0\). In particular the occupied logarithmic bins have upper Banach density zero: after a sufficiently late finite prefix every gap is at least any prescribed \(J\), and the upper density is at most \(1/J\).

There are also examples specific to the prescribed-powers statement, where the relative widths can be summable. For instance replace \(H_j\) by \(2^{2^{j^3}}\) while keeping \(X_j=2^{2^{j^4}}\) and the progression spacing \(j\). Then \(D_j=o(\log\log H_j)\) while \(H_j/X_j\) tends to zero faster than any geometric sequence. This proves affine avoidance in that example; the simultaneous-power argument above does not apply to it.

**Reproduction.** The adjacent exact arithmetic checker illustrates the sector rounding, bracketing margins, finite tiling with proportional budgets, entropy candidate bound, and sparse-burst parameter comparisons. It does not construct the enormous random routing tables or claim a Lean proof. The measure theorem is the written deduction above from the published finite routing lemma and the localized counting step.
