# A linear denominator obstruction for slow lonely runners

Research note, 27 November 2026. For \(n\) distinct positive integer speeds \(V\) and a stationary runner, let \(\mathrm{ML}(V)=\max_t\min_{v\in V}\|vt\|\). A *witness* is a time at which all the distances are at least \(1/(n+1)\), and the denominator of a rational witness is its denominator in lowest terms.

**Theorem.** For every integer \(h\ge1\) there is a primitive \(n\)-element set \(V\subset[1,2n]\), where \(n=360h+4\), such that
\[
 \mathrm{ML}(V)>\frac4{n+1},
 \qquad
 \text{every rational witness has denominator at least }2n+12h+4 .
\]
In particular, universally searching only denominators \(\le2n+o(n)\) cannot settle the slow-speed case, even on sets with a large loneliness margin. The lower bound on the witness denominator is \((61/30)n+O(1)\) on this family.

The slow-speed case is Tao's suggested restriction \(\max V\le2n\) in [*Some remarks on the lonely runner conjecture*](https://arxiv.org/abs/1701.02048), addressed up to \(2n-O((\log n)^2)\) by [Pomerance](https://arxiv.org/abs/2111.07157) following [Bohman–Peng](https://arxiv.org/abs/2109.09860). The latter paper's coprime-pair proof uses rational witnesses with denominator at most \(2n\) in its proved speed range. Our result is a barrier to enlarging that type of denominator search to all slow speed sets without allowing strictly larger denominators. It is not a counterexample to Tao's restriction or the Lonely Runner Conjecture and does not improve the numerical speed cap of the cited positive results.

## 1. Construction and denominator exclusions

Fix \(h\ge1\) and abbreviate
\[
 m=10h,\quad \ell=6h+1,\quad c_0=60h+2,\quad C=120h-4,\quad D=2n+2\ell+1.
\]
Let
\[
 A=[1,\ell]\cup\{6j:1\le j\le 5h-1\},\qquad
 R=\{n+c_0+6i:0\le i<m\},\qquad V=A\cup([n+1,2n]\setminus R),
\]
where all intervals of speeds are integer intervals. The two parts of \(A\) overlap at exactly \(h\) points, so \(|A|=10h=|R|\), and \(1,2n\in V\). Write \(n+c\) for a removed speed; all such \(c\) lie in \([c_0,C]\), have \(c\equiv2\bmod6\), and \(n\equiv4\bmod6\). We will use \(n>3C\), \(C-c_0<c_0\), \(c_0>2\ell+1\), and \(n-C>2\ell+1\).

For a reduced fraction \(a/d\), \(d\ge2\), fix a unit \(x\bmod d\) with \(ax\equiv\pm1\bmod d\) and \(1\le x<d/2\) when \(d>2\). A speed congruent to \(0,\pm x,\pm2x\bmod d\) has distance at most \(0,1/d,2/d\), respectively. The use of residues \(\pm x\) below is always at \(d>n+1\), and of \(\pm2x\) only at \(d>2n+2\), so the appropriate distances are strictly below the witness threshold. Integer times fail outright.

**Small denominators, \(d\le n+1\).** The full interval \([n+C+1,2n]\) consists of selected speeds. If \(d\le n-C\), that interval contains a multiple of \(d\). If \(n-C<d\le n\), then \(2d>n+C\) and \(2d\le2n\). For \(d=n+1\), the speed \(n+1\) itself is present. These provide a zero residue.

**Middle denominators, \(n+2\le d\le 2n\).** If \(d\) is selected, use it. Otherwise \(d=n+c\in R\). For any inverse residue \(x\), the speed \(d+x\) belongs to \([n+1,2n]\), since \(d+x<3(n+C)/2<2n\). If it is selected this suffices. If \(d+x\in R\), then \(0<x\le C-c_0<c\), so \(d-x\) is also in \([n+1,2n]\) and suffices if selected. If both are removed, their indices in the removed progression are symmetric around the index of \(d\); hence \(x=6j\) with \(j\le\lfloor(m-1)/2\rfloor=5h-1\). The speed \(x\) is then in \(A\). In all cases some selected speed has residue \(\pm x\).

**The two denominators \(2n+1,2n+2\).** For \(x=1\) use speed 1. Otherwise \(d-x\in[n+1,2n]\). It cannot be in \(R\): its being a unit modulo \(d\) would contradict the common factor 3 for \(d=2n+1\), or the common factor 2 for \(d=2n+2\), since all removed speeds are multiples of six.

**Larger searched denominators, \(d=2n+j\) with \(3\le j\le2\ell+1\).** If \(x<j\), use \(x\) when \(x\le\ell\). Otherwise \(2x\ge2\ell+2>j\) and \(d-2x\) lies in the full interval \([n+C+1,2n]\), using \(x\le j-1\) and \(n-C>j\). It has residue \(-2x\). If \(x\ge j\), then \(d-x\in[n+1,2n]\), and we can use it if selected. If it is removed, write \(d-x=n+c\); then
\[
 2x=2n+2j-2c\in[n+C+1,2n],
\]
using \(j<c_0\le c\) and \(n>3C\). Thus the speed \(2x\) is selected. This exhausts all reduced denominators up through \(D\).

## 2. There are explicit witnesses with a large margin

Let \(q=30h-5\), so that \(\max A=q-1<n\), and take \(t=1/q+1/(3nq)\). For the high speeds \(n+1\le v\le2n\), the perturbation \(v/(3nq)\) lies between \(1/(3q)\) and \(2/(3q)\); the unperturbed phase is a multiple of \(1/q\). Consequently the perturbed phase is at distance at least \(1/(3q)\) from every integer. For the low speeds \(1\le v\le q-1\), the unperturbed phase has distance at least \(1/q\) and moves by less than \(1/(3q)\). Thus \(\mathrm{ML}(V)\ge1/(3q)>4/(n+1)\), as \(12q<n+1\). The maximal good distance and the smallest good denominator are different notions.

## 3. A simpler one-hole family with exact minimum denominator

For \(n\ge10\), \(n\equiv4\bmod6\), take \(V'=\{1\}\cup([n+1,2n]\setminus\{n+2\})\). Its **least witness denominator is exactly \(2n+5\)**. The preceding first three cases apply with just \(c=C=2\): the omitted middle denominator is hit by \(d+x\), since it lies in range and is not the omitted speed.

For \(d=2n+3\), the only inverse residues \(1\le x<d/2\) not already blocked by a selected \(d-x\) are \(1,2,n+1\). The speed 1, the speed \(d-4=2n-1\), and again the speed 1 (since \(2(n+1)\equiv-1\bmod d\)) block these cases in order. For \(d=2n+4\), such inverse residues can only be \(1\) or \(3\) (2 is not a unit); the speeds 1 and \(d-6=2n-2\) block them. In these two denominators the use of a doubled inverse residue makes the distance at most \(2/d<1/(n+1)\). At \(d=2n+5\), the time \(t=(d+1)/(2d)\) has denominator \(d\) in lowest terms. It gives distance \(v/(2d)\) for even speeds and \((d-v)/(2d)\) for odd speeds. For even speeds \(v\ge n+1\), and for odd speeds \(v\le2n-1\), so both distances are at least \(1/(n+1)\).

[The exact integer verifier](verify_factor_lonely_runner_denominator.js) replays the case certificates for \(h=1,\ldots,8\), verifies the large-margin witness there, and exhausts reduced fractions for the one-hole family for \(10\le n\le130\) in its residue class. The infinite statements use the written proof, not a finite extrapolation or a Lean run.
