# Three more rank-36 four-type exclusions from Fano transports

The following three exact four-type faces are impossible at Seidel rank 36:
\[
\begin{aligned}
&\{U_{0,20},U_{0,24},U_{0,26},U_{2,28}\},\\
&\{U_{0,20},U_{0,24},U_{0,26},U_{3,37}\},\\
&\{U_{0,20},U_{1,25},U_{1,27},U_{3,37}\}.
\end{aligned}
\]
This is not a rank-36 exclusion. The checker proves these three independently and does not give a status to any other four-type palette.

## Rank-free shape and transport facts

Let \(m_k\) be the number of unordered pairs of distinct antipodal Fano lines with absolute dot \(k\), using the ordinary evaluation-coordinate dot product (an oriented Fano vector has square 14). Two distinct properly aligned Fano vectors have at most two agreements in each sign, by unique closure from any three sites of the same sign. Orient them for nonnegative dot, so this bounds \(k\le4\). At \(k=3\), their neutral difference would have square 22. It cannot include an entry of magnitude two, since changing sign if necessary and adding \(d_i=3e_i-Ae_i\) there would give charge one squared norm \(22+23-28=17\), impossible. Thus the three agreements include two of one sign, forcing their two common opposite neighbors as additional agreements. This contradiction rules out \(k=3\). At \(k=4\) exactly two same-sign agreements occur in each sign and there are no conflicts, and analogous unit arguments hold at \(k=2\).

**Dot four.** Align \(f,g\) for dot \(+4\), let \(P_0,Q_0\) be their two common positives and two common negatives, and put \(s=f+g\). The four sites induce an alternating square, whose opposite diagonals are \(P_0,Q_0\); \(s\) is \(+2\) on \(P_0\), \(-2\) on \(Q_0\), signed unit elsewhere, with square 36. Add \(d_i+d_j\) at \(Q_0=\{i,j\}\), which is a nonedge. The resulting graph mark has charge two and squared norm \(36+50-56=30\), hence is a unit \(G(2,30)\) labeling. The endpoints \(i,j\) are positive there. Given this label and those two specified positive sites, subtract their marks to recover \(s\). Its two \(+2\) sites and any of its ordinary \(+1\) sites determine one of \(f,g\) by triple closure; the other follows by subtraction. Therefore every target has at most \(\binom42=6\) preimages among aligned unordered pairs. Each unordered pair of lines has two alignments, so
\[
m_4\le3G(2,30).
\]
In particular, if \(G(2,30)=0\), all shared-positive-pair Fano collisions are impossible even if \(N_{20}\ne0\).

**Dot two.** Align for dot \(+2\). Their neutral square-24 difference cannot contain an entry of magnitude two (the same shift would have charge one and norm 19). There is precisely one common positive \(p\) and one common negative \(q\), since two agreements of the same sign would force two of the other. Put \(s=f+g\); its squared norm is 32 and its only exceptional entries are \(s_p=+2,s_q=-2\). The mark \(h=s+d_q\) has charge one and squared norm \(32+23-28=27\). It is unit if \(p\sim q\), and otherwise has one \(+2\), at \(p\), and no \(-2\). In fact all other negative sites of \(s\) are in at least one Fano's negative side containing \(q\), and thus are not adjacent to \(q\). In the nonunit case \(h-d_p\) gives a neutral norm-18 vector. Conversely the known \((1,27)\) nonunit split shows that the entire \(+2\)-only population has \(9N_{18}\) fields: the other nonunit source, a positive-site subtraction from \(G(2,26)\), always gives a \(-2\). Given \(h\) and its specified \(+1\) site \(q\), recover \(s\); its one common positive \(p\) and the pigeonhole among the other \(6+6\) positive sites force a unique pair of Fano summands by triple closure. There are at most eight candidate \(+1\) sites in unit \(h\), and five when a \(+2\) occurs. Counting the two alignments gives
\[
2m_2\le8U_{1,27}+45N_{18}.
\]

**Dot one.** Align for dot \(+1\). If the neutral square-26 difference is nonunit, uniqueness of short Fano differences charges the line pair to its two oriented difference vectors. The known nonunit count \(8G(1,21)\) bounds the number of those pairs by \(4G(1,21)\). Otherwise there is exactly one same-sign shared site and no sign conflicts. Select the alignment in which the shared site \(q\) is negative. The sum \(s=f+g\) has square 30 with unique exceptional \(-2\) at \(q\). Adding \(d_q\) gives a unit \((1,25)\) field, again because no other marked negative is adjacent to \(q\). Recover \(s\) from that field and the indicated \(+1\) site \(q\); applying triple closure to the two partitions of the other \(7+7\) positive sites proves the Fano sum pair is unique. There are at most seven candidate sites \(q\). Hence
\[
m_1\le7U_{1,25}+4G(1,21).
\]
These are counts on the actual graph, not a per-class independence hypothesis. They are valid at every rank for the true graph populations. If a selected target type has nonzero quadratic value, its rank-36 global raw count is \(2402W\); for \(U_{1,25}\) and \(U_{1,27}\) subtract their known nonunit sources before multiplication. The \(m_k\) in these inequalities are never divided by the extension-retention normalizer.

## Two elementary quadratic constraints

Let \(N=N_{14}\), \(F=N/2\). The sum of the rank-one projectors \(f f^T\) over one orientation of each line has trace \(14F\) and rank at most 44. Its trace-square is
\(196F+2(m_1+4m_2+16m_4)\).
Therefore
\[
88(m_1+4m_2+16m_4)\ge49N^2-4312N.
\]
Use an exact tangent at \(N=198\) in the certificates. Also count the \(4158\) graph nonedges as positive pair seeds. Each oriented Fano uses 21. Two distinct oriented Fanos sharing such a pair share exactly one such pair, and each absolute-dot-four line pair occurs just twice by the two orientations. Thus \(2m_4\ge21N-4158\), either by \(\binom{x}{2}\ge x-1\) or by the integer pair-incidence formula. This is the common-pair row used by the middle certificate.

## Exact certificate

The accompanying `rank36_four_fano_palette_cut.py` regenerates the published full averaged higher-moment rows, the rank-36 original scalar Fourier pair and the two maximal-extension theta conversion equations, using raw folded \(W\) and reversing the four unit substitutions. The only other lower slacks used by the checked rows are the visible nonnegative counts, original \(Y_1\ge0,\ Y_3\ge44804\), the established \(S\) nonnegativity, and where specified the zero-component coclique variance tangent at 34 and the actual global coclique-Sidon tangent at 15000. The old quadratic/conditional/geometric rows that the verifier can construct but that are absent from the explicit certificate weights play no role.

Place the checker beside `higher_moments.py` and `rank36_three_types.py` in the repository's shared-norm-18 directory. It uses only native exact arithmetic and local source rows; no LP solver. In the listed order it verifies nonnegative integer combinations equal to the respective negative constants
\[
-406138318584356050,\quad -85401435,\quad -50714072332.
\]
This completes exactly the three stated exclusions, separately from all unresolved or merely numerical tests.

The subsequent [orthogonal-Fano cut](rank36-four-orthogonal-cut.md) excludes a fourth support under a separate exact witness.
