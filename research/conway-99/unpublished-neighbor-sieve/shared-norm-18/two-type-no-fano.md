# The two-type case has no Fano markings

Suppose only the neutral norm-18 and norm-24 types occur among the twelve selected unit types. Then **no neutral norm-14 marking occurs anywhere in the graph**, without assuming a symmetry. The two-type case remains open at ranks 40 and 42.

A norm-14 Fano marking has two 22-coclique endpoints: adjoin either sign side to the same 15-site anticomplete set. The endpoints meet in 15 sites. By the [marked-coset compatibility criterion](../../marked-coset-shells/README.md), their original isotropic seven-classes are compatible in a common maximal extension \(H\), since \(15\equiv1\bmod7\). Their indicator difference is the Fano marking, up to sign; it is also retained in that extension. More explicitly the corresponding coset vectors \(w_C,w_D\) both lie in the extension lattice, and their difference evaluates to the signed indicator difference because the common translate \(u_0\) cancels.

Write \(M\) for the number of eligible 22-cocliques in this extension and \(B\) for the number of eligible oriented norm-14 markings. The two endpoints give \(M\ge2\) and the two Fano orientations give \(B\ge2\). But [the short-count identities](two-type-short-counts.md) require \(M\) to be odd and \(42M+49B+9S\le189\), where \(S\ge0\) counts the eligible unit \((1,23)\) fields. Thus \(M\ge3\) would give \(42M+49B\ge224\), a contradiction.

Consequently the two \(B=2\) rows of the ten-tuple list cannot occur. The remaining eight tuples, in the order \((M,S,W_{0,18},W_{2,34})\), are
\[
\begin{gathered}
(1,2,50,129),\ (1,5,51,102),\ (1,8,52,75),\
(1,11,53,48),\ (1,14,54,21),\\
(3,0,51,63),\ (3,3,52,36),\ (3,6,53,9).
\end{gathered}
\]
Thus the eligible oriented norm-18 count lies between **400 and 432** in every maximal extension. At rank 42 these are graph-wide counts; at rank 40 the [averaging rule](two-type-residue-balance.md) gives \(2500\le N_{18}\le2700\).

## Stronger overlap count when three cocliques occur in an extension

If \(M=3\), any two eligible cocliques meet in 1 or 8 sites (15 would yield a Fano marking). Their centered indicator Gram matrix has diagonal \(154/9\) and off-diagonal entries in \(\{-35/9,28/9\}\). Strict diagonal dominance makes the three vectors independent. Each is orthogonal to every eligible norm-18 field by the [residue-balance argument](two-type-residue-balance.md), so the effective dimension for those fields is at most \(44-3=41\).

Select \(W_{0,18}\) representatives in each of the four signed classes as in the earlier matching proof. The edgeless-remainder rank inequality is the same with dimension 41. For \(W_{0,18}=51,52,53\) the largest admissible remainder has 114 vertices. The [standard-library scan](two_type_no_fano.py) verifies this and the eight tuples. Thus an extension with three cocliques must have respectively at least **45, 47 or 49** disjoint pairs of aligned six- or seven-site overlaps, according to its tuple. In particular it has at least 90 distinct overlap pairs in total. At rank 40, if \(h\) of the 50 extensions have three cocliques, the same [double-count](two-type-residue-balance.md) strengthens the graph-wide bound to \(\lceil(4150+7h)/2\rceil\) pairs. These are necessary incidence counts, not a realization.
