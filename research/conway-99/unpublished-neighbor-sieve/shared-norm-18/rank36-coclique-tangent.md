# Rank 36: norm 18, norm 24 and unit norm 26 cannot be the only three selected types

This excludes the sole exactly-three-type rank-36 alternative containing norm 18 that remained after the [original screen](panel-heights.md#all-rank-36-alternatives-with-exactly-three-selected-types). It uses a graph packing inequality inside each maximal lattice extension and an exact moment identity. No rank is thereby excluded.

## 1. Count norm-four vectors from compatible cocliques

Fix a maximal totally isotropic subgroup \(H\) of the seven-discriminant space, and let \(U\) be the corresponding rank-44 determinant-49 extension. Use \(W_{a,t}\) as in the [folded moment equations](../short-shell-moments.md#four-unimodular-lattices-from-the-same-extension), with nonzero seven-value shell counts divided by eight and charge \(+a\) counted once. In this section all quantities count vectors for this fixed \(H\). Put \(M=W_{2,22}\), the number of eligible independent 22-sets \(C\). Indeed a charge-two norm-22 labeling is exactly \(c=-1_C\); for these labels the seven-value is zero, and the original seven-class lies in \(H\) precisely when counted here. The degree-14 graph equation implies that every vertex outside \(C\) has exactly four neighbors in \(C\).

Distinct such cocliques meet in 1, 8 or 15 vertices by the [marked-coset compatibility criterion](../../marked-coset-shells/README.md). Let \(n_8,n_{15}\) count ordered pairs having the indicated overlap. The centered indicators \(1_C-\frac29\mathbf1\) have squared norm \(154/9\); for a distinct pair the inner product is \((|C\cap C'|-1)-35/9\). Nonnegativity of the squared norm of their sum gives
\[
n_8+2n_{15}\ \ge\ \frac59M^2-3M.
\]

For overlap 15, the difference of the indicators is a signed norm-14 eigenvector on the two exclusive 7-sets. It is a Fano support: an exterior vertex sees at most one per sign, and its counts on the two signs are equal. The two sign sets send \(14(14-4)=140\) edges outside, so exactly 15 exterior vertices miss both signs. The shared 15-set must be this entire set. Thus each ordered pair at overlap 15 has a distinct difference counted by \(W_{0,14}\), since the class difference lies in \(H\).

For overlap 8, write \(R=C\cap C'\), \(X=C\setminus R\), \(Y=C'\setminus R\) and \(O=V\setminus(C\cup C')\). Each \(o\in O\) has the same number \(h(o)\) of neighbors in both exclusive 14-sets, and \(4-h(o)\) in \(R\). Each site of \(X\) sees four in \(Y\) and none in \(X\cup R\), so \(\sum_Oh=140\). Each pair of sites of \(R\) has two common neighbors, all in \(O\), so \(\sum_O\binom{4-h}2=56\) and \(\sum_Oh^2=336\). For \(q_i=|\{o\in O:h(o)=i\}|\) this gives \(3q_0+q_1+q_4=7\) by summing \((h-2)(h-3)/2\). Hence there are at most \(8+q_0\le10\) vertices outside \(X\cup Y\) anticomplete to both. For fixed ordered exclusive sets, two different compatible shared 8-sets would intersect in at least 6 sites, giving two distinct eligible cocliques with intersection at least \(14+6=20\), impossible. The ordered overlap-8 pairs are therefore injective into the charge-zero squared-norm-28 fields counted in \(U^*\). Tightness sends these to vectors of squared norm four in \(U^*\); they belong to \(U\), since the discriminant plane is anisotropic and their norm is even. They contribute at least \(n_8\) vectors to \(Y_2\), the number of squared-norm-four vectors of \(U\).

For each eligible coclique take its field \(c=-1_C\). At each \(i\in C\) translate by \(d_i=3e_i-Ae_i\); the resulting field of charge 3 has squared labeling norm 39. The translation has zero seven-class (it corresponds to \(u_i\)), so remains in the same eligible class at seven. It has a unique \(+2\) at \(i\), since \(C\) is independent; knowing \(i\) recovers \(c\). Thus these fields yield \(22M\) distinct vectors plus their negatives in \(U\), again by even squared norm four and anisotropy. The original \(462\) signed triangle marks are already in the graph lattice, are distinct, and in positive charge have unit norm-39 labels: \(+1\) on their triangle, \(-1\) at each adjacent exterior vertex. Hence no translated field replicates one of these original marks; the neutral differences are distinct from both charge-three families.

Combining the three disjoint counts and \(n_{15}\le W_{0,14}\) gives
\[
Y_2+2W_{0,14}\ \ge\ 462+41M+\frac59M^2.
\tag{1}
\]
In particular, using \(5(M-70)^2\ge0\), the linear expression
\[
T=9(Y_2+2W_{0,14}-462-41M)-700M+24500
\tag{2}
\]
is nonnegative in every \(H\), and hence in their mean.

## 2. The rank-36 averaged moment contradiction

Write \(X_j\) for the number of \(v\in U^*\) with \(7\|v\|^2=2j\); the determinant-49 anisotropic plane gives \(Y_j=X_{7j}\). Using the [weight-22 scalar basis](../../maximal-marked-lattice/README.md#arithmetic-checks-at-the-remaining-ranks) and determinant-49 Fricke scaling, the companion checker rederives
\[
Y_2=1000-8X_7+25X_8+11X_9+8X_{10}+3X_{11}+X_{12}.
\]
For any \(j\), the charge dictionary keeps just charges \(0,\pm3\) on \(U^*\), since \(U\) contains \(3u_0\), and the marked index-three sublattice \(D\) has \(U=D+\mathbb Z(3u_0)\). The relevant label squared norms are \(2j\) at charge 0 and \(2j+11\) at charge 3. At nonzero seven-value each shell contributes eight times its \(W\) count to \(X_j\), and positive charge is doubled to include its opposite. For the present branch \(N_{16},N_{20}\) vanish because they are unit-only; the charge-three terms for \(j\le10\) vanish by \(2j+11<33\). Thus
\[
(X_7,X_8,X_9,X_{10},X_{11},X_{12})
=(W_{0,14},0,8W_{0,18},0,8W_{0,22}+16W_{3,33},8W_{0,24}+16W_{3,35}).
\tag{3}
\]
The same linear equation holds after averaging. From now on \(W\) and \(T\) denote their means.

For the three selected unit columns \((0,18),(0,24),(0,26)\), the exact nine-row system of [the original screen](rank36_three_types.py) gives \(E=0\), with
\[
\begin{split}
E={}&-148962W_{0,0}-3207W_{0,14}+6396W_{0,18}
-648W_{0,22}-216W_{0,24}+3207W_{2,22}\\
 &-11W_{2,32}-1296W_{3,33}-756W_{3,35}-1199W_{4,44}.
\end{split}
\]
The four unit subtractions are already in that system. In particular unselected *unit* \((1,27)\) vanishes, not necessarily the corresponding whole shell, whose \(9N_{18}\) nonunit contribution is retained.

Since \(W_{0,0}=1\), combining (2), (3), and \(E=0\) gives
\[
3T+E=-60936+8772W_{0,18}-3369W_{0,14}-11W_{2,32}-324W_{3,35}-1199W_{4,44}.
\]
The [norm-18 bound when norms 16 and 20 are absent](panel-heights.md#a-rank-36-consequence-if-norm-18-occurs) gives the actual graph count \(G_{0,18}\le16,166\). Its nonzero seven-value implies \(W_{0,18}=G_{0,18}/2402\) after averaging. All other displayed population terms are nonnegative, so
\[
0\le3T=3T+E
\le -60936+8772\frac{16166}{2402}
=-\frac{2280060}{1201}<0 .
\]
This contradiction leaves at most six of the original 220 exactly-three-selected-type alternatives at rank 36. Run `python3 rank36-coclique-tangent.py` in this directory with python-flint to verify both row identities and the rational inequality. No numerical optimization is used.
