# Rank 36 forces norm 16, 18 or 20 and at least four selected types

Every Conway 99 candidate of Seidel rank 36 over the field of seven elements has an integral neutral label of squared norm 16, 18 or 20. When norm 20 is absent, it satisfies the stronger population bound
$$
17150 N_{16}+4459 N_{18}\ge 9{,}319{,}996.
$$
Here $N_t$ counts both orientations of vectors $b$ on the 99 graph vertices with $Ab=-4b$ and $b^tb=t$. These three shells have only signed unit entries on their supports. The result holds with any number of other short types present, for every grid count and without an automorphism assumption.

The [two primal-lattice exclusions](rank36-primal-local-cuts.md) together with the [graph-wide coclique calculation](rank36-primal-global-sidon-cut.md) left just the triple $(0,26),(2,28),(2,30)$ from the original 220 exactly-three-type alternatives. It contains none of these three neutral norms. Thus rank 36 needs **at least four** of the [twelve selected unit types](../short-shell-moments.md#when-the-nonzero-labels-must-all-be-signed-units).

## Two Fano supports on the same square force norm 20

Write $N_t$ for the number of oriented integral neutral labels of squared norm $t$. If $N_{20}=0$, then **$N_{14}\le198$**.

A norm-14 support has two independent seven-sets as its sign classes. Each vertex sees four on the other side, and two on one side have precisely two common neighbors, both on the other side. Three specified sites of one sign determine the whole oriented label. These are properties of the [complement-of-Fano incidence graph](../../short-support-packing/README.md#the-fano-configuration-is-determined-by-three-vertices-of-one-sign).

Suppose distinct supports contain the same square. Orient their labels $b,b'$ to agree on that square. They have exactly two common positives and two common negatives, as a third common vertex of either sign would identify the labels. A positive of $b$ which is negative in $b'$ sees neither common negative. In the Fano support of $b$ the two common negatives together see $4+4-2=6$ of its seven positives. Thus there is at most one such conflicting site. Interchanging the signs gives at most one more. If there are $c$ conflicts, then $b\cdot b'=4-c$ and $\|b-b'\|^2=20+2c\le24$.

A neutral label of squared norm at most 24 has no entry of magnitude two or greater. Indeed, orient such an entry to be at most $-2$ and add the site label $3e_i-Ae_i$. This gives a charge-one label of squared norm at most $24+23-28=19$, excluded by the [charge-one minimum](../affine-witness.md). A conflict would give an entry of magnitude two in $b-b'$. Thus $c=0$ and the difference is a norm-20 label.

Every pair of nonadjacent sites determines a square on its two common neighbors. Those neighbors are nonadjacent because an adjacent pair has only one common neighbor. Counting opposite pairs gives $99\cdot84/4=2079$ squares. Each Fano support contains exactly $\binom72=21$ of them, one per pair of positives. When $N_{20}=0$ they belong to different supports, so $21N_{14}/2\le2079$. The factor two counts the two orientations of each support.

## One coefficient identity in the original graph lattice

For the rank-44 graph-generated lattice $L$, write $x_j,y_j$ for the numbers of vectors of squared norm $2j$ in $\sqrt7 L^*$ and $L$ respectively. Then $x_0=y_0=1$ and $x_1=\cdots=x_6=0$. On the next four shells, $x_7,x_8,x_9,x_{10}$ equal $N_{14},N_{16},N_{18},N_{20}$. Indeed the [dual labeling dictionary](rank36-primal-local-cuts.md) permits charges $0,\pm3$, and the charge-three minimum is 33 while the squared labeling norms $2j+11$ here are at most 31.

At rank 36 the original level-seven theta pair satisfies
$$
\begin{aligned}
57967 x_7 +17150 x_8 +4459 x_9 +637 x_{10}
={}&343(68y_2+3y_3)+119021 y_1+49 x_{12}\\
 &-32002243 x_0-4079299 y_0 .
\end{aligned}
$$
One way to obtain the weights 68 and 3 is to cancel $x_{11}$ between the weight-22 identities for $343y_2$ and $343y_3$. The [checker](rank36_four_types.py) verifies this single homogeneous identity directly on every applicable basis direction. It takes the [level-seven Fourier basis](../../maximal-marked-lattice/verify.py), uses the original rank-36 Fricke scale $7^7$, and sets the first fifteen $x$-coefficients to the coordinate unit vectors by back substitution. The directions with indices $0,7,\ldots,14$ span the subspace with $x_1=\cdots=x_6=0$.

Use the 462 signed triangle marks in the squared-norm-four shell and the [unconditional bound of 44,804](../../rook-array-exclusion/rectangle-class-forest.md) in the squared-norm-six shell. Dropping $119021y_1+49x_{12}\ge0$ gives
$$
57967N_{14}+17150N_{16}+4459N_{18}+637N_{20}\ge 20{,}797{,}462 .
$$
When $N_{20}=0$, the square bound limits the first term to $57967\cdot198=11{,}477{,}466$. Subtraction gives the claimed inequality. In particular if $N_{16}=N_{20}=0$, there are at least 2,092 oriented norm-18 labels, using their even count. If $N_{18}=N_{20}=0$, there are at least 544 oriented norm-16 labels.

The qualitative exclusion also follows from the older [squared-norm-six bound of 41,058](../../rank-34-exclusion/README.md), which still gives $17150N_{16}+4459N_{18}\ge5{,}465{,}362$ when norm 20 is absent. Run `python3 rank36_four_types.py` with the standard library. It checks the finite Fano incidences, the theta identity and both versions of the inequality. Rank 36 with four or more selected types and the other three ranks remain open.

The [Fano difference-packing inequalities](fano-difference-packing.md) strengthen the square estimate quantitatively, also when norm 20 is present.
