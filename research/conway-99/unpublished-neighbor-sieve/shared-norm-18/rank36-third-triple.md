# Rank 36 excludes the three-unit alternative (0,26), (1,25), (1,27)

This excludes a single population alternative in [PR #271](https://github.com/mxym/math/pull/271). It does not exclude rank 36 or Conway 99. The proof combines two already valid moment systems, with an exact rational coefficient identity rather than a numerical optimum.

In the notation of the PR, \(W\) denotes the extension-average population; at the nonisotropic shell types used below, \(W_{a,t}=G(a,t)/2402\), while \(W_{0,0}=1\). Use the nine rows returned by \(\texttt{short\_equations()}\) in [rank36_three_types.py](rank36_three_types.py). Normalize each row by its first nonzero coefficient (the RREF pivot). On the allowed columns for \(\{(0,26),(1,25),(1,27)\}\), the linear combination
\[
(-266,\ 0,\ 168,\ -116,\ 36,\ 12,\ -8,\ 0,\ 18)
\]
of these normalized rows is
\[
12W_{0,22}+24W_{3,33}+26W_{3,35}+18W_{4,44}+8W_{2,32}=266W_{0,0}.
\]
The exact short row computation already includes the four published unit subtractions. In this branch \(N_{16},N_{18},N_{20},N_{24},G(1,21),G(2,26)\) vanish, so the selected \(G(1,25),G(1,27),N_{26}\) are their unit populations. No unselected nonunit population is incorrectly set to zero.

For the [rank-44 scalar forms](../../maximal-marked-lattice/README.md#arithmetic-checks-at-the-remaining-ranks), \(x_j\) counts vectors in the original dual \(L^*\) with \(7\|v\|^2=2j\), and \(y_j\) counts squared-norm \(2j\) vectors of \(L\). The [evaluation correspondence](../affine-witness.md#an-exact-count-for-each-rank) has \((v,u_i)=b_i+a/9\). Since \(L\) is obtained from the difference lattice by adjoining \(3u_0\), the required integrality of \((v,3u_0)=3b_0+a/3\) selects \(a=0,\pm3\) among the centered representatives modulo nine. Tightness gives \(7\|v\|^2=t-11a^2/9\). Thus \(x_j=N_{2j}+2G(3,2j+11)\). At \(j=7,8,9,10\) the charge-three contribution vanishes because \(t\le31<|\sum_i b_i|=33\). In the present branch \(N_{16},N_{18},N_{20},N_{24}\) vanish as those shells are unit-only. Therefore \(x_7=N_{14}\), \(x_8=x_9=x_{10}=0\), \(x_{11}=N_{22}+2G(3,33)\) and \(x_{12}=2G(3,35)\). Converting the short moment identity to oriented graph counts yields
\[
12x_{11}+13x_{12}+18G(4,44)+8G(2,32)=638932.
\]
On the other hand the rank-36 two-cusp identity is
\[
35x_7+25x_8+11x_9+8x_{10}+3x_{11}+x_{12}
=343(y_2+988+43y_1)-1988.
\]
The [marked-vector bound](../../rank-34-short-support/README.md) gives \(y_2\ge462\), and the [Fano packing bound](../../short-support-packing/README.md#the-fano-configuration-is-determined-by-three-vertices-of-one-sign) gives \(N_{14}\le990\). With \(y_1\ge0\), the scalar identity forces
\[
3x_{11}+x_{12}\ \ge\ 343(462+988)-1988-35\cdot990=460712.
\]
Thus \(12x_{11}+13x_{12}\ge1842848>638932\), contradicting the first identity since the other terms are nonnegative.

Run `python3 rank36-third-triple.py` from this directory with python-flint. It checks the short rational row combination and rederives the scalar identity on the complete weight-22 level-seven cusp-pair basis with \(x_1=\cdots=x_6=0\), using the rank-36 Fricke scaling \(7^{11-(44-36)/2}=7^7\). No numeric optimization is used.

This is the third extra exclusion beyond the original 210, leaving at most seven of the 220 exactly-three-type rank-36 alternatives.
