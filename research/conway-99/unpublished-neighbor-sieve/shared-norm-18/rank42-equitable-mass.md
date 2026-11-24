# Three coupled literal shell counts on a charged rank-42 face

Assume seven-rank 42, with selected unit support contained in $\{(0,26),(2,28),(2,30)\}$. This is a necessary condition, not an exclusion. Write $B=N_{14}$, $M=G_{2,22}$, $S=G_{1,23}-99-7B$ and $h=G_{3,35}+G_{4,44}$. All are **literal whole-graph** counts, not counts divided by eight. The neutral labels $B,N_{26}$ include both signs; a positive-charge label is counted only at the specified positive charge. Then:
$$
\begin{aligned}
2G_{3,33}&=808+16(M+S)+96B+h,\\
G_{2,28}&=784+8S+56B+h,\\
N_{26}&=4680+40(M+S)+296B+3h .
\end{aligned}
$$
In particular a graph on this face has at least 404 equitable 33-sets, 784 unit $(2,28)$ labels and 4,680 oriented unit neutral norm-26 labels.

These are affine identities, not fitted minima. The [companion exact checker](rank42_equitable_mass.py) reduces the three exact rows modulo the common equations of original_site_populations.py and the nine forbidden **unit** families. It evaluates raw graph quantities with that chart's global map $G$, not directly with its $W$ function. In this determinant-49 case every isotropic residue is zero, so the isotropic $W_{0,14},W_{1,23},W_{2,22}$ are literal counts; in contrast the nonisotropic normalized quantities $W_{3,33},W_{3,35},W_{4,44},W_{2,28},W_{0,26}$ are one eighth of their respective graph masses. For $N_{26}$ the raw nonunit correction $8G_{1,21}$ vanishes because the selected $(1,21)$ family is absent; no correction applies to $(2,28)$. The unit support exclusions also imply zero raw $(1,25),(1,27)$ since their shorter sources $(0,16),(0,18),(2,26)$ vanish. The independent types $B,M,S,h$ in the displayed right-hand sides need not vanish; $S$ counts unit noncanonical graph fields after the 99 graph columns and seven translations per oriented Fano. A $(3,33)$ field is exactly $-1_T$ on a 33-site set with $A1_T=6\mathbf 1-4\,1_T$.

A useful direct comparison with no $h$ term is $2G_{3,33}-G_{2,28}=24+16M+8S+40B$; eliminating both large shells gives $N_{26}-3G_{2,28}=2328+40M+16S+128B$. These relations involve the *same graph*. They do not imply that every equitable set has an individual associated $(2,28)$ label, or prove that any graph on the face exists.

The [pointwise mixed harmonic identities](rank48-pointwise-centroids.md) add constraints at each of the 99 individual sites, not just the three total masses. They also apply before restricting the unit support.
