# Two mixed quadratic identities for the actual graph centroids

These vector identities hold in **every** determinant-49 terminal extension $H$ of the graph lattice, at any of the four remaining seven-ranks. Fix $H$. For each raw positive-charge species $G_{a,t}$, take its $H$-eligible actual fields $b$ of charge $a$ and cost $t$. Write
$$
 m_{a,t}=\frac1{s_{a,t}}\sum_b (b+(a/9)\mathbf1),\qquad
 s_{a,t}=\begin{cases}1,&9t-11a^2=0\bmod7,\\8,&\text{otherwise.}\end{cases}
$$
This is a vector in the real $-4$ graph eigenspace, or equivalently a list of 99 exact pointwise identities. Nonisotropic $s=8$ is a gluing average, not an assertion of equal populations. Abbreviate $m_{a,t}$ by its three-digit code. Then
$$
-3m_{121}+m_{123}+m_{125}-m_{127}
+4m_{226}-2m_{228}-m_{230}-m_{333}+m_{335}-m_{337}-m_{444}=0,
$$
$$
-32m_{121}+7m_{123}+6m_{125}-8m_{127}+m_{129}-7m_{222}
+38m_{226}-19m_{228}-6m_{230}+9m_{335}-9m_{337}-9m_{444}=0.
$$

**Proof.** In the rank-48 even unimodular gluing, take the product of one linear form on the 44 graph coordinates with one on the four auxiliary coordinates. This quadratic is harmonic because the two factors live in orthogonal summands. Its squared-norm-four sum plus 48 times its squared-norm-two sum vanishes: its weighted theta series is a weight-26 cusp form, proportional to $\Delta E_{14}$. The graph linear form can be evaluation at any graph mark, giving the centered entry $b_o+a/9$. Use the nontrivial three-shift auxiliary gluings. For an auxiliary direction $h$ the pairing at numerator $w$ is $(w\cdot h)/3$. Average over all sixteen isometries of the residual seven-plane. In a nonzero norm circle of eight signed residues, each compatible residue has the same weight $1/8$; a zero residue has weight one. For neutral species the averaged graph centroid vanishes by negation. For nonzero charge the two charge signs yield the same product, so the common factor $2/3$ can be dropped.

The [exact checker](rank48_pointwise_centroids.py) uses the exact auxiliary numerator enumeration already present in higher_moments.py. For shift $B=(-1,1,-1,1)$ and $h=(0,0,0,1)$, its raw integer coefficient row is three times the first displayed row $R_1$. For $h'=(0,1,1,0)$ and $A=(-2,1,0,0)$ the second is $18R_1-R(A,h')-2R(B,h')$, where $R$ denotes the integer numerator row. These are rank-48 mixed moments, not a transfer based only on scalar total populations.

**The rank-42 three-type face.** If the selected unit support is contained in $\{026,228,230\}$, the raw $121,125,127,226,337$ terms all vanish (in particular both sources $018,226$ of nonunit $127$ vanish). Write $B_{a,t}=\sum_b(b+(a/9)\mathbf1)$ in ordinary whole-graph counts, *not* normalized. Then
$$
 B_{333}+B_{230}+2B_{228}+B_{444}=8B_{123}+B_{335},
$$
$$
 B_{129}=-56B_{123}+56B_{222}-9B_{335}+9B_{444}
                         +19B_{228}+6B_{230}.
$$
Here $123$ and $222$ are the isotropic species among these terms, so they are not divided by eight. Whole-graph scope is justified because at rank 42 the original discriminant space is already the terminal plane.

For instance on the *additional* extremal slice $B=M=S=h=0$ in [the mass bridge](rank42-equitable-mass.md), the raw totals $G_{333},G_{228}$ are 404,784. The same scalar chart gives $G_{230}=1732$ (verification in the companion below). The raw $123$ fields are exactly the 99 graph columns, whose **centered** vector sum vanishes. For each site $o$ the first identity is therefore
$$
 \#\{T\in G_{3,33}:o\in T\}
   =868+\sum_{b\in G_{2,30}}b_o+2\sum_{b\in G_{2,28}}b_o .
$$
Indeed the centered constant is $404/3+(2/9)(1732+2\cdot784)=868$. Also $B_{129}=7B_{228}-6B_{333}$ on this slice. The identities do not by themselves exclude the slice or the whole rank.
