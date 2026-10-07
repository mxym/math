# Coupled upper-end stability: a cone-law obstruction to a linear volume gate

This note is separate from the completed upper-end stability supplement. It
contains proved gate obstructions and one explicitly unproved route. No claim
of an improved global exponent is made here. The separate matching and
geometry notes improve the matching and containment gates, respectively.

## 1. Precise obstruction under the selected-basis intermediate hypotheses

Let `0<e<=1/2` and put

\[
 Q_e=[-1,1]^3\cap\{|x_1+e x_2|\le1,\ |x_2+e x_3|\le1\}.
 \tag{1.1}
\]

The body is centrally symmetric and full-dimensional, with
`(1-e)[-1,1]^3 subset Q_e subset [-1,1]^3`. Its cone law has five direction
pairs

\[
 \pm z_1=\pm e_1,\quad \pm z_2=\pm e_2,\quad \pm z_3=\pm e_3,
 \quad \pm z_4=\pm(1,e,0),\quad \pm z_5=\pm(0,1,e).
 \tag{1.2}
\]

Write `p_i` for the probability of the entire pair, with uniform signs inside
each pair. Define

\[
\begin{aligned}
 V_e&=8-4e+e^2-e^3/3,\\
 C_1=C_4&=2-e/2,\qquad C_2=2-e,\\
 C_3&=4-3e+e^2-e^3/2,\qquad C_5=2-e+e^2/2,\\
 p_i&=2C_i/(3V_e).
\end{aligned} \tag{1.3}
\]

In particular `sum p_i=1`, `p_4,p_5>=1/8`, and

\[
 (p_1,p_2,p_3,p_4,p_5)\longrightarrow(1/6,1/6,1/3,1/6,1/6).
 \tag{1.4}
\]

Let `phi` be the fourth-largest absolute cofactor of a four-sample tuple, and
let `A=E|det(X_1,X_2,X_3)|`. Exact enumeration gives

\[
 \mathbb E\phi=24p_1p_3p_4p_5e^2\sim e^2/27,
 \tag{1.5}
\]

\[
\begin{aligned}
 A=6[&p_1p_2p_3+e p_1p_2p_5+e p_1p_3p_4+p_1p_3p_5\\
     &+e^2p_1p_4p_5+p_2p_3p_4+e p_2p_4p_5+p_3p_4p_5]
      \longrightarrow2/9,
\end{aligned}\tag{1.6}
\]

and the scalar upper-end deficit is

\[
 \delta_e=\tfrac12-a(Q_e)
     =\frac{3p_1p_3p_4p_5e^2}{A}\sim e^2/48.
 \tag{1.7}
\]

For the basis `U=I`, the simultaneous section cost used in the matching lemma
is exactly

\[
 Q(U)=\int\phi(e_1,e_2,e_3,x)\,d\nu(x)
   +\sum_{j=1}^3\iint\phi(e_1,\ldots,\widehat e_j,\ldots,e_3,x,y)
                      \,d\nu(x)d\nu(y)
       =2p_4p_5e^2\sim e^2/18.
 \tag{1.8}
\]

Let `W` be any coordinate partition into lines and planes, and let
`P_W=product_j proj_(W_j) Q_e`. All four possible partitions satisfy

\[
\begin{aligned}
 v_W&:=\mathbb E_{\nu_{Q_e}}[h_{P_W}(X)-1]\\
 &=\mathbb E_{\nu_{Q_e}}\operatorname{dist}(X,\bigcup_j W_j)
 \in\{p_4e,p_5e,(p_4+p_5)e\},\\
 \min_W v_W&=e\min(p_4,p_5)\ge e/8.
\end{aligned}\tag{1.9}
\]

Thus neither a coordinate-block mean-distance estimate nor a coordinate-block
mixed-volume-surplus estimate with exponent greater than `1/2` in `Q(U)` can
hold under these hypotheses. In particular, the tempting replacement

\[
 \min_W v_W\le C\mathbb E\phi
 \quad\hbox{or}\quad
 \min_W v_W\le C\delta_e
 \tag{1.10}
\]

is false for this uniformly nondegenerate family. These particular support
calculations concern the prescribed basis and its coordinate partitions.
Section 3 gives separate proofs for arbitrary block choices and for distance
to the entire affine equality class; neither follows merely from (1.9).

The unit-ball hypothesis of the matching lemma is obtained without changing
the obstruction. Put `c=sqrt(1+e^2)`, replace `Q_e` by `c Q_e`, and choose the
basis with columns `e_i/c`. Every cone-law sample then has norm at most one,
the basis determinant is `c^(-3)>= (5/4)^(-3/2)`, its coordinate law remains
exactly (1.2), and its transformed primal body remains `Q_e`. The section cost
and `E phi` are simply divided by `c^3`. Its determinant expectation remains
bounded below by a positive constant. Consequently the example meets the
bounded-law, determinant, simultaneous-section, and controlled-basis
hypotheses with constants independent of `e`.

## 2. Proof of the formulas

Fix `u=x_2`. The allowed `x_1` interval has length `2-e|u|`. The allowed
`x_3` interval has length `2` if `|u|<=1-e`, and length
`1+(1-|u|)/e` otherwise. Therefore

\[
 |Q_e|=2\int_0^1(2-eu)
     \begin{cases}2,&u\le1-e,\\1+(1-u)/e,&u>1-e\end{cases}
          du=V_e.
\]

On the positive `x_1=1` facet one has `-1<=u<=0`, giving area `2-e/2`.
On the positive `x_2=1` facet the allowed `x_1` and `x_3` lengths are
`2-e` and `1`, respectively. On the positive `x_3=1` facet one integrates
`2-e|u|` over `-1<=u<=1-e`, giving `C_3`. These coordinate facets have
support number one.

The positive new facet `x_1+e x_2=1` is parametrized by
`x_1=1-eu`, `0<=u<=1`, and its allowed `x_3` interval. Its area-normal vector
is `C_4(1,e,0)`; its area times support number is `C_4=2-e/2`.
The other positive new facet has `x_2=1-e x_3`, `0<=x_3<=1`, and `x_1`
length `2-e+e^2x_3`. Its area-normal vector is `C_5(0,1,e)`, with area times
support number `C_5`. These calculations prove the cone masses in (1.3).
They also give `sum C_i=3V_e/2`, as required by the divergence theorem.

For four samples to have four nonzero cofactors, their four distinct direction
types must be `{1,3,4,5}`. Every other type set has a zero cofactor, and any
repeated type also produces at most three nonzero cofactors. For the exceptional
type set the cofactor magnitudes are

\[
 (1,1,e,e^2).
\]

Its fourth absolute cofactor is `e^2`. Its unnormalized balanced Rademacher
defect is exactly

\[
 \frac{2+e+e^2}{2}
 -\mathbb E|\epsilon_1+\epsilon_2+e\epsilon_3+e^2\epsilon_4|
 =\frac{e^2}{2}.
\]

Indeed, equal signs on the first two terms contribute mean absolute value
`2`, and opposite signs contribute mean absolute value `e`; both cases have
probability one half. All other tuples have zero defect by the balanced
three-support equality. The probability of the exceptional four-type set is
`24p_1p_3p_4p_5`. Equations (1.5) and (1.7) follow, using
`Delta=4A delta`. Enumerating the ten three-type sets gives (1.6).

For (1.8), the one-sample section vanishes because every sample is at most
two-sparse. Among the two-sample sections, only the one omitting `e_2` can
have four nonzero cofactors; its two additional types must be `4,5`, in either
order. Its fourth cofactor is `e^2`, giving the formula.

Every coordinate projection has both axis support numbers equal to one.
The projection onto the `12` plane preserves the first new inequality,
and the projection onto the `23` plane preserves the second. Thus the
`12|3` product has support surplus zero at `z_4` and `e` at `z_5`; the
`1|23` product has the opposite behavior. At the `13|2` product and the
all-line product both new normals have surplus `e`. All axis normals have
surplus zero. The Euclidean distances to the block unions are precisely the
same: an unhandled pair has a tail of length `e` and all handled pairs have
distance zero. This proves (1.9).

## 3. What this says about a coupled proof

### Sharp square-root matching even with arbitrary block choices

The mean-distance obstruction is stronger than the fixed-coordinate statement.
It persists if the line and plane blocks, and the sampled basis, can be chosen
freely. The following elementary finite-set lemma makes this precise.

**Finite-set lemma.** Let `d>=3`, `0<e<=1/2`, and let
`R^d=direct_sum W_j`, with `dim W_j` equal to one or two. For

\[
 \mathcal Z_e=\{e_1,\ldots,e_d,e_1+e e_2,e_2+e e_3\}
\]

one has

\[
 \max_{z\in\mathcal Z_e}\operatorname{dist}(z,\bigcup_jW_j)
       \ge\frac{e}{6\sqrt d}. \tag{3.2}
\]

**Proof.** Suppose the maximum is `r<e/(6 sqrt d)`. Assign each axis vector
to a nearest block and choose `w_i` in that block with `|w_i-e_i|<=r`.
Let `T` have columns `w_i`. Then `||T-I||<=sqrt d r=:eta<1/12`, so `T`
is invertible. The number of assigned axis indices in each block is at most
its dimension. Summing the numbers and dimensions gives `d` on both sides;
therefore the assigned index sets `J_j` partition the axes, have sizes one
or two, and `W_j=T span{e_i:i in J_j}`.

For `y` in `W_j`,

\[
 |\operatorname{proj}_{J_j^c}y|
       \le\frac\eta{1-\eta}|y|.
\]

Take `y` to be the orthogonal projection of an arbitrary `z` onto `W_j`.
Since `|y|<=|z|`, the triangle inequality gives

\[
 \operatorname{dist}(z,W_j)
 \ge\operatorname{dist}(z,\operatorname{span}J_j)
          -\frac\eta{1-\eta}|z|.
\]

The two edges `12` and `23` cannot both be contained in blocks of a partition
whose block sizes are at most two. For the corresponding uncontained edge
vector `z`, its distance to every coordinate block is at least `e`.
Since `|z|<=sqrt(5/4)`, its distance to every actual block is at least
`e-3 sqrt(d) r>e/2>r`, a contradiction. This proves (3.2).

For every dimension, take the actual cone body

\[
 K_{e,d}=Q_e\times[-1,1]^{d-3}. \tag{3.3}
\]

Its cone law has the five three-dimensional direction-pair masses
`(3/d)p_i`, and mass `1/d` on each additional coordinate-axis pair. All
`d+2` masses are at least `3/(8d)`. Applying (3.2) therefore yields

\[
 \inf_{(W_j)}\mathbb E_{\nu_{K_{e,d}}}
              \operatorname{dist}(X,\bigcup_jW_j)
       \ge\frac{e}{16d^{3/2}}. \tag{3.4}
\]

The determinant and fourth-cofactor expectations are exactly

\[
 A_d=\frac{d!\,27}{6d^d}A,
 \qquad
 \mathbb E\phi_d=\frac{(d+1)!\,81}{d^{d+1}}
                 p_1p_3p_4p_5e^2
       \sim\frac{(d+1)!}{8d^{d+1}}e^2. \tag{3.5}
\]

For the first formula, a determinant needs one sample on each additional
coordinate axis and three independent samples in the first three-dimensional
subspace. For a positive fourth cofactor, a `(d+1)`-tuple needs one sample
on every additional axis and the four exceptional types `{1,3,4,5}` in that
subspace. Its four nonzero cofactors have magnitudes `(1,1,e,e^2)`, with all
other cofactors zero. This proves (3.5) by ordered-type counting. The scalar
deficit is

\[
 \delta(K_{e,d})=(3/d)\delta_e\sim e^2/(16d), \tag{3.6}
\]

either by the dimension-weighted product identity or by the same exact
defect count. The section cost at the axis basis is
`18 p_4 p_5 e^2/d^2`.

Scaling by `c=sqrt(1+e^2)` puts the entire cone law in the unit ball.
Every basis matrix formed from its samples has `||U||<=sqrt d`. If its
coordinate blocks are `W'_j`, their original blocks are `U W'_j`, and

\[
 \operatorname{dist}(U^{-1}X,\bigcup_j W'_j)
 \ge \frac{1}{\sqrt d}
           \operatorname{dist}(X,\bigcup_j UW'_j).
\]

Consequently (3.4) gives a coordinate mean lower bound
`e/(16 c d^2)` for **every** invertible sampled basis and every line/plane
partition. The bounded-law determinant mass has an explicit uniform lower
bound: using `p_i>=1/8` and `A>=6p_1p_2p_3>=3/256`, one obtains

\[
 A_d/c^d\ge
   \frac{27d!}{512d^d(5/4)^{d/2}}. \tag{3.7}
\]

It follows that, in every fixed dimension `d>=3`, no exponent greater than
`1/2` can replace the square-root exponent in a mean-distance matching lemma
under its actual hypotheses, even when the law is required to be the cone
law of a uniformly nondegenerate symmetric body and the block decomposition
can be chosen freely.

### The discrepancy is also linear in distance to the entire product class

The same family satisfies a full-class geometric estimate:

\[
 \boxed{\frac{e}{120\sqrt d}
       \le D(K_{e,d},\mathcal E_d)-1
       \le\frac{e}{1-e}\le2e.} \tag{3.8}
\]

This does not improve the existing `1/d` obstruction, since here the scalar
deficit is of order `e^2`. It shows, however, that the matching square-root
loss can reflect an actual first-order product discrepancy, rather than
only a badly chosen coordinate presentation.

We use a general elementary flat-facet observation. Suppose a full-dimensional
body `K` has a facet with unit normal `n`, support number `h>0`, and a
Euclidean tangent disk of radius `rho` contained in the facet. If
`K subset E subset (1+s)K`, the upper boundary of `E`, over that disk and
in direction `n`, is the graph of a finite concave function with height in
`[0,sh]` above the facet plane. At a differentiability point in the
concentric disk of radius `rho/2`, its gradient has norm at most
`2sh/rho`: restrict the concave function to each tangent line, and compare
its derivative with secants to points at distance `rho/2` on either side.
Such differentiability points exist by local Lipschitz continuity of finite
concave functions. Their outward unit normal `n_E` satisfies

\[
 \operatorname{dist}(n,\operatorname{span}n_E)
       \le\frac{2sh}{\rho}. \tag{3.9}
\]

If `E` is an affine product of line and plane factors, every regular outward
normal of `E` lies in one of its dual blocks, a direct-sum partition into
subspaces of dimensions one and two. Indeed, if two primal factors were
on their boundaries at a point, their nonzero normal cones would give at
least two independent normal rays; that point could not be regular.
At a regular point exactly one factor is on its boundary, and its normal
annihilates all the other primal blocks.

For `Q_e`, tangent disks of radius `rho=1/10` lie in its five positive
facets, with centers

\[
 (1,-1/2,0),\quad(0,1,-1/2),\quad(0,0,1),\quad
 (1-e/2,1/2,0),\quad(0,1-e/2,1/2).
\]

For the two new facets the disk is taken in their actual tangent planes.
All disks satisfy the remaining inequalities with room to spare for
`e<=1/2`. In `K_{e,d}`, use the same centers with zero extra coordinates;
the radius-`1/10` disks in the full `(d-1)`-dimensional tangent planes remain
inside the corresponding facets. Each additional coordinate facet also
contains such a disk centered at its coordinate-axis endpoint. All facets
in question have the scaled normals in `Z_e`, namely `z=n/h`.

For any `E in E_d` with `K_{e,d} subset E subset (1+s)K_{e,d}`, (3.9)
therefore puts every `z in Z_e` within

\[
 (1/h)(2sh/\rho)=20s
\]

of the union of `E`'s dual line/plane blocks. Equation (3.2) forces
`20s>=e/(6 sqrt d)`. Every Banach–Mazur sandwich can be rescaled to this
form, and taking its infimum proves the lower bound in (3.8), without any
attainment assumption. Finally
`(1-e)[-1,1]^d subset K_{e,d} subset [-1,1]^d` gives the upper bound.

### A joint geometric gate remains necessary

The family has deficit of order `e^2` and a ridge-scale geometric discrepancy
of order `e`. It does not threaten the conjectured optimal dimension-three
power `1/3`, since `e` is smaller than a constant times `delta^(1/3)`.
Instead it shows why it is unsafe to strengthen the final volume gate by
inserting a square into the mean-distance estimate. The small determinant
factor `e^2` is compensated by geometry spread over a ridge, whose cap-volume
scale has exponent two rather than three.

By contrast, the three-coordinate corner truncation has
`E phi` of order `t^2`, `delta` of order `t^3`, and support surplus of order
`t^3`. In that case the half-mass gate and a support-Lipschitz estimate lose
a factor which the actual support cost already contains. The two families
show different gates becoming active. The separate extreme bounds cannot be
assumed to saturate on one body.

There is a useful exact weighted estimate. For the normalized cofactor tuple,
let `g=1/2-t_1` and `phi=M t_4` on `M>0`, and define `g=phi=0` on `M=0`.
Since `t_4<=1/4` and `g<=1/2` on `M>0`, Lemma 3.1
of the completed proof implies

\[
 t_4g\le\min(t_4/2,g/4)\le\mathscr D(t),
 \qquad \boxed{\mathbb E[\phi g]\le NA\delta.}
 \tag{3.1}
\]

This carries no power loss, but it cannot replace the omitted-basis matching
cost by itself. Matching consistency must still be proved using a geometric
cost which treats a shallow long circuit and two overlapping nearly-axis
pair directions differently.

An unproved route toward the optimal `1/d` is to produce a geometric witness
at a product-containment defect `t`, classify the support involved by its
active block dimension, and show that the cone-law masses times the circuit
defect are at least `c_d t^r` for some `r<=d`. A proof must account for
determinant factors, the normal-angle factors in localized facet mass, and
non-polyhedral contact patches together. Merely optimizing the independent
mean estimates does not establish such a statement. No complete lemma of
this form is proved in this note.

## 4. Exact finite verification

`check_global_slanted.py` replays the cone-mass identity, the determinant
expectation, all 625 ordered direction-type four-tuples with their 16 sign
averages, all simultaneous two-sample sections, and the four block costs,
at eight rational values of `e`. It also checks the product determinant,
fourth-cofactor and scalar-deficit formulas in 32 cases across dimensions
three through six. It uses exact rational arithmetic and
exceptions rather than Python assertions. The finite checks support the
displayed identities; the all-parameter proof is the algebra above.

The finite-set lemma, facet disks, and flat-facet geometric argument in
Section 3 also received a separate analytical audit, with no gap found.
This is model-assisted mathematical review, not external peer review or
formal certification; the exact tests are not used to establish these
geometric arguments.
