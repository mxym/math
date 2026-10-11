---
title: "Singular loci of rooted tree compartment models"
subtitle: "A recursive resultant formula and the catenary and tree multiplicity conjectures"
author: "Yongxian Zhang"
date: "11 October 2026"
geometry: "margin=1in"
fontsize: 11pt
colorlinks: true
---

**Research status.** This note gives a complete written proof of the polynomial identities and corollaries stated below. It has not been externally peer reviewed or formalized in Lean. The accompanying exact checks are supplementary finite diagnostics, not a substitute for the proofs for arbitrary finite trees. No assertion of worldwide priority is made.

School of Computer Science and Engineering, South China University of Technology. Contact: mxymmxym1@gmail.com. ORCID: 0009-0000-3864-3536. No external funding. AI-assisted research and verification. Separately original material is all rights reserved, subject to any applicable existing repository license; third-party notices are unchanged.

# Abstract

We determine the Jacobian determinant of the input-output coefficient map for every finite bidirected tree with a single input and measured state at the same vertex and a single leak at any fixed vertex. The formula is a product of directed rates toward the leak, powers of bidirectional edge products determined by descendant subtree sizes, and squared resultants of characteristic polynomials of sibling principal submatrices. The latter retain the original diagonal losses to deleted vertices. The proof factors the coefficient map through diagonal and edge-product coordinates and establishes a polynomial-merging Jacobian identity. We also factor the numerator-denominator resultant and relate it directly to the physical-parameter Jacobian. These identities prove the catenary singular-locus formula in Gross--Meshkat--Shiu, Conjecture 5.5, and the exact edge multiplicities of their Conjecture 5.9, attributed there to Hoch--Sweeney--Tung. At strictly positive rates, coefficient-map regularity is equivalent to minimality of the root input-output realization; failure occurs exactly when two sibling subtrees share an eigenvalue, at some vertex. An exact five-compartment example has nine pairwise distinct positive rates but an unobservable mode and singular parameter Jacobian.

# 1. Scope and notation

Let $T=(V,E)$ be an undirected tree with $n\geq1$ vertices. Every edge is present in both directions. Designate a measured/input vertex $r$ and a leak vertex $\ell$, which need not coincide. For adjacent vertices $i,j$, write $a_{ij}$ for the rate **from $j$ to $i$**. Let $\kappa$ be the only leak parameter. There are $2(n-1)+1=2n-1$ independent parameters.

Define the physical compartment matrix

$$
 A_{ij}=a_{ij}\quad(i\sim j),\qquad
 A_{jj}=-\sum_{i\sim j}a_{ij}-\kappa\,1_{j=\ell},
$$

and put all other off-diagonal entries equal to zero. The model is

$$
 \dot x=Ax+e_r u,\qquad y=e_r^{\mathsf T}x.                 \tag{1}
$$

The polynomial results are identities in the independent variables $a_{ij},\kappa$ over $\mathbb Z$, hence also hold for arbitrary real specializations. The physical interior means $a_{ij}>0$ and $\kappa>0$. No sign assumption is used to derive the Jacobian identities.

Write

$$
 P_r(z)=\det(zI-A),\qquad
 Q_r(z)=\det(zI-A)_{\widehat r,\widehat r}.                  \tag{2}
$$

The empty determinant is one. These are monic polynomials of degrees $n$ and $n-1$. The coefficient map $C=C_{T,r,\ell}$ lists all their nonleading coefficients, first those of $P_r$, then those of $Q_r$, in descending degree. Fix any parameter order. Let

$$
 J_{T,r,\ell}=\det DC_{T,r,\ell}.                           \tag{3}
$$

Changing these orders only changes a fixed sign. A $\pm$ sign below always means a sign determined by the chosen orders and tree, **not** one that can vary with the rates.

The formal adjugate identity applied to $\partial I-A$ gives $P_r(\partial)y=Q_r(\partial)u$. With zero initial condition, the transfer function is $Q_r/P_r$. We retain the unreduced polynomial pair at singular parameter values, exactly as in the coefficient-map definition of the singular locus in [GMS]. A singular Jacobian is a differential rank failure; it should not be silently equated with every stronger notion of nonunique inverse at an exceptional point.

Root the tree at $r$. For a nonroot vertex $c$ with parent $v$, let $T_c$ be its full descendant subtree and $s_c=|T_c|$. Define

$$
 f_c=a_{cv},\qquad b_c=a_{vc},\qquad p_c=f_cb_c.
$$

Here $f_c$ points away from the observation root, and $b_c$ points toward it. For every vertex $v$ set

$$
 P_v(z)=\det(zI-A[T_v,T_v]),\qquad
 Q_v(z)=\prod_{c\in\operatorname{Ch}(v)}P_c(z).             \tag{4}
$$

**Boundary convention:** $A[T_v,T_v]$ is a principal submatrix of the original matrix. Its diagonal is not recomputed after deleting the other vertices. In particular, $b_v$ remains a loss term in the diagonal of the top vertex of a proper subtree. Closing a subtree by removing this loss produces different polynomials and invalidates the theorem.

For monic polynomials, use the standard resultant convention

$$
 \operatorname{Res}(F,G)=\prod_{F(\alpha)=0}G(\alpha),
$$

counting multiplicities. Set

$$
 \mathcal B_{T,r}=
 \prod_{v\in V}\ \prod_{\{c,d\}\subseteq\operatorname{Ch}(v)}
            \operatorname{Res}(P_c,P_d)^2.                \tag{5}
$$

For the leak root $\ell$, write $\pi_\ell(v)$ for the parent of $v\ne\ell$ in the tree rooted at $\ell$, and define

$$
 \tau_\ell=\prod_{v\ne\ell}a_{\pi_\ell(v),v},\qquad
 \eta_\ell=\prod_{v\ne\ell}a_{v,\pi_\ell(v)}.              \tag{6}
$$

These are respectively the products of all rates pointing toward and away from the leak. They satisfy $\tau_\ell\eta_\ell=\prod_{c\ne r}p_c$.

# 2. Main identities

**Theorem 1 (all-tree physical Jacobian).** For every finite tree and every choice of $r,\ell$,

$$
 \boxed{
 J_{T,r,\ell}
  =\pm\tau_\ell\prod_{c\ne r}p_c^{\,s_c-1}\,
                  \mathcal B_{T,r}.}                     \tag{7}
$$

The determinant is not the zero polynomial. Thus the singular locus of this square coefficient map is exactly the zero set of (7). The expression is a complete product formula, not a claim that every displayed resultant is irreducible.

**Theorem 2 (transfer resultant).** For the same model,

$$
 \boxed{
 \operatorname{Res}(P_r,Q_r)
 =\pm\prod_{c\ne r}p_c^{\,s_c}\mathcal B_{T,r}
 =\pm\eta_\ell J_{T,r,\ell}.}                            \tag{8}
$$

All statements include zero edge rates by polynomial identity. We are not dividing by $\eta_\ell$ at boundary points. Likewise, specializing $\kappa=0$ is allowed as a point of this parameterized one-leak family, but is not a claim about the different, lower-dimensional model obtained by deleting the leak parameter entirely.

# 3. The polynomial-merging Jacobian

This section proves the algebraic step responsible for the squared resultants.

**Lemma 3 (interpolation determinant).** Let $F_1,\ldots,F_k$ be monic polynomials of positive degrees $m_1,\ldots,m_k$, and put $N=\sum_i m_i$. With monomial coefficient bases, the linear map

$$
 \mathcal S_F:\bigoplus_i\mathbb R[z]_{<m_i}
                 \longrightarrow\mathbb R[z]_{<N},
 \quad (h_i)\longmapsto\sum_i h_i\prod_{j\ne i}F_j        \tag{9}
$$

has determinant

$$
 \det\mathcal S_F=\pm\prod_{i<j}\operatorname{Res}(F_i,F_j).
                                                               \tag{10}
$$

*Proof.* First suppose all $N$ roots are distinct, also across different polynomials. Work over $\mathbb C$ and order roots in blocks $\alpha_{i,1},\ldots,\alpha_{i,m_i}$. Let $V$ be the full evaluation Vandermonde matrix, and $V_i$ the matrix for the $i$th root block. Evaluating (9) on block $i$ kills every term except $h_i\prod_{j\ne i}F_j$. Therefore

$$
 \det(V)\det\mathcal S_F
 =\left(\prod_i\det V_i\right)
   \prod_i\prod_{a=1}^{m_i}\prod_{j\ne i}F_j(\alpha_{i,a}).
$$

The full Vandermonde determinant is the product of the within-block determinants and the cross-block factors. In the last product each pair of blocks contributes both orientations of each root difference. Cancelling the within-block determinants and one orientation of the cross-block factors gives (10), with coefficient-order sign only. Both sides are polynomials in the coefficients. The distinct-root condition is a nonempty Zariski-open set. Hence their polynomial equality holds identically, including multiple and shared roots. The cases $k=0$ and $k=1$ are interpreted as determinant one and satisfy the same statement. $\square$

**Lemma 4 (a branch merge).** In addition to the monic $F_i$, let $G_i$ be monic of degree $m_i-1$, and let $t_i,d$ be scalars. Define

$$
 Q=\prod_iF_i,\qquad
 P=(z+d)Q-\sum_i t_iG_i\prod_{j\ne i}F_j.                 \tag{11}
$$

The coefficient map

$$
 (d,\{t_i,\operatorname{coeff}F_i,\operatorname{coeff}G_i\}_i)
       \longmapsto(\operatorname{coeff}P,\operatorname{coeff}Q)
$$

has Jacobian determinant

$$
 \pm\prod_i t_i^{m_i-1}
          \prod_{i<j}\operatorname{Res}(F_i,F_j)^2.        \tag{12}
$$

Here and below $\operatorname{coeff}$ omits a prescribed monic leading coefficient.

*Proof.* First replace $(t_i,G_i)$ by the unrestricted polynomial $Z_i=t_iG_i$ of degree at most $m_i-1$. If $G_i=z^{m_i-1}+g_{i,1}z^{m_i-2}+\cdots+g_{i,m_i-1}$, its coefficient transformation is

$$
 (t_i,g_{i,1},\ldots,g_{i,m_i-1})
 \longmapsto(t_i,t_ig_{i,1},\ldots,t_ig_{i,m_i-1}),
$$

whose determinant is $t_i^{m_i-1}$, including $t_i=0$. When $m_i=1$, there are no $g$ variables and this factor is one.

Next put $W=\sum_i Z_i\prod_{j\ne i}F_j$. The derivative of the map $(\{F_i\},\{Z_i\})\mapsto(Q,W)$, ordered in these blocks, is

$$
 \begin{pmatrix}\mathcal S_F&0\\ *&\mathcal S_F\end{pmatrix}.
$$

Indeed variations of a monic $F_i$ have degree less than $m_i$, the derivative of $Q$ is exactly (9), and the derivative of $W$ in the $Z$ variables is the same map. Its determinant is $(\det\mathcal S_F)^2$.

Finally, $(d,Q,W)\mapsto(P,Q)$ with $P=(z+d)Q-W$ has determinant $\pm1$. To verify this rather than assume it, write $Q=z^N+q_1z^{N-1}+\cdots$ and $W=w_0z^{N-1}+\cdots$. The coefficient of $z^N$ in $P$ is $q_1+d$, which recovers $d$ with derivative one after $Q$ is fixed. Each remaining coefficient of $P$ contains the corresponding coefficient of $W$ with coefficient $-1$. The rest is block triangular. The chain rule and Lemma 3 prove (12). No inverse involving a zero rate was used. $\square$

# 4. From a tree to diagonal and edge-product coordinates

Introduce independent variables $d_v$ at vertices and $p_c$ at undirected edges. The determinant expansion on a tree, or a Schur complement followed by polynomial continuation, gives

$$
 P_v=(z+d_v)\prod_cP_c
      -\sum_c p_c Q_c\prod_{w\ne c}P_w.                  \tag{13}
$$

Here the products and sums range over children of $v$. One direct determinant justification is that every nontrivial cycle in a contributing permutation must be a two-cycle along one tree edge: a longer permutation cycle would give a graph cycle. When $v$ is fixed, the first term results. When $v$ is paired with child $c$, the sign is negative, the off-diagonal product is $p_c$, the child root is deleted, and the other branches remain intact. This is exactly the second term. Thus the argument does not require invertibility of any subtree block.

Let $\Phi_{T,r}$ be the coefficient map $(d,p)\mapsto(P_r,Q_r)$.

**Lemma 5 (independent-coordinate Jacobian).**

$$
 \det D\Phi_{T,r}
 =\pm\prod_{c\ne r}p_c^{s_c-1}\mathcal B_{T,r}.           \tag{14}
$$

*Proof.* For a leaf, $P_v=z+d_v$, $Q_v=1$, and the determinant is one. For a general root $v$, first map each child's independent subtree coordinates to $(P_c,Q_c)$, retaining the linking $p_c$ and $d_v$. This is a block-diagonal operation whose determinant is the product of the child Jacobians. Each child contributes $2s_c-1$ coordinates; adding one link parameter per child and $d_v$ gives $2\sum_cs_c+1=2|T_v|-1$, so the maps are square. Apply Lemma 4 with $F_i=P_c$, $G_i=Q_c$, $t_i=p_c$. It supplies the new factors $p_c^{s_c-1}$ and all sibling resultants at $v$. Induction includes each vertex and edge once, proving (14). $\square$

The physical map into these coordinates is

$$
 \Psi_\ell:(\kappa,\{a_{ij}\})\longmapsto
 \left(d_v=\sum_{i\sim v}a_{iv}+\kappa1_{v=\ell},\quad
              p_{\{i,j\}}=a_{ij}a_{ji}\right).            \tag{15}
$$

**Lemma 6 (physical-coordinate Jacobian).**

$$
 \det D\Psi_\ell=\pm\tau_\ell.                           \tag{16}
$$

*Proof.* If $n=1$, the map is $d_\ell=\kappa$ and the determinant is one. Otherwise choose a leaf $v\ne\ell$, with neighbor $u$. Put $t=a_{uv}$ and $s=a_{vu}$, so $t$ points from the leaf toward the leak. The leaf outputs are $d_v=t$ and $p_{\{u,v\}}=st$. Order the leaf parameters $(t,s)$ first and these two outputs first. Their derivatives in all remaining parameters are zero, and their $2\times2$ derivative block is

$$
 \begin{pmatrix}1&0\\s&t\end{pmatrix}.
$$

The remaining outputs are the smaller-tree coordinate map, except that $d_u$ has the extra term $s$. With $(t,s)$ fixed, this term has no derivative in the remaining parameters. Thus the full Jacobian is block triangular with determinant $t$ times the smaller-tree determinant. Every removed leaf contributes the rate directed toward $\ell$. Repeating proves (16) without division. $\square$

Since $C_{T,r,\ell}=\Phi_{T,r}\circ\Psi_\ell$, (14) and (16) prove the identity in Theorem 1. Nonvanishing of the resulting polynomial follows also from the nondivisibility proof in Section 6.

# 5. The full transfer resultant

*Proof of Theorem 2.* Fix $v$ and a child $c$. Modulo $P_c$, (13) reads

$$
 P_v\equiv-p_cQ_c\prod_{d\ne c}P_d\pmod {P_c}.
$$

Resultant multiplicativity, swapping arguments with its degree sign when necessary, gives

$$
 \operatorname{Res}(P_v,Q_v)
 =\pm\left(\prod_cp_c^{s_c}\operatorname{Res}(P_c,Q_c)\right)
        \prod_{\{c,d\}\subseteq\operatorname{Ch}(v)}
                  \operatorname{Res}(P_c,P_d)^2.          \tag{17}
$$

For clarity, each $p_c$ occurs $s_c$ times because $P_c$ has degree $s_c$. Each unordered sibling pair occurs twice because it appears once when reducing modulo $P_c$ and once when reducing modulo $P_d$. A leaf gives resultant $\operatorname{Res}(z+d_v,1)=1$. Induction yields the first equality in (8). Since $\prod_{c\ne r}p_c=\tau_\ell\eta_\ell$, Theorem 1 gives the second equality as a polynomial identity. $\square$

# 6. Exact coordinate multiplicities and the two conjectures

It is not enough to display explicit powers in (7). To prove the *exact* multiplicities, we must rule out additional coordinate factors hidden in the resultants.

**Lemma 7 (no coordinate factor in a sibling resultant).** After the physical substitution (15), no directed-edge variable $a_{ij}$ divides $\operatorname{Res}(P_c,P_d)$ for distinct children $c,d$ of any vertex. The leak variable $\kappa$ does not divide it either. Every such resultant is a nonzero polynomial.

*Proof.* The polynomial of a proper descendant subtree uses only directed rates whose source vertex lies in that subtree, including the rate from its root back to the deleted parent, and $\kappa$ if its leak lies inside. The variable sets of sibling subtrees are therefore disjoint, except that there is only one global leak variable and it lies in at most one of them.

Fix a directed variable $a$ and set it to zero. It affects at most one of the two sibling subtrees. Call that subtree the first one; if it affects neither, choose either as the first. Give its other rates any fixed nonnegative values. Its characteristic polynomial remains monic, with finitely many complex roots, whether or not it has a zero root.

In the other subtree, choose all rates with sources in that subtree strictly positive, and choose a nonnegative leak if present. This principal matrix is invertible: there is a path from every vertex to its top boundary loss. For a detailed justification, positive bidirected rates on a tree admit a positive diagonal symmetrization. The negative of the symmetrized subtree matrix has a quadratic form that is a sum of edge squares, plus a strictly positive boundary-killing square at its top vertex, and possibly a nonnegative leak square. A zero quadratic form forces the top coordinate to vanish, then every coordinate to vanish along the connected tree. Thus this matrix is positive definite and its characteristic roots are nonzero.

Scale every rate with source in this second subtree, and its leak if present, by a common $t>0$. Its entire principal matrix scales by $t$, so its roots become $t\beta_1,\ldots,t\beta_{s_d}$ with every $\beta_j\ne0$. There are only finitely many $t>0$ at which one of these equals a root of the first fixed polynomial. Choose any other $t$. The resultant is then nonzero while $a=0$. Since a polynomial is divisible by a coordinate variable exactly when its restriction at that coordinate zero is the zero polynomial, the claimed nondivisibility follows.

For the leak variable, set $\kappa=0$ first. The same construction works with positive edge rates: the proper principal subtrees still have their boundary loss, so the second block is invertible and can be scaled. This proves nondivisibility by $\kappa$. The constructions also prove that every resultant is nonzero as a polynomial. $\square$

No proof of a general compartmental inverse theorem is being imported in this lemma: the elementary diagonal symmetrization and edge-square argument are written explicitly in Section 7 as well.

**Corollary 8 (exact directed-edge exponents).** For an edge joining the observation-rooted parent $v$ to child $c$, the multiplicity of either directed rate in $J_{T,r,\ell}$ is

$$
 s_c-1+1_{\{\text{the rate points toward }\ell\}}.         \tag{18}
$$

The multiplicity of $\kappa$ is zero.

*Proof.* The monomial factors of (7) have exactly these powers. By Lemma 7 the product of all sibling resultants supplies no additional coordinate factor, since the polynomial coefficient ring is an integral domain and each coordinate variable is prime. $\square$

This proves in particular that (7) is nonzero, because its monomial factors and each of its resultant factors are nonzero polynomials.

## 6.1. The catenary formula

Take the path $1-2-\cdots-n$ with $r=\ell=1$. Each child $i+1$ has subtree size $n-i$, and there are no sibling pairs. Theorem 1 gives

$$
 \boxed{
 J_{\mathrm{path},1,1}
 =\pm\prod_{i=1}^{n-1}
       a_{i,i+1}^{\,n-i}a_{i+1,i}^{\,n-i-1}.}            \tag{19}
$$

This is the formula in [GMS, Conjecture 5.5, equation (11)], written by edges rather than collecting equal exponents. It holds for every $n\ge2$. In particular the last outward rate $a_{n,n-1}$ and the leak rate have exponent zero; no boundary case is discarded.

This result resolves that stated polynomial conjecture by a written proof. It does not newly establish the previously known generic global identifiability of endpoint-observed catenary models.

## 6.2. The rooted-tree multiplicity rule

For $r=\ell$, (18) says that an outward edge entering a subtree of size $s$ has exponent $s-1$, and its reverse edge exponent $s$. At a leaf these are zero and one. If a child has further child-subtree sizes $s_1,\ldots,s_k$, then $s=1+\sum_i s_i$. Its outward exponent is $\sum_i((s_i-1)+1)$, and its inward exponent is $1+\sum_i s_i$.

These are precisely the recursive rules of [GMS, Conjecture 5.9]. That paper attributes the rule to Molly Hoch, Mark Sweeney, and Hwai-Ray Tung. Corollary 8 therefore proves the conjectured **largest powers**, not just lower bounds on divisibility. Formula (7) additionally identifies the remaining, potentially noncoordinate factors through the sibling resultants and permits an arbitrary leak vertex.

## 6.3. Check against the known star formula

For a star observed and leaking at its center, every $s_c=1$ and $P_c=z+b_c$. Thus (7) reduces to

$$
 J=\pm\prod_cb_c\prod_{c<d}(b_c-b_d)^2,
$$

the already proved mammillary formula in [GMS, Theorem 5.1]. It is a consistency check and recovered prior result, not a new claim.

# 7. Positive rates: spectral collisions and observable modes

**Corollary 9 (exact interior singularity criterion).** At strictly positive edge and leak rates, the following statements are equivalent:

1. $J_{T,r,\ell}\ne0$.
2. For every vertex, the characteristic polynomials of any two distinct child principal submatrices have no shared root.
3. $P_r$ and $Q_r$ are coprime.
4. The realization $(A,e_r,e_r^{\mathsf T})$ is controllable and observable.

All the roots in statement 2 are real and negative.

*Proof.* In (7) and (8), all edge monomials are nonzero. The elementary vanishing criterion for the resultant proves the equivalence of statements 1--3.

Here is a direct spectral proof of the remaining assertions. On a tree choose $t_i>0$ recursively so that $a_{ij}t_j=a_{ji}t_i$ on every edge. There is no cyclic consistency condition. Set $S=\operatorname{diag}(\sqrt{t_i})$ and $L=S^{-1}AS$. The matrix $L$ is real symmetric. For a real vector $w$,

$$
 w^{\mathsf T}(-L)w
 =\sum_{\{i,j\}\in E}
       (\sqrt{a_{ji}}\,w_i-\sqrt{a_{ij}}\,w_j)^2
       +\kappa w_\ell^2.                                \tag{20}
$$

If this expression vanishes, the leak coordinate is zero and each edge relation propagates zero across the connected tree. Hence $-L$ is positive definite. Its principal submatrices are positive definite as well, proving the negative, real spectrum assertion for the original similar principal blocks. The same argument for a subtree with an extra boundary-killing square proves the auxiliary claim used in Lemma 7, even without an internal leak.

The root diagonal resolvent is unchanged by diagonal similarity:

$$
 \frac{Q_r(z)}{P_r(z)}=e_r^{\mathsf T}(zI-L)^{-1}e_r
       =\sum_\lambda\frac{\|\Pi_\lambda e_r\|^2}{z-\lambda},
                                                               \tag{21}
$$

where $\Pi_\lambda$ is orthogonal projection onto the $\lambda$-eigenspace of $L$. Distinct summands have distinct poles and nonnegative residues. Thus the reduced denominator has degree $n$ exactly when every eigenvalue is simple and every projection $\Pi_\lambda e_r$ is nonzero. By expressing $e_r,Le_r,\ldots,L^{n-1}e_r$ in an orthonormal eigenbasis, their determinant is a Vandermonde determinant times the product of the root eigenvector components. It is nonzero under exactly the same condition. This proves controllability; symmetry gives observability, and similarity transports both properties back to $A$. The equivalence with coprimality follows. $\square$

The statement is about local differential regularity and input-output minimality. It does not assert that every regular tree model has only one global parameter vector. Different branches can still give discrete alternatives, and this note does not recompute their generic number.

# 8. An exact interior singularity with all rates distinct

Use vertices $0,1,2,3,4$, observation/leak root zero, and undirected edges

$$
 (0,1),\ (1,2),\ (0,3),\ (3,4).
$$

In that order, assign the outward rates $(33,27,39,80)$, the reverse rates $(75,48,70,90)$, and leak $51$. All nine rates are positive and pairwise distinct. The full matrix is

$$
 A=\begin{pmatrix}
 -123&75&0&70&0\\
 33&-102&48&0&0\\
 0&27&-48&0&0\\
 39&0&0&-150&90\\
 0&0&0&80&-90
 \end{pmatrix}.                                         \tag{22}
$$

The two root-child principal polynomials are

$$
 P_1=(z+30)(z+120),\qquad P_3=(z+30)(z+210).              \tag{23}
$$

They are not equal, but they share the eigenvalue $-30$. Formula (7) therefore gives a singular physical Jacobian. Direct exact differentiation gives rank eight out of nine. The root observability matrix has rank four out of five, and $\gcd(P_0,Q_0)=z+30$.

This is a mathematical counterexample to extending the star-model shortcut "pairwise distinct positive rates suffice" to arbitrary rooted trees. The missing distinction is between distinct *rates* and disjoint *subtree spectra*. The example and ranks are checked by a separately implemented symbolic program; no observational data, fitted parameters, or floating-point simulation enter these assertions.

# 9. Relation to hydrological theory and limitations

Equation (1) describes a linear conservative exchange network with one external loss. Summing its state equations gives $\frac{d}{dt}\mathbf1^{\mathsf T}x=u-\kappa x_\ell$. The proved theorem concerns a known tree, known input/output location, and unknown time-independent transfer and leak rates. It directly addresses an inverse-problem obstruction in compartmental storage models; it does not settle general catchment-model identifiability.

The output convention in the published conjectures is a measured compartment state. For the useful special case $r=\ell$ and actual measured discharge $q=\kappa x_r$, the transfer pair becomes $(P_r,\kappa Q_r)$. The two coefficient descriptions carry equivalent local information in the positive interior. Indeed, conservation and multilinearity of the determinant in the root diagonal give

$$
 P_r(0)=\kappa Q_r(0).                                   \tag{24}
$$

To justify (24), with $\kappa=0$ all column sums of $A$ are zero, so $\det(-A)=0$. The derivative of $\det(-A)$ in $\kappa$ is its root diagonal cofactor $Q_r(0)$, which does not depend on $\kappa$ when the leak is at $r$. Thus (24) follows. At positive rates $Q_r(0)>0$ by the positive definiteness of the principal block. Hence $\kappa=P_r(0)/Q_r(0)$ is a smooth function of the state-response coefficients. Conversely, the leading coefficient of the discharge numerator is $\kappa>0$, so division recovers the monic $Q_r$. These maps give inverse smooth transformations on their images, preserving differential rank. This is not a claim about unknown distributed discharge weights or multiple outlets.

Several boundaries of the result matter. Multiple independent leak parameters, noncoincident input and measured-state vertices, unknown topology, nonlinear flux laws, forcing-dependent coefficients, tracer chemistry, noisy or discrete observations, and global fibre counting are not covered by Theorem 1. Structural regularity also does not give a quantitative condition number or a guarantee of stable inversion. Near a sibling spectral collision, conditioning can be poor even while the determinant is nonzero. Those are separate theoretical questions, not unperformed experiments required for validity of the polynomial proof.

# 10. Proof dependencies, diagnostics, and literature positioning

The arbitrary-tree proof uses the following chain:

$$
 \begin{gathered}
 \text{Vandermonde evaluation}\Longrightarrow
 \text{interpolation determinant}\Longrightarrow
 \text{branch-merging Jacobian}\Longrightarrow
 \det D\Phi;\\
 \text{leaf elimination}\Longrightarrow\det D\Psi;\qquad
 \text{chain rule}\Longrightarrow J;\\
 \text{resultant recursion}\Longrightarrow\operatorname{Res}(P_r,Q_r);\\
 \text{disjoint branch variables and scaling}\Longrightarrow
 \text{exact coordinate multiplicities}.
 \end{gathered}
$$

The positive-interior interpretation uses only finite-dimensional spectral decomposition in addition. All tree-specific determinant, recursion, and normalization arguments needed here are proved above. No laboratory assumption or simulation result is a premise of these theorems.

`exact.py` computes characteristic coefficients and derivatives directly from the physical matrix by exact integer Faddeev--LeVerrier arithmetic, then applies fraction-free determinant elimination. It checks all 200 unlabeled rooted tree shapes with one through eight vertices, every possible single-leak vertex, and five deterministic rate fixtures: positive, signed, equal, one zero outward rate, and one zero reverse rate. The resulting 7,230 cases include singular cases. The proposed formula is evaluated separately using principal characteristic polynomials and Sylvester resultants. The program also checks the full transfer resultant against the product of root reachability and observability determinants. The exact recorded counts, outputs and source hashes are in the generated evidence, rather than serving as an induction argument.

`independent.py` does not import the primary checker. It uses symbolic characteristic polynomials and differentiation to verify eleven small-model polynomial identities against hand-written formulas. It also verifies (22)--(23), the ranks, and the cancelled factor exactly. Four altered formulas in the primary checker and the all-distinct-rates false claim in the second checker are rejected. `reproduce.py` repeats both checkers normally and with Python optimization enabled in a fresh source directory, checks equality of their respective outputs, and records the source hashes. It does not certify the prose proof or invoke a Lean kernel.

The novelty claim is deliberately narrow. [GMS] states the catenary and tree-exponent conjectures addressed here. The 2026 paper [ACD+] still discusses the catenary formula as a possible future resolution. General graph-level local identifiability for single-input/single-output tree models is already classified by [BGMS]. Constructive identifiability and global solution counts for constrained tree systems have much older precedents, including [CLR]. This note claims neither the first use of compartment models in hydrology nor the first identifiability proof for a path. Its proposed contribution is the all-size, all-root, arbitrary-single-leak singular polynomial and its proved consequences. Literature search is not proof of historical priority, and external specialist review remains necessary before journal-level claims of novelty or acceptance.

# References

**[GMS]** Elizabeth Gross, Nicolette Meshkat, and Anne Shiu. *Identifiability of linear compartmental models: the singular locus*. Final arXiv text dated 28 June 2021, arXiv:1709.10013; Advances in Applied Mathematics (2022). Conjectures 5.5 and 5.9 and Theorem 5.1 are numbered as in the final text. [Full text](https://ar5iv.labs.arxiv.org/html/1709.10013).

**[ACD+]** Saber Ahmed, Natasha Crepeau, Paul R. Dessauer Jr., Alexis Edozie, Odalys Garcia-Lopez, Tanisha Grimsley, Jordy Lopez Garcia, Viridiana Neri, and Anne Shiu. *Identifiability of Directed-Cycle and Catenary Linear Compartmental Models*. SIAM Journal on Applied Dynamical Systems 25(1), 304--350 (2026). DOI: [10.1137/25M1728636](https://doi.org/10.1137/25M1728636). Section 6 explicitly refers to the still-to-be-resolved catenary singular-locus conjecture.

**[BGMS]** Cashous Bortner, Elizabeth Gross, Nicolette Meshkat, Anne Shiu, and Seth Sullivant. *Identifiability of linear compartmental tree models and a general formula for input-output equations*. Advances in Applied Mathematics 146, 102490 (2023); [arXiv:2106.08487](https://arxiv.org/abs/2106.08487).

**[CLR]** C. Cobelli, A. Lepschy, and G. Romanin Jacur. *Identifiability results on some constrained compartmental systems*. Mathematical Biosciences 47(3--4), 173--195 (1979). DOI: [10.1016/0025-5564(79)90036-1](https://doi.org/10.1016/0025-5564(79)90036-1). The abstract and its treatment in later sources establish relevant prior work on tree-model identifiability and solution counts; this cycle did not inspect its complete proof text.
