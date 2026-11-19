# The sharp bound on the largest atom of a sum of three independent integer variables

Yongxian Zhang

Let $Q(X)=\max_{t\in\mathbb Z}\Pr(X=t)$. For caps $0<\alpha_i\le1$ let
$k_i=\lfloor1/\alpha_i\rfloor$, $\beta_i=1-k_i\alpha_i$.
Write $Y_i$ for independent integer variables with mass $\alpha_i$ at $0,\ldots,k_i-1$ and residual mass $\beta_i$ at $k_i$. We prove the three-summand case of the point-concentration conjecture attributed to Juškevičius (2023) in Kurauskas, arXiv:2603.11043v1, Conjecture 1.3:

**Theorem.** For all independent integer $X_1,X_2,X_3$ with $Q(X_i)\le\alpha_i$,
$$
 Q(X_1+X_2+X_3)\le
 \max_{\epsilon_i\in\{-1,1\}}Q(\epsilon_1Y_1+\epsilon_2Y_2+\epsilon_3Y_3).
$$
The right side is attained by admissible variables and is given by the explicit weighted eight-box expression (1) below. The caps can differ and need not have integer reciprocals. This is a point mass, not the mass of a general interval. We do not settle four or more arbitrary summands.

## 1. Eight nested boxes and the candidate

Fix a target $t$. Keeping two marginal laws fixed, the conditional success given $X_i=x$ is a nonnegative summable sequence $h(x)$ of total sum one. Choose $k_i$ distinct locations of its largest entries, then one more of the remaining largest; append arbitrary zero entries if its support runs out. Largest entries of a nonnegative summable sequence exist at every such stage. Writing $\lambda$ for the value of the last choice, for any admissible mass distribution the expectation of $h-\lambda$ is at most $\alpha_i$ times the sum of its positive entries. This upper value is attained by placing $\alpha_i$ on the first $k_i$ sites and $\beta_i$ on the extra site. Thus we may replace the three marginals one at a time to increase or preserve the probability at $t$, without assuming finite support originally or a compact feasible set.

For the resulting $i$-th marginal let $A_i$ be its $k_i$ heavy sites and $B_i$ these sites plus one extra (arbitrary distinct if $\beta_i=0$). Its mass function is $(\alpha_i-\beta_i)1_{A_i}+\beta_i1_{B_i}$. For $S\subseteq\{1,2,3\}$ let $Z_S(t)$ count integer triples summing to $t$ in the box using $B_i$ for $i\in S$ and $A_i$ otherwise. Its coefficient in the mixture is
$$
 v_S=\prod_{i\in S}\beta_i\prod_{i\notin S}(\alpha_i-\beta_i).
$$
The sorted index coordinates of this box range over $[0,l_i]\cap\mathbb Z$, with $l_i=k_i-1+1_{i\in S}$. Let $L_S=\sum l_i$ and
$$
 h_S(j)=[x^j]\prod_{i=1}^3(1+x+\cdots+x^{l_i}),\qquad
 M_S=h_S(\lfloor L_S/2\rfloor).
$$
Outside the support, set coefficients to zero. Let $\mathcal I$ be the four $S$ with $L_S$ even. For $S\in\mathcal I$ put $K=L_S/2$ and $D_S=M_S-h_S(K+1)$. We prove the exact optimum is
$$
 \boxed{\quad \sum_S v_SM_S-\min_{S\in\mathcal I}v_S D_S .\quad}       \tag{1}
$$

## 2. The central antichain and its one-unit drop

Equip a box of index triples with the coordinatewise order. As the physical values in each coordinate strictly increase, the index triples summing in physical values to fixed $t$ form an antichain. For this product of chains the LYM bound is
$$
 \sum_{j}\frac{\#\{\text{antichain elements of index sum }j\}}{h_S(j)}\le1.
$$
Here and below only nonempty ranks are included. We give details, also to justify the equality use. The two-chain rank sizes form a symmetric log-concave trapezoid: in a slice of fixed index sum $s$, the first coordinate is uniform on the integers from $\max(0,s-l_2)$ to $\min(l_1,s)$. As $s$ increases by one the endpoints increase by at most one. The uniform distributions can be quantile-coupled so that the first coordinate increases by zero or one; the complementary coordinate also does so. This holds because both endpoints increase and the new interval is stochastically between the old interval and its translate by one (uniform quantiles, or direct comparison of CDFs).

For a uniform three-chain slice of rank $s$, write $I$ for the third coordinate and $J=s-I$ for the sum of the first two. The law of $I$ has masses proportional to the trapezoid $g(s-i)$ on $0\le i\le l_3$, where $g$ is the two-chain rank sequence, zero off its range. For $s+1$ the ratio $g(s+1-i)/g(s-i)$ is nondecreasing on common support by log-concavity; the support endpoints both stay put or increase. Thus $I_{s+1}$ stochastically dominates $I_s$ (on normalization, the two mass functions cross at most once from smaller to larger). Likewise $J_{s+1}$ dominates $J_s$, since its law is the fixed weights $g(j)$ truncated to $s-l_3\le j\le s$, and both truncation endpoints advance. Reflecting the latter comparison gives $I_{s+1}\le_{\rm st} I_s+1$. Quantile-couple the third coordinates; then $I,J$ each advance by zero or one and exactly one advances. Within the two-coordinate slices of ranks $J$, use identical positions for equal ranks and the preceding coupling for successive ranks. This couples uniform successive three-chain slices by covering relations. Link the successive couplings by their conditional probabilities to get a random full increasing chain uniform at each rank. An antichain is hit at most once, giving LYM.

The rank sizes are symmetric and unimodal (convolution of symmetric uniform interval sequences is symmetric unimodal: represent a symmetric unimodal sequence as a nonnegative sum of same-center interval indicators and use the two-interval trapezoid). In particular $Z_S(t)\le M_S$. If $D_S>0$ at an integral center, it is the unique largest rank by this unimodality, so equality $Z_S=M_S$ in LYM forces the entire central index rank to sum in physical values to $t$.

In fact $D_S\in\{0,1\}$. If one $l_i>K$, its whole-sum convolution has the same coefficients at $K$ and $K-1$: for any indices of the two shorter chains (whose maximal sum is $2K-l_i\le K-1$), either target is attained by one valid index of the longest. Hence the drop is zero. If all $l_i\le K$, then the coefficient at $K$ of $(1-x)\prod_i(1+\cdots+x^{l_i})=\prod_i(1-x^{l_i+1})/(1-x)^2$ is
$$
 K+1-\sum_i(K-l_i)=1.
$$
No double numerator exponents contribute, since $l_i+l_j=2K-l_h\ge K$. By symmetry the drop to $K+1$ equals that to $K-1$. This includes $K=0$.

## 3. Choosing a single sacrificial corner

Fix any $S\in\mathcal I$. Take each $A_i=[0,k_i-1]\cap\mathbb Z$; form $B_i$ by appending $-1$ if $i\in S$, or $k_i$ if $i\notin S$. Up to translations these are precisely the independent signed canonical marginals in the theorem. Let $c_T$ be the sum of the three interval midpoints at corner $T$. At $S$ it is an integer (total width even), and $c_T=c_S+|T\triangle S|/2$. Take the common integer target $t=c_S+1$. For $T\ne S$ it is within $1/2$ of that box's midpoint and gets its largest rank $M_T$. At $S$ it loses exactly $D_S$. Choosing a corner minimizing $v_SD_S$ attains (1). If the minimum is zero, the rank upper bounds already finish the proof.

## 4. The four rigid corners cannot all be full

Henceforth every $S\in\mathcal I$ has $D_S=1$ and $v_S>0$. Suppose, aiming at a contradiction, that an arbitrary triple of nested pairs $(A_i,B_i)$ and target $t$ attain $Z_S(t)=M_S$ at all four such corners. Every one of these central index ranks is then full. We record the elementary geometric consequence.

Consider a single full central index rank at integer $K$ in a box of positive widths $a,b,c$, with $a+b+c=2K$ and $a,b,c\le K$. Denote the sorted physical arrays by $x_0,\ldots,x_a$, $y_0,\ldots,y_b$, $z_0,\ldots,z_c$. For $1\le i\le a,\ 1\le j\le b$, neighboring differences $x_i-x_{i-1}$ and $y_j-y_{j-1}$ agree whenever
$$
 K+1-c\le i+j\le K+1.
$$
Indeed $(i-1,j,K+1-i-j)$ and $(i,j-1,K+1-i-j)$ are both central. Every two successive $i,i+1$ can use a common $j$: the integer interval $[K+1-c-i,K-i]$ is nonempty since $c\ge1$ and meets $[1,b]$ since $i\le a-1\le K-1$ and $K-c\le b$. Also every $i$ has a neighbor $j$ and conversely, because $[K+1-c-i,K+1-i]$ meets $[1,b]$ for $1\le i\le a$ ($a\le K,\ K-c\le b$); interchange $a,b$ for the converse. Thus all first and second increments agree, even if one list has only one increment. Applying the same argument with the other pair shows that all three arrays are arithmetic progressions with one common positive step.

First suppose all $k_i\ge2$. The preceding conclusion applies at all four corners. Any two different corners of the prescribed parity share one array (their subsets differ in exactly two coordinates); this array has at least two terms, so the common step agrees between these corners. All six arrays are therefore arithmetic progressions with the same step.

If exactly one $k_i=1$, say $k_1=1$, use the two corners in $\mathcal I$ containing index 1. All widths there are positive; they share the two-element $B_1$, and between them use both the short and long arrays for coordinates 2 and 3. The same conclusion follows with a singleton interpreted as a one-point progression. If exactly two $k_i=1$ but the third exceeds one, precisely one parity corner leaves both singleton arrays short; its third width is positive, violating the condition that every width is at most half the total. This case was already settled by a zero drop. Finally, if all $k_i=1$, $\mathcal I$ consists of the empty set and the three pairs. In each pair-corner the widths are $1,1,0$ in some order. Fullness of its central rank equates the positive gaps of the two two-element arrays. Applying this to all three pairs again gives one common positive step.

Let this step be $h$. A nested arithmetic progression of lengths $k_i$ and $k_i+1$ with the same step extends at one endpoint (also true for a singleton). Its interval midpoint therefore shifts by $\Delta_i=\pm h/2$. At every even-total-width full corner, the physical sum for the central rank is exactly the sum of the array midpoints, hence equals $t$. Four such equal sums are impossible: for even subset parity, equality at the empty set and each pair forces all pairwise sums $\Delta_i+\Delta_j=0$; for odd subset parity, equality at the three singletons forces all $\Delta_i$ equal, and equality at the triple forces their common value to be zero. Either way this contradicts $|\Delta_i|=h/2$.

Thus at least one integral-center box loses at least one integer count. The weighted loss is at least $\min_{S\in\mathcal I}v_S$ in this remaining, all-unit-drop case. This is exactly the deduction in (1), proving the sharp upper bound and the theorem.
