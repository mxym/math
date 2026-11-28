# Exact minor-law feasibility for alternating pair rings

This is a supplement to the [distinct-support classification](MarcusDistinctSupportClassification.md). It determines **exactly** when an even alternating ring with the same real rotation at each gate has a common minor law. For arbitrary two-by-two gates it gives an exact linear feasibility problem with one variable per gate, including arbitrary complex phases. It concerns the spectrum-independent common law, not a counterexample to Marcus–de Oliveira.

The equal-angle threshold was suggested by the author-external review of the classification (the geometry research line). We reproduce it independently and extend the analysis to arbitrary gate probabilities and phases.

## 1. An exact linear feasibility formulation

Let $m\ge2$, with coordinate pairs $A_i=(u_i,v_i)$ in the first matching of gates $V_i$ and $B_i=(v_i,u_{i+1})$ in the second matching of gates $W_i$, indices taken modulo $m$. Write $L=2m$. Use the displayed local orders for row and column indices $0,1$. Let $p_j$ denote the common squared modulus of the two diagonal entries of gate $j$, so that its two off-diagonal entries have squared modulus $1-p_j$.

Define the product probability and one complex interference factor by
\[
 q_0(b)=\prod_{j=1}^L
       \begin{cases}p_j& b_j=0,\\1-p_j& b_j=1,\end{cases}
 \qquad
 C=\prod_i (V_i)_{00}\overline{(V_i)_{10}}\,
       \prod_i (W_i)_{11}\overline{(W_i)_{10}}.
\]
Here $b$ is a binary vector of switches. Then the common minor law holds **if and only if** there are real $E_1,\ldots,E_L$ such that
\[
 q(b)=q_0(b)+(-1)^{|b|}
       \left((-1)^{m-1}\operatorname{Re} C
                        +\sum_{j=1}^L E_j(-1)^{b_j}\right)
       \ \ge 0
                   \qquad\text{for every }b\in\{0,1\}^L.
\tag{1}
\]
When feasible, this is an explicit normalized distribution on the deterministic switch routings. For fixed nondegenerate magnitudes, phases influence this test through one real scalar:
$|C|=\prod_j\sqrt{p_j(1-p_j)}$, so only its real part enters. If any gate has $p_j=0$ or $1$ then $C=0$ and the independent law itself suffices.

**Proof of necessity.** The one-by-one support and the two-by-two rank-one transfer blocks force every permitted permutation to route one input from each $A_i$ to each of its two neighboring output blocks, as in the classification. Thus the permutation identifies a unique vector of switches. This argument uses just zeros and rank-one constraints, and remains valid at degenerate magnitudes; additional zeros can only further restrict the allowed switches.

Every marginal omitting two prescribed switches is the product marginal: prescribe just those two gates to have unchanging middle occupancy (both ports or neither), toggle at every other gate around the overlap cycle, and choose the input/output sets through any specified active switch assignment. This gives a unique intermediate occupation. Consequently the probability difference from $q_0$ has Walsh degrees at least $L-1$.

For all gates active, one can prescribe any switch vector and its complement as the two possibilities, by starting with the occupied middle set of all $u_i$. The relative determinant sign is $(-1)^{m-1}$, because the two paths match the first gate labels to the last gate labels by a one-step cyclic shift relative to each other. For the all-zero switches the products of local entries with the second path conjugated are exactly the factors displayed in $C$. Switching the chosen input column at a first gate multiplies its factor by $-1$, by orthogonality of the two rows; switching the chosen output row at a second gate similarly multiplies its factor by $-1$, by orthogonality of the columns. This remains true when the factor is zero. Thus the complement-pair interference is $2(-1)^{m-1+|b|}\operatorname{Re}C$. It determines the degree-$L$ Walsh coefficient exactly, and does not constrain the degree-$(L-1)$ coefficients through these pair observations. This gives (1).

**Proof of sufficiency.** Every squared minor is one of the same two types, or identically zero. Fix any selected input and output sets. The middle occupation must have the prescribed count at every gate. If these counts admit no middle set, the entire Cauchy–Binet expansion is zero and there is no deterministic routing either. If any count is 0 or 2 and a middle set exists, that count fixes both its adjacent bits and propagates uniquely around the cycle. In this case the number of inactive gates is even: around the even overlap cycle the middle bit flips once at each active gate. There are at least two inactive gates. The observation then fixes only the active switch bits and is reproduced by the product marginal of any function of the form (1). If all counts equal 1, there are precisely two complementary middle sets, so the observation is precisely one complement pair, reproduced by the fixed degree-$L$ coefficient. The restrictions to minor moduli 0, unit inactive determinants, and noninterfering product magnitudes all remain valid when some local gate entries vanish. Finally the appended Walsh functions in (1) each sum to zero, so $q$ has total mass 1. Thus it satisfies the full law.

## 2. Equal real angles: the exact window and an explicit law

Suppose every gate in the displayed local orientations is
\[
      \begin{pmatrix}c&s\\-s&c\end{pmatrix},
      \qquad c,s\ge0,\quad c^2+s^2=1.
\]
The cases $p=c^2=0,1$ are deterministic. For $0<p<1$, put
\[
 X=\max\{(1-p)/p,\ p/(1-p)\},\qquad
 J=\text{the largest odd integer at most }m.
\]
Then the common law exists **if and only if**
\[
              J(1-X^{-2})\ \le\ 2(1+X^{-J}).
\tag{2}
\]
This inequality is non-strict: equality is feasible. In particular $m=2$ permits every same-angle choice, even though different angles in that same four-gate architecture need not have a common law.

To prove (2), the independent distribution is exchangeable, and permuting the $L$ Walsh variables preserves the required coefficient $D=(-1)^{m-1}(cs)^L$ and the condition of nonnegativity for all bits in (1). Average any feasible law over all bit-position permutations to set all $E_j$ equal to some $E$. Conversely a nonnegative symmetric candidate in (1) is enough; no symmetry of the physical circuit is used at this step. Put $x=(1-p)/p$ and $\tau=2E/D$. At Hamming weight $m+k$ the candidate mass divided by $(cs)^L$ is
\[
             x^k-(-1)^k(1-\tau k),\qquad -m\le k\le m.
\tag{3}
\]
The change $(x,k,\tau)\mapsto(1/x,-k,-\tau)$ preserves these constraints, so assume $x=X\ge1$.

The negative even $k=-2$ imposes $\tau\le(X^{-2}-1)/2$. It is the strongest negative even constraint because $(1-X^{-r})/r$ decreases in $r>0$ (it is the average of the decreasing function $(\log X)X^{-u}$ for $0\le u\le r$). The negative odd constraints say $\tau\ge-(1+X^{-r})/r$ at odd $r\le m$. The numerator decreases and the denominator increases; hence the strongest is at $r=J$. Their compatibility is exactly (2).

For sufficiency take $\tau=(X^{-2}-1)/2$ in (3). Every positive even constraint requires $\tau\ge(1-X^r)/r$; the largest right side is at the smallest positive even $r=2$, and $\tau\ge(1-X^2)/2$ follows from $X^2+X^{-2}\ge2$. Positive odd constraints are automatic since $\tau\le0$, and $k=0$ has mass zero. The remaining negative constraints were already checked. For the original case $x<1$ use the opposite sign of this $\tau$, as dictated by the above symmetry. This is an explicit probability law at every feasible parameter, including the endpoints of (2).

If $m\ge3$, there is a unique $X_J>1$ with equality in (2), since the left side increases from 0 to $J>2$, while the right side decreases from 4 to 2. The interval of feasible $p$ in $(0,1)$ is
\[
         \left[\frac{1}{1+X_J},\,\frac{X_J}{1+X_J}\right].
\]
For $J=3$ it is $[1/3,2/3]$. As $J\to\infty$ its half-width is asymptotic to $(1+W(e^{-1}))/(4J)$, where $W$ is the nonnegative inverse of $w\mapsto we^w$. Indeed $a_J=J\log X_J$ satisfies $J(1-e^{-2a_J/J})=2(1+e^{-a_J})$. For large $J$ the two sides force $1\le a_J\le4$; then taking limits gives the unique root of $a=1+e^{-a}$, and the half-width is $\tfrac12-\tfrac1{1+X_J}\sim a/(4J)$. Thus any fixed same-angle $p\notin\{0,1/2,1\}$ eventually fails on sufficiently long alternating rings.

For equal squared magnitudes but arbitrary phases, one can likewise reduce (1) to a single real parameter. Replace the 1 in $1-\tau k$ in (3) by $\operatorname{Re}C/\prod_j\sqrt{p_j(1-p_j)}$, and choose $\tau$ with all $2m+1$ resulting masses nonnegative. Here $\tau$ is normalized by the full magnitude, $2E/[(-1)^{m-1}|C|]$, instead of $D$. The independent case of zero interference illustrates why magnitudes alone are in general insufficient.

**Exact controls.** `python3 -O verify_marcus_alternating_ring_phase.py` verifies all minors up to complementation for two same-angle probability laws and one mixed-angle complex circuit with nonzero cross-term real part. It also checks sample scalar boundary and failure cases using exact rationals.
