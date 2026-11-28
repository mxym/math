# Rooted dyadic cycles in abelian K3,3 covers and elementary-abelian minima

**Theorem.** Every vertex of every finite regular abelian cover of $K_{3,3}$ is contained in a simple cycle of length $4,8,16$, or $32$. For elementary abelian deck groups at primes $3,5,7$ the following sharper statements hold. At prime 3 every vertex is contained in a cycle of length $4,8$, or $16$. Among connected covers without any of the lengths $4,8,16$, none exists at prime 3; the minimum graph orders at primes 5 and 7 are respectively **3750** and **2058**.

This supplements the [six-layer existence and sharpness results](FactorErdosGyarfasBipartiteSixOrbits.md), in which the general color-preserving six-layer theorem was unrooted. The present rooted assertion is for the specific base $K_{3,3}$, not arbitrary six-layer quotients. The minimum orders are in the given elementary abelian classes only. The initial rooted and finite-class results came from the research Dreamer; the projective-kernel census below was independently implemented and reproduced. Previously known explicit cyclic witnesses are not counted again here.

## 1. Rooted cycles by compression

Use a translation-matching presentation of the regular cover. To hit a vertex in one fiber, retain that base vertex and one other base vertex on the same side, together with the three vertices on the opposite side. The three length-two paths between the selected pair become three translation matchings upon compression. Choosing origins, their offsets can be written $0,a,b$.

If two offsets agree, their paths through different middle fibers have the same endpoints and yield a simple four-cycle. Otherwise the [two-layer three-matching theorem](FactorErdosGyarfasAbelianTwoOrbits.md) supplies a simple cycle of length $4,8$ or $16$ in the compressed graph. Expanding gives a simple cycle of length $8,16$ or $32$. An interior vertex on any one of the paths determines its two endpoint vertices by the matching bijections; if such an interior vertex were repeated then the same contracted edge would have been reused, contradicting simplicity. Distinct path types have distinct middle fibers. The expanded cycle visits both selected outer fibers. Deck translation taking its vertex in the target fiber to the desired vertex preserves the simple cycle. The same argument works for a target on either side.

For an elementary abelian 3-group, if $0,a,b$ are distinct and $a,b$ are dependent, the relevant compressed component is a $K_{3,3}$ on the two copies of their three-element span, so it has a four-cycle. If $a,b$ are independent, the alternating path-label word
\[
                    0,1,0,1,2,1,0,2
\]
with label shifts $0,a,b$ closes, with partial voltages distinct in each endpoint fiber. Indeed the first fiber sees $0,-a,-2a,b$, and the second sees $0,-a,-2a+b,b$, all over the characteristic-three group. This gives a simple compressed 8-cycle, hence a 16-cycle through the desired vertex after expansion and translation. In either case 32 is unnecessary.

## 2. The exact elementary-abelian census

Number the base parts $0,1,2$ and $3,4,5$. Normalize the five tree shifts on $03,04,05,13,23$ to zero; use four generator shifts on $14,15,24,25$, directed from the first part to the second. The shifts generate the deck group exactly when the cover is connected, by the tree normal form for loops. For deck group $(\mathbb F_p)^r$ the four shifts therefore give a linear surjection
\[
                \mathbb F_p^4\longrightarrow \mathbb F_p^r.
\]
Up to choice of deck basis, this is uniquely prescribed by its $(4-r)$-dimensional kernel. Enumerate kernels via reduced row-echelon matrices over $\mathbb F_p$. These counts refer to the fixed labeled base, before quotienting by base automorphisms.

For each cyclically nonbacktracking directed base walk of length $4,8,$ or $16$, record its total formal shift $w$ and all differences of partial shifts between occurrences in the same fiber. If a difference is zero already in $\mathbb F_p^4$, the walk can never lift to a simple cycle and can be discarded. Otherwise a lift is a simple cycle in the cover with kernel $K$ precisely if
\[
              w\in K,\qquad d\notin K
        \quad\text{for every recorded same-fiber difference }d .
\]
Every simple cycle projects to such a walk: an immediate reversal in a matching returns to the same lifted vertex. As membership in a linear subspace is invariant under nonzero scalar multiplication, encode both the differences and $K$ by projective-line bitsets, with the total shift either zero or one projective line. This yields a different exact replay from direct path enumeration in each candidate cover. The checker enumerates all $72,648,133128$ rooted directed base walks at the three lengths respectively. It visits every kernel, tests every needed total and collision class, and gives the following counts (all kernels, followed by those without any of the three lengths):
\[
\begin{array}{c|rrrr}
p &r=1&r=2&r=3&r=4\\\hline
3&(40,0)&(130,0)&(40,0)&(1,0)\\
5&(156,0)&(806,0)&(156,0)&(1,1)\\
7&(400,0)&(2850,0)&(400,52)&(1,1)
\end{array}
\]
Rank zero is the base itself and has a four-cycle. No connected elementary abelian cover can have rank above four. This gives the stated orders $6\cdot 5^4=3750$ and $6\cdot 7^3=2058$. An explicit minimizing 7-case assigns the four shifts $1,7,49,113$ in base-seven vector notation, least significant coordinate first. Its kernel is generated by $(-1,-2,-2,1)$, and the same checker explicitly verifies this kernel avoids all three short lengths. Together with the rooted theorem, every vertex in any passing cover is on a 32-cycle.

**Exact replay.** `python3 -O verify_erdos_gyarfas_k33_rooted.py` verifies the characteristic-three word, the three full projective-kernel censuses, and the concrete $\mathbb F_7^3$ example using only standard-library arithmetic.
