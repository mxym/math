# Comb rigidity for the pure towers at two possible odd-covering LCMs

Let a finite set of residue classes modulo pairwise distinct odd
integers greater than one cover the integers. Write Q for its LCM
and let \(Q<473\,824\,157\,932\,125\). The
[pinned two-LCM certificate](https://github.com/mxym/math/blob/4ae600294cde2f6323a502cb8ec9ff7accf5fabc/research/euclidean-tensor-geometry/theoretical-cryptography/FactorOddCoveringTwoLowLCMs.md)
leaves \(Q=168\,131\,152\,814\,625\) or \(320\,977\,655\,373\,375\).
Both have support \(3,5,7,11,13,17,19,23,29\), with 3-exponent
4 or 5 respectively and 5-exponent 3. Every pure modulus
\(3^e\), \(1\le e\le v_3(Q)\), and \(5^e\), \(1\le e\le3\),
is mandatory and indispensable by that certificate.

**Theorem.** For each \(p=3,5\), write \(r_{p,e}\pmod {p^e}\)
for the required pure classes. There exists a residue
\(\xi_p\bmod p^{v_p(Q)}\) such that for every e in its pure tower,
\[
 r_{p,e}\equiv \xi_p\pmod {p^{e-1}},
 \qquad
 r_{p,e}\not\equiv \xi_p\pmod {p^e}.
\tag{1}
\]
Thus each removed cylinder branches from the same surviving root
path, at one successive depth. The two pure towers must both
be combs, in the precise sense of (1). One can choose a single
integer \(\xi\) realizing both \(\xi_3,\xi_5\) by CRT.
It does not follow that this \(\xi\) is uncovered by the mixed
moduli.

This is a restriction on **positions of actual residue classes**,
not a better lower bound for Q or a proof excluding either value.
It depends on the preceding omission result for the two LCMs and
the mandatory 3 and 5 towers. We make no existence assertion.

## 1. Replacing uniform conditioning by adapted cylinder caps

In a prime-power coordinate let \(\nu_j\) be any probability law
supported on the residues surviving the chosen pure-tower deletions.
Suppose for every congruence class of exponent e the law gives
mass at most \(u_{j,e}\) for \(1\le e\le a_j\).
Write \(s_j'=\sum_e u_{j,e}\) and choose
\(c_j=(1-\delta_j)^{-1}\), \(0\le\delta_j\le1/2\).
When the numbers \(c_j u_{j,e}\) are valid nonincreasing
tails in \([0,1]\), use comparison variables \(D_j\) with
\[
 \Pr(D_j\ge e+1)=c_j u_{j,e},\qquad
 X_j=\prod_{i<j}D_i.
\]
The pinned finite-support distortion proof gives its same stage
bound with the new law and caps,
\[
 L_j=c_j\,\mathbb E\big[s_j'(X_j-\eta_j)-\delta_j\big]_+,
\tag{2}
\]
where \(\eta_j=1\) for total pure-tower deletion
and \(\eta_j=0\) for no deletion.

For clarity, that proof requires only the stated coordinate
congruence bounds, not that the reference law be uniform.
An active class of modulus \(m p_j^e\) consumes at most
\(u_{j,e}\) of the reference fibre. Its prefix condition is
spelled out by the exponents of m. At most one term occurs
per modulus. The fibre distortion changes the covered mass
from \(\alpha\) to \(c_j(\alpha-\delta_j)_+\), preserves
earlier-coordinate marginals, and bounds each future conditional
\(p_j^e\)-cylinder probability by \(c_j u_{j,e}\).
The reverse-coordinate convex comparison with these tails then
replaces actual prefix indicators by nested ones. On each
comparison tuple there are \(X_j-\eta_j\) eligible prefixes for
each exponent e; summing e yields (2). All these steps use
only nonnegative weights. If \(\sum_j L_j<1\), the final
measure has an uncovered point in the allowed product.

Here we use adapted laws only at 3 and 5, remove their whole
pure towers, and keep \(\delta_1=\delta_2=0\).
At all later coordinates we use exactly the older choice
of reference law, with
\(u_{j,e}=p_j^{-e}/(1-\sum_{f=1}^{a_j}p_j^{-f})^{\eta_j}\).
Every test uses rational caps and rational thresholds.

## 2. Capacity and exhaustive pure-tower shapes

A class modulo \(p^e\) is a node at depth e in the rooted
p-ary residue tree of depth a (\(a=v_p(Q)\)), using least
significant digits first. Two mandatory pure classes at the
same prime cannot meet: their moduli are comparable, so
intersection would give containment of one in the other
and contradict indispensability. Thus after deleting one
node at each depth, all deleted nodes are mutually disjoint
as cylinders.

Given caps \(u_1,\ldots,u_a\), compute maximum allowed
total mass bottom-up. A deleted node has capacity zero,
a surviving leaf has capacity \(u_a\), and a surviving
nonroot node of depth e has capacity
\(\min(u_e,\sum\text{ child capacities})\). The root has
capacity equal to the sum of its child capacities.
Inductively every total amount from zero to a node's capacity
can be divided among its children, so root capacity at least
one proves existence of the required reference law. With
rational caps the mass can be chosen rational. These capacities
are evaluated exactly, not inferred from a floating-point
optimization status.

One representative of each rooted-tree shape is enough.
Start with the full depth-a tree. After each depth e, replace
one live node at that depth by a dead node, then sort the child
representations at all vertices. A prior automorphism can
always transport an actual live node to one of those tried.
Nodes with identical current child shapes need only be
tried once in a given sibling list. The number of retained
partial shapes after each depth is \(1,1,2,6\) for
\(p=3,a=4\), \(1,1,2,6,27\) for \(p=3,a=5\), and \(1,1,2\)
for \(p=5,a=3\).

There is an independent enumeration without sorting subtrees.
Fix the first deleted digit (by root symmetry), iterate
all compatible deeper deleted prefixes, and use the list
of pairwise longest common prefix lengths as the orbit key.
This key exactly determines the rooted tree of the marked
nodes: at each depth it determines which deeper markers
remain in the same child branch, while unused branches are
indistinguishable. There are 3,780/464,940/1,900 raw
tuples respectively, giving the same 6/27/2 shapes.
The automorphisms used here are independent sibling
permutations; it is not asserted that two such sets are
affine translates of each other as residue classes.

For each Q jointly combine the 3-shapes with the 5-shapes.
The rational certificate contains one capacity-feasible
choice of caps and one threshold schedule for every
combination except the pair of combs. The results are:

| Q | Combined shapes | Strictly excluded | Largest rounded-up loss (ppm) |
|---:|---:|---:|---:|
| 168131152814625 | 12 | 11 | 996505 |
| 320977655373375 | 54 | 53 | 995858 |

The omitted shape in each case is unique: when all parents
of deleted nodes lie on one live path, rooted-tree
automorphisms can put that path on all-zero digits and
each deleted side branch at that level's last digit.
This is exactly (1). That neither comb/comb case is
excluded by this table is a limitation, not a construction.

## 3. Replay

[The certificate data](odd_covering_pure_tower_comb_schedules.json)
contains only rational caps and threshold numbers (common denominator
\(10^8\)); no dependence on the numerical search used to find
them is necessary. Its `excluded` field records one pair
of deleted-prefix lists in each excluded chart.

~~~sh
python3 verify_factor_odd_covering_comb_towers.py odd_covering_pure_tower_comb_schedules.json
node verify_factor_odd_covering_comb_shapes.js odd_covering_pure_tower_comb_schedules.json
~~~
The Python replay enumerates the sorted trees, verifies every
capacity and product-tail condition, and evaluates the finite
losses as exact rationals. The Node replay independently
enumerates all raw marked prefix tuples with the LCP key and
checks the precise shape coverage of the same table. Neither
replay examines candidate covers or solves the residual two
charts.
