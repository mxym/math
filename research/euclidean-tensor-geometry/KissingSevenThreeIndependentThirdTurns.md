# Seven-dimensional kissing codes with three independent third turns

Let $G=(C_3)^3$ act on $\mathbb C^3\oplus\mathbb R$ by three independent coordinate rotations through $120^\circ$, fixing the last line pointwise. All code points have unit norm and distinct points have inner product at most $1/2$.

**Theorem.** A $G$-invariant code has at most **126** points. Exactly **two** configurations achieve 126 up to isometry: the $E_7$ root code and the classical non-antipodal $C_{7\text{-}126c}$ code. More generally, any such code with **more than 118** points is obtained from one of these two maxima by deleting whole equatorial axis triangles. Its size is 120, 123, or 126. We do not claim 118 is the sharp threshold for this structure.

No equator, lattice, antipodality, or transitivity is assumed. Neither a single rotation of order three nor three simultaneous rotations with only one independent group generator suffice as a hypothesis. The [unrestricted seven-dimensional kissing number](https://www.mefyi.com/papers/kissing-numbers-five-seven/) is not determined here.

**Prior results.** The two equality configurations are classical. [Cohn, Jiao, Kumar and Torquato](https://arxiv.org/abs/1102.5060) discuss four noncongruent 126-point configurations without this symmetry restriction. [Novgorodtsev, Theorem 3](https://www.preprints.org/manuscript/202610.0335) proves the same two equality types under the *different* hypothesis of a full 72-point $E_6$ cross section, with no symmetry requirement. Here the orbit bounds force that section at equality and force its completion above 118. The [six-dimensional companion theorem](https://github.com/mxym/math/blob/4b782c9cb9f76b74fbb231d9fce0c91e7523a83d/research/euclidean-tensor-geometry/KissingThreeIndependentThirdTurns.md) has only one maximizer.

## Orbit sizes and small sections

Write a point as $(v_1,v_2,v_3,z)$. A nonzero complex coordinate has radius at least $1/\sqrt3$: rotating it alone moves the point $\sqrt3$ times that radius. A support of size $0,1,2,3$ therefore has orbit size $1,3,9,27$. Denote by $p$ the number of fixed poles, $n_i$ the number of single-support points on coordinate $i$, and $k_{ij}$ the number of nine-point orbits on support $ij$. Write $n=\sum n_i$ and $k=\sum k_{ij}$. There are at most two triple orbits: each has all radii $1/\sqrt3$ and $z=0$. The largest inner product with another triple is $\tfrac13\sum_i\cos\delta_i\ge1/2$, where $0\le\delta_i\le60^\circ$ are their nearest phase distances modulo $120^\circ$. Thus the only possible second triple is its negative. Fix the first triple $T$ at phases zero when one exists.

Each plane plus the fixed line is three-dimensional, so $p+n_i\le12$ by the [three-dimensional kissing theorem](https://arxiv.org/abs/math/0410324). In particular $p+n\le36$. On the two-plane-pair subspace (two complex coordinates and the real line) [Tomar's five-dimensional bound](https://doi.org/10.5281/zenodo.23638108) gives
\[
             p+n_i+n_j+9k_{ij}\le43 .
\]
Thus $k_{ij}\le4$ and $3p+2n+9k\le129$. With **zero** triple orbits the size $N=p+n+9k$ satisfies $2N\le129+9k-p\le237$, so $N\le118$.

## One triple: two same-side pair orbits cannot share a support

Suppose $T$ is present. Within a given closed hemisphere and on a fixed pair of complex coordinates there is at most one nine-point orbit. We prove this small geometric fact with the exact closed-box certificate below. It puts $k\le6$, so with exactly **one** triple the total is at most $27+54+36=117$.

Scale lengths by $\sqrt3$. A pair on this support has radii $u=\sqrt{1+A},v=\sqrt{1+B}$ and unsigned height $h=\sqrt{1-A-B}$, where $A,B\ge0$ and $A+B\le1$. Let $\alpha,\beta\in[0,\pi/3]$ be the nearest phase distances from $T$. Kissing compatibility implies
\[
              u\cos\alpha+v\cos\beta\le3/2 .
\]
For a second pair orbit use primes. On either coordinate the greatest possible circular distance between two phases of unsigned distances $\alpha,\alpha'$ is
\[
 d(\alpha,\alpha')=\min(\alpha+\alpha',\,2\pi/3-\alpha-\alpha').
\]
This is attained by opposite choices of phase sign and is at least $|\alpha-\alpha'|$. Independence of the two plane rotations and agreement of the height signs therefore require
\[
 uu'\cos d(\alpha,\alpha')+vv'\cos d(\beta,\beta')+hh'\le3/2 .
\]

The [standard-Python verifier](verify_kissing_seven_three_third_turns.py) covers the four coordinates $(A,B,3\alpha/\pi,3\beta/\pi)$ by closed dyadic boxes. In each it rounds each radius **down**, using integer square roots at scale $10^4$; for the height it uses the *upper* two squared-radius endpoints. It bounds cosines from below at the *largest possible* phase distance. For the two-orbit bound this distance, in units $\pi/3$, is bounded above by the minimum of 1, the sum of the two upper phase endpoints, and 2 minus the sum of the lower endpoints. All cosines are nonnegative. Away from $\pi/3$ the degree-10 alternating Taylor lower polynomial at the upper rational angle from $\pi<355/113$ is rounded down; at $\pi/3$ the bound $1/2$ is exact. Only a strictly excessive lower bound discards a closed region. Widths $1/4,1/8,1/16$ leave respectively **163, 16, 0** unordered pairs of boxes after the three necessary inequalities. Every child pair is included; identical boxes are tested explicitly, so a pair of distinct continuous orbits inside one box is not lost.

## Two triples and directed triangle layers

Put the two triples at $T$ and $-T$. For a pair orbit with unscaled radii $a,b$ and phase distances $\delta,\gamma$ from $T$, summing the two triple constraints gives
\[
 \sqrt3\ge a[\cos\delta+\cos(60^\circ-\delta)]
             +b[\cos\gamma+\cos(60^\circ-\gamma)]
 \ge\tfrac32(a+b)\ge\sqrt3 .
\]
Consequently $a=b=1/\sqrt3$, $z=\pm1/\sqrt3$, and on its two coordinates the pair phases must be $0^\circ$ and $60^\circ$ in some order (they cannot coincide, by either triple constraint). At a given height and support at most one of the two orientations can occur: two reversed pairs on that same support have largest product $1/3+2(1/3)\cos60^\circ=2/3$. Record the support as an edge directed from phase $0$ to phase $60^\circ$ on three labels. Two incident edges at the same height must have opposite phases on their shared coordinate, since equal phases would give $2/3$. Three edges at that height form a directed 3-cycle.

Here are the resulting bounds on single-support points. If two edges of the same height sign meet axis $i$, a single point there with height of the same sign and magnitude $t$ would satisfy
\[
       t+(\sqrt3/2)\sqrt{1-t^2}\le\sqrt3/2 .
\]
For $0<t\le\sqrt{2/3}$ this is impossible: $\sqrt3/2$ times $1-\sqrt{1-t^2}=t^2/(1+\sqrt{1-t^2})$ is less than $t$. At $t=0$ only the six midpoint rays qualify. If there is just one incident edge of the same sign it still forces $t+\tfrac12\sqrt{1-t^2}\le\sqrt3/2$, hence $t<5/12$; the left side increases on $[0,\sqrt{2/3}]$ and already exceeds the right side at $5/12$.

Let $i_+,i_-$ be the two incident-edge counts at a given axis. The following bounds count individual single-support **points**.
* The unrestricted bound is 12. If one count equals 2 and the other is zero, all singles lie in the opposite closed hemisphere. Its opposite pole could be added locally, giving at most 11 singles, and their count is a multiple of three, hence at most 9.
* If one count equals 2 and the other is positive, all singles are on the same closed side and $|z|<5/12$. Three different triangle phases would have a pair at angular distance at most $40^\circ$; their product would be at least $(1-(5/12)^2)\cos40^\circ>1/2$. Thus there are at most 6 points. When both counts equal 2 all such points are equatorial midpoints.
* If both counts equal 1, all singles have $|z|<5/12$, possibly on opposite sides. Four triangles have a pair at angular distance at most $30^\circ$. Their product would exceed $(1-(5/12)^2)\cos30^\circ-(5/12)^2>1/2$. This gives at most 9 points.

If $k\le3$, the total is at most $54+9k+36\le117$. If $k\ge4$, both heights are occupied and neither pole is feasible. For $k=4$ the two edge counts are $3+1$ or $2+2$. In the former case the full-cycle sign limits all three axes to at most nine points ($N\le117$). In the latter case equal middle vertices of the two paths give axis bounds $6,9,9$, and distinct middle vertices give $6,6,9$ ($N\le114$). For $k=5$, all three axes have a full-cycle sign and at least one opposite edge, so $N\le54+45+18=117$. The verifier also checks these counts for all pairs of edge subsets of the triangle.

It follows that above 118 there are **six** pair orbits: a directed 3-cycle at each height. The two triples contribute 54, the two layers contribute 54, and the only remaining choices are whole triangles on the six equatorial midpoint rays in each coordinate. Completing all of these gives 126 points, with an $E_6$ equator by the [explicit root model](https://github.com/mxym/math/blob/4b782c9cb9f76b74fbb231d9fce0c91e7523a83d/research/euclidean-tensor-geometry/KissingThreeIndependentThirdTurns.md). Reverse the labels of the triangle if necessary to fix the top cycle. The bottom cycle is either the same or the reverse. In the reversed case the code is antipodal, while choosing the same orientations leaves only the 36 antipodal pairs in the equator. Thus the two full codes are noncongruent. The checker tests all $7{,}875$ unordered pairs in each, using integer Eisenstein coordinates; in the antipodal case it also checks closure under all root reflections. By Novgorodtsev's identification these are precisely $E_7$ and $C_{7\text{-}126c}$. Deleting equatorial triangles gives all the stated sizes; no uniqueness of an unrestricted partial-code completion is asserted.

**Replay.** Run ordinary `python3 verify_kissing_seven_three_third_turns.py`. It needs only the standard library. The section inequalities use the cited unconditional three- and five-dimensional bounds; the interval checker is solely for the shared-support two-orbit lemma, not a search over whole 126-point configurations.
