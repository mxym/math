# A four-type superset is impossible at every remaining rank

There is no Conway graph whose selected unit support is contained in **{neutral 18, neutral 24, (2,28), (3,37)}**. This removes the two additional exact triples {18,24,228} and {18,24,337} from the common eighteen and also excludes the exact four-type case. No rank is itself excluded. We prove the stronger fact that the assumed vanishings in just one maximal determinant-49 extension H contradict the genuine graph constraints there. Conversely absence of a unit type graph-wide implies absence among every H-eligible family. There is no graph symmetry assumption.

## Graph and harmonic bookkeeping in one fixed extension

Let n=W018=N18(H)/8, V=8W024, Z=W028, L=4W022, F=W014, M=W222 and S=W123−99−7F. The isotropic W028, W014, W222 and W123 count actual fields in the zero class of the *residual plane*. L is the number of antipodal H-eligible norm-22 lines, and Z,V count oriented neutral norm-28 and norm-24 fields respectively. S is the integer count of extra signed-unit (1,23) fields. On the assumed support F, M, S are not initially set to zero. All other selected coordinates are zero in their **unit** sense. In particular raw (1,25) vanishes because its only nonunit source is the absent norm 16. In particular a norm-30 sum of two norm-18 fields is unit: its maximum absolute entry is two, and a doubled site would translate to the absent raw (1,25). Neutral norm-18 and norm-22 fields are always unit. These are fixed-H implications because each translation has zero seven-class.

The [unconditional angular bound](norm18-parallelogram-dictionary.md) gives maximum absolute product ten between nonantipodal norm-18 sources; in particular eleven is impossible even if Fano labels exist. Since norms 16 and 20 vanish here, absolute ten and eight are excluded as well. Nine cannot occur in the residual plane: its two-source Gram determinant mod seven is 5, neither zero nor a square in the square-determinant plane. Thus absolute products are at most seven, with just 4,−3 in one signed source class.

Use the norm-22 Johnson graph with D double norm-28 lines as edges and L vertices. We recall why allowing Fano labels or these two extra selected unit types does not invalidate its construction. At a fixed norm-28 sum z, the inner products of one source against the two sources of a second representation sum to 14, forcing both to equal seven. Thus one representation at most in a projective source direction, and distinct directions must be perpendicular: at most two in total. Its companion lines have norm22 and are distinct. Conversely at q=a_i+b_i with m decompositions, the source classes are fixed, distinct and perpendicular; orient all a_i in the same signed class. For i≠j the a_i·a_j=b_i·b_j=4 and a_i·b_j=7. Consequently c_ij=a_i−a_j=b_j−b_i is the double direction, with opposite center s_ij=a_i+a_j−q=a_i−b_j. The companion bijection counts 2D=sum_q binom(m,2). At fixed q different s_ij are genuinely distinct lines: they have one COMMON nonzero signed seven-class so cannot be negatives; equality would force equality of the unordered index pairs since the Gram of the a_i is 14I+4J, positive definite. This proof does not require a global neutral minimum of 18, which a Fano could violate. The centered a_i−q/2 have Gram 14I−(3/2)J, so m≤9 without a bound on any unselected positive-charge shell.

Write Q=supp(q), P_i={x∈Q:a_i(x)=q(x)}. Each P_i has 11 sites because a_i·q=11; off Q no two a_i can agree nontrivially since s_ij is unit. Hence d_ij=#doubled sites of c_ij=|P_i∩P_j|−4, all outside Q. Write h_q=sum d_ij. To bound its global sum, orient a doubled site p of a norm-28 line positively. It gives b=d_p−c with b_p=1 and b of raw type (1,23). An ordinary d_j has no such site. Each of the S extra unit b has six choices. The other possible b are the Fano translates f+d_j with f(j)=−1, at most 7F fields; each has exactly three +1 sites (the three of seven positives of f missing j), not counting its +2 at j. These are the [standard true-unit substitutions](../short-shell-moments.md). Therefore the sum of d over all unoriented norm-28 lines is at most 6S+21F. Each double has exactly two ends, so sum_q h_q≤12S+42F.

There is no need to suppose the four signed class sizes n_i equal. The [cross-centroid argument](unconditional-cross-shell-centroids.md), counting within-class dot-four pairs by Z/2+D instead of a multiplicity cap, gives
```
(12+4√2)n² ≤ 84n + 7Z + 14D + (7√2/2)V.
```
Indeed cross absolute-six pairs use distinct norm-24 lines on this face; absolute-eight is absent. For arbitrary n_i the step 3 sum n_i²+√2 (n_1+n_2)(n_3+n_4)≥(3+√2)(sum n_i)²/4 applies, with sum n_i=4n.

## Four blocked opposite edges at every clean center

Call a center clean if it has \(m=4\) and all six differences are signed units. The four triples of its four source sets have sizes at most one for their common intersections. In fact for any three \(P_i,P_j,P_k\) on the 22 sites, each has size 11 and pairwise overlap 4, so their union has size \(33-12+|P_i\cap P_j\cap P_k|=21+|P_i\cap P_j\cap P_k|\le22\). At a clean center, if \(k(x)\) counts its four memberships, \(\sum(k(x)-2)=0\) and \(\sum(k(x)-2)^2=4\), so exactly two sites have \(k=3\) and none has \(k=4\). The four triple populations are therefore **\(1,1,0,0\)**, with no second profile.

For an anchor pair \(1,2\) at a clean \(q\), suppose its opposite endpoint \(s=a_1+a_2-q\) also has a unit triangle through the anchor edge. The two triple counts on \(q\) containing that anchor pair must coincide. Here is the graph-side reason. For either third decomposition \(q=a+b\) on \(q\) and the same third decomposition \(s=a'-b'\) on \(s\), align the signed source classes as usual. The anchor products give \(q\cdot a'=s\cdot a=-3\), hence \(b\cdot b'=-6-a\cdot a'\), forcing both common-class products to equal \(-3\). Their norm-30 sums are unit, so each pair overlaps in exactly three sites, all with opposing signs. On the four anchor sites \(X=P_1\cap P_2\) one has \(q=s=a_1=a_2\); the two choices \(a,a'\) cannot both be active there, as that would be same-sign overlap. Every \(b,b'\) overlap is in \(X\): an overlap cannot oppose an active anchored \(b_1\) or \(b_2\), since both endpoint wedges are unit; and off the entire anchor support \(b=-a,\ b'=a'\), so opposing \(b,b'\) would give agreeing \(a,a'\). Thus exactly three sites in \(X\) are chosen by neither \(a\) nor \(a'\). Their two triple populations sum to one. Applying this to both choices of the third index at \(q\), with the same \(a'\), gives the claimed equality. This is also the [opposite-endpoint relation](rank42-two-type-closure.md) in the earlier two-type proof.

Each clean center has four local unit incidences whose two triple populations are unequal (the four \(1,0\) pairs among the four triples). Their opposite local unit edges consequently lie in no unit triangle. Let \(w_q\) be the number of these wedge-free unit edges at any center and \(B\) the number of clean centers. The charge is injective on incidences because a Johnson edge and its opposite end recover the charging incidence, giving \(\sum w_q\ge4B\).

For every center the pointwise inequality is
\[
\binom m2+\tfrac34 w_q-3\,1_{\mathrm{clean}}\ \le\ 3+\tfrac{25}{8}h_q.
\]
For \(m\le3\), if \(h_q=0\) then only \(m=2\) contributes \(w_q=1\); if \(h_q\ge1\), use \(w_q\le2\). A clean \(m=4\) is exact; if only one pair is nonunit then every other edge lies in a triangle of \(K_4\) minus that edge, so \(w_q=0\). If at least two are nonunit, use \(h_q\ge2,\ w_q\le4\). For \(m=5,6,7,8,9\), distributing the \(11m\) memberships of the \(P_i\) as evenly as possible on 22 sites gives respectively \(h_q\ge4,6,15,20,32\), since \(\sum_x\binom{k(x)}2=4\binom m2+h_q\). Edges counted by \(w_q\) have no triangle even among themselves, and therefore \(w_q\le\lfloor m^2/4\rfloor\). Substitution verifies all five inequalities. Thus no local enumeration is needed.

Summing and using \(\sum w_q\ge4B\) and the doubled-slot bound gives
\[
2D\le3L+\tfrac{75}{2}S+\tfrac{525}{4}F.
\]
This also implies the weaker \(2D\le3L+42S+147F\).

## Exact scalar identities

It follows with 4√2>28/5 and 7√2/2<5 that the following rational tangent slack is nonnegative:
```
T_j=5(7Z+84n+5V+21L+294S+1029F)−88(2jn−j²) ≥0.
```
The [fixed-H scalar checker](nearface_common.py) reduces the following three exact identities in the native common harmonic rows with precisely the eight forbidden selected unit coordinates set to zero. No original rank-specific Fourier rows, graph-wide averaging or fitted real inputs occur.
```
54405 = 89085W228+9970W337+241760F+100470M+1175W234+4050W335+27T55,
2702n = 145579+19910F+5745M+5685W228+300W335+695W337+2T54,
6n = 291+2S+16F+5M+3W228+W337.
```
The first forces the nonnegative integers M=F=0 and 3W228+W337≤54405/9970. The second gives n≥145579/2702, in particular N18(H)≥432 by antipodality. The last now gives S>13, hence S≥14.

## Contradiction

We already know \(F=0\). The stronger bound on \(2D\) lowers the term \(294S\) in the weaker bound for \(14D\) to \((525/2)S\), so the old \(T_{55}\) in the certified identity is at least \((315/2)S\): the improvement is multiplied by five, and the same rational estimates and tangent continue to apply. Therefore
\[
54405\ \ge\ 27T_{55}\ \ge\ 27(315/2)\cdot14=59535.
\]
This is a contradiction in one fixed extension \(H\). Replay the exact moment rows and common support counts with `python3 nearface_common.py`. No graph configurations or local menus are enumerated in the argument.

Together with the [common eighteen-support sieve](common-six-family.md) this leaves at most sixteen common triples. This is a necessary support filter, not a claim of graph realizability.
