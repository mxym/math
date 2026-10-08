# Sharp upper Main: independent mathematical bridge review

Review date: 7 October 2026 UTC. Scope: the remaining **upper** stability proof,
with the actual invariant, every prescribed maximum simplex, its own centroid,
and the original `gSharp`. This review does not redo the pyramid/B or truncation
sharpness audits, run Lean, change frozen sources, or publish anything.

## Conclusion first

**PASS at the traditional mathematical and inspected source-semantic level.**
No mathematical gap was found in the original first-variation argument or in
the newer direct radial replacement. The difficult remaining geometric bridge
was **scale**, not the already established prescribed-simplex retention.
The radial estimate really controls actual volumes for the same compact-limit
law and absorbs its extra factor into the original Q using the stronger
first-moment assignment bound. It does not require an unsupported containment
of a finite approximating body in the enclosing simplex.

The same selected anchors also construct a genuine enclosing simplex, with
positive barycentric weights and exactly the required normalized facet atoms.
They are auxiliary polar anchors; they never replace the input maximum S.
Section 3 below gives a direct self-contained construction and a useful extra
quantitative positive-weight bound.

The new candidate source explicitly contains `theorem sharpMain : sharpMainGoal`
and uses the same input S all the way through normalization, cap retention and
the pullback. That is a source-semantic observation, **not this review's own
kernel verification**. Independent full reconstruction, source identity and
empty-kernel closure are the separate formal auditor's responsibility.

An exact **actual-body** counterexample in section 6 proves that normalized
brightness, even with a positive centered atomic simplex law and exact facet
contacts, cannot by itself replace scale control. This counterexample does
not refute the candidate: its non-even support test detects precisely the
information the candidate's radial proof retains.

## 1. Sources and verification boundary

1. Original written proof: Git object
   `c897a556e12e460380c7cf521e88f84286994915`,
   `notes/sharp-simplex-stability/proof.tex`, read with `git show`, without
   checkout or fetch. SHA256:
   `9361999cfa4337500041da4b3fc824cd3676a07a22ffad0274e38346bf301b98`.
2. Local actual-pyramid independent audit, especially `SAME_WITNESS_REVIEW.md`,
   `INDEPENDENT_AUDIT_REPORT.md`, and the exact frozen source under
   `../lean_actual_pyramid_independent_audit_20261007/source/`.
   Its established audit covers 714 public proofs and 1499 owned declarations.
3. Local literal truncation independent audit, used only to verify scope and
   the unchanged actual Targets. Target SHA256:
   `8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94`.
4. Owner Page `[private page identifier removed]`, observed at sequence 17.
   Historical Page statements about an open Main were superseded during this
   review by the candidate below; proof counts are not mathematical conclusions.
5. Complete new radial written proof, Library
   `[private delivery identifier removed]`: all 376 lines read, saved locally
   as `NEW_RADIAL_PROOF_SOURCE.txt`; 18361 bytes, SHA256
   `0c2e2eebf7f4409f4fdb56d68879eb5281b4d6db71337c9864f497922715d0e4`.
6. 627-assembly readable patch `[private delivery identifier removed]`:
   inspected full relevant interfaces at lines 11030–11129, 12235–12499,
   12765–12909, including the explicit finite-Minkowski premise.
7. New upper-Main candidate `[private delivery identifier removed]`,
   index `[private delivery identifier removed]`.
   Declared patch: 203 files, 1422231 bytes, SHA256
   `9a0a33f57cc6a3f9f373040ae11fd98ade985bbd5712f31fca3b82f702b7a932`.
   Targeted full source reads cover `FiniteRadialSupportScale.lean`,
   `PolarSimplexConstruction.lean`, `OriginalRadialScale.lean`, and
   `SharpUpperMain.lean`; this review does not independently reconstruct or
   certify all 203 files.

## 2. Corrected obligation ledger

The following separates actual prior Lean results, new inspected source, and
traditional mathematics. Conditional wrappers are not counted as unconditional
Main proofs.

| Link | Exact obligation | Status and guard |
|---|---|---|
| Original input S | Fix any maximum S; affine-normalize that S, sending its own centroid to 0; get unit ball ⊂ S ⊂ K ⊂ R0 ball | Already in audited 714 source: `maximum_simplex_regular_normalization`, `maximumInscribed_R0_ball`; not a new open geometric leaf |
| Affine restoration | Preserve actual entryDefect and the actual infimum over homotheties at the original centroid | Already proved by `entryDefect_affine_image`/`entryDefect_affineBody`, `centeredDilation_affine_map`, `excess_affine_image` |
| Actual law and strong assignment | One μ,φ, ν, w and assignment; h_K(w_i)=1, centering, brightness, A/B/D identities and cost ε ≤ c t/(1+t), where t=(d+1)e and c=(d+1)(d+2) | Audited actual pyramid/joint bridge; do not reselect a law or replace the actual invariant |
| Directional roundness | Actual projection and volume bounds give E(-u·X)+ ≥ 2b; ε ≤ h=Qt ≤ b implies b ball ⊂ conv(w) | Traditional proof complete; candidate `ActualNormalizedDirectionalRoundness` and same-witness Q wrapper consume the identical w |
| Genuine polar simplex | Construct P={y:w_i·y≤1} as an actual d-simplex; unit ball ⊂ K ⊂ P ⊂ M ball; positive λ; normalized injective normals n_i and heights H_i with n_i/H_i=w_i | Section 3 complete; candidate `PolarSimplexConstruction` explicitly supplies these facts. This was an actual construction obligation at the 627 checkpoint |
| Actual P cone law / brightness | Correct assigned weights to the unique centered weights on those same w; identify them with actual facet weights; normalized brightness difference ≤(M+1)h/2 | Corrected weights are not silently identified with assignment weights. The 627 finite-halfspace correction has explicit atom, independence and body premises, now discharged by the constructed P |
| Scale | For the same compact-limit law, α=|P|/|K| ≤ (1+Mh)^d | 627 still required `FiniteSupportMinkowskiObligation`; original classical proof is valid but needs a same-law finite-limit bridge. New radial source discharges scale without Minkowski: sections 4–5 |
| Actual cap | Actual absolute projection deficits ≤Jh imply Hausdorff distance ≤L(Jh)^(1/(d−1)) | Actual projection-cap geometry is already established; 627 scale/cap algebra preserves original J,L. New radial consumer must supply its actual scale input |
| Every prescribed S | From small Hausdorff distance, shrink P into K, invoke maximality of the original S, use its actual barycentric determinant ratio and near-permutation, then retain its own centroid | Already in audited 714 `PrescribedSimplex`, `HausdorffRetention`, `Mxym.StochasticRigidity`; gives the stronger factor 2Mdρ, leaving slack in original factor 4 |
| Threshold and global Main | Same original b,M,Q,J,L,rSharp,eSharp,aSharp,gSharp; e≥0; local estimate + coarse R0−1 | Scalar gates proved before this review. Candidate `sharpLocal` and literal `sharpMain` now assemble the actual inputs. Independent whole-chain kernel acceptance remains outside this review |

**Mathematical-gap classification:** no outstanding mathematical gap was found
in the inspected actual route. At the 627 checkpoint, the positive-dimensional
finite Minkowski theorem and polar construction were genuine unfilled formal
premises, not mere variable renamings. They are supplied/bypassed in the new
candidate. The existence of a final source proof must still be distinguished
from independently verified final proof-term closure.

## 3. Self-contained polar construction from the supplied anchors

Let w_0,…,w_d be affinely independent in R^d, with ||w_i||≤1 and
b B_2^d ⊂ T=conv(w_i), where b>0. Suppose also h_K(w_i)=1.
Let the genuine affine barycentric coordinate functions of T be

    α_i(x)=λ_i+ℓ_i·x.

They satisfy α_i(w_j)=δ_ij, Σα_i=1 and Σα_i(x)w_i=x. Consequently

    Σλ_i=1,  Σℓ_i=0,  Σλ_i w_i=0,  Σ w_i ℓ_i^T=I.

Because α_i≥0 on bB, minimizing its affine formula on that ball gives
λ_i≥b||ℓ_i||. For d≥1, ℓ_i≠0: the coordinate has value 1 at w_i and 0 at
another vertex. Thus **λ_i>0**, with no assumption about assigned weights.
Define

    q_i=−ℓ_i/λ_i.

Then ||q_i||≤1/b=M and

    q_i·w_j=1−δ_ij/λ_i.                         (3.1)

For y satisfying all w_i·y≤1, put β_i(y)=λ_i(1−w_i·y).
These coefficients are nonnegative and sum to 1. Transposing the preceding
identity Σw_iℓ_i^T=I gives Σℓ_iw_i^T=I, so

    Σ β_i(y)q_i = −Σℓ_i + Σℓ_i(w_i·y) = y.       (3.2)

Conversely, (3.1) and λ_i>0 show every q_i satisfies all the halfspaces.
Therefore

    P={y:∀i,w_i·y≤1}=conv(q_0,…,q_d).

The same formula gives β_i(q_j)=δ_ij, proving the q_i are affinely independent:
apply each affine β_i to any affine dependence. This is a genuine simplex,
not an abstract polar-set placeholder.

The support contacts imply K⊂P. Cauchy–Schwarz and ||w_i||≤1 imply B⊂P.
The proven ||q_i||≤M implies P⊂MB. For each i, another vertex q_j has
w_i·q_j=1; hence h_P(w_i)=1. In particular w_i≠0. Each inequality is
nonredundant: the facet is precisely conv(q_j:j≠i), since (3.1) has strict
inequality at q_i and equality at all other vertices.

Normalize by n_i=w_i/||w_i|| and H_i=1/||w_i||. Then ||n_i||=1,
H_i≥1>0, n_i/H_i=w_i, and the literal halfspace carrier is still P.
If n_i=n_j, the two w's are positive multiples. Their equal support value
h_P(w_i)=h_P(w_j)=1 forces the multiple to be 1, contradicting affine
independence unless i=j. Thus the normals are injective, exactly as required
by the actual finite-facet theorems.

There is also a useful quantitative margin not needed by Main:

    1=α_i(w_i)≤λ_i+||ℓ_i||≤λ_i(1+1/b),
    hence λ_i≥b/(1+b).                          (3.3)

The actual cone weights γ_i=area(F_i)H_i/(d|P|) are nonnegative, sum to 1,
and satisfy Σγ_iw_i=0 by the actual facet mass and balance identities.
Uniqueness of barycentric coordinates gives γ_i=λ_i, so they are strictly
positive. Thus positivity is derived from the actual simplex, not stipulated.

For assignment weights p_i=Pr(a(X)=i), let c=Σp_iw_i. Centering gives
||c||≤ε. Since p_i=α_i(c),

    p_i−λ_i=−λ_i q_i·c,
    Σ|p_i−λ_i|≤Mε.                             (3.4)

Combining the assignment's 1-Lipschitz error with (3.4) for |u·x| gives
absolute-moment error ≤(1+M)ε. Both actual laws are centered, so their
negative-part moments differ by at most (1+M)ε/2. This proves the normalized
brightness comparison at the original constant; the assigned p are not
assumed to equal the actual λ.

## 4. The direct radial scale argument is valid

Fix one finite actual supporting approximant
Q={x:n_i·x≤h_i}, with unit normals and h_i=h_K(n_i)≥1.
Let F_i be its actual facets, C_i=conv(0,F_i), and
p_i=|C_i|/|Q|. The actual radial mass/decomposition identities give
p_i≥0 and Σp_i=1. Zero-area/empty facets cause no difficulty.
Its actual cone law has these probabilities at x_i=n_i/h_i.

For the fixed enclosing P define s_i=h_P(n_i)/h_i=h_P(x_i).
Since K⊂P⊂MB, one has 1≤s_i≤M. We do **not** assume Q⊂P.
For nonzero y∈P the ray from 0 through y exits the compact Q at q=t_0y,
on some actual facet F_i. Such an exit exists because Q contains a ball and
is bounded. At an active inequality,

    1/t_0=n_i·y/h_i≤h_P(n_i)/h_i=s_i.

Thus y=s_i[(1/(t_0s_i))q] belongs to s_i C_i. The origin can be included
separately as a null singleton. Consequently actual measure subadditivity and
homothety scaling, not a scalar model, give

    |P|/|Q|≤Σp_i s_i^d
           ≤1+dM^(d−1)(Σp_i s_i−1).            (4.1)

The second inequality is the elementary identity
s^d−1=(s−1)Σ_{j=0}^{d−1}s^j≤dM^(d−1)(s−1), valid for 1≤s≤M.

Now take precisely the subsequence φ and compact law μ already chosen by the
joint actual moment/assignment theorem. Since h_P is continuous and
M-Lipschitz, it is a bounded continuous test on the common compact unit ball.
Hence Σp_i s_i→I=∫h_P(x)dν(x) along that same φ. Actual approximation-volume
convergence and |K|>0 pass (4.1) to

    α=|P|/|K|≤1+dM^(d−1)(I−1).                 (4.2)

The fixed-body polar support and K⊂P give I≥1. Since every selected anchor
has h_P(w_i)=1, the identical assignment gives I−1≤Mε. Therefore

    α−1≤dM^d ε.                               (4.3)

This argument uses neither first variation nor a replacement surface-area law.
It applies directly to the constructed compact-limit law. The finite
approximants may protrude outside P, and that does not invalidate the cover.

## 5. Original constants, cap exponent, and every S

Put t=(d+1)e≥0, c=(d+1)(d+2), h=Qt. The strong actual assignment says
ε≤c t/(1+t), while the exact original constant is Q=c8^dM^(4d).
For M≥1,

    cM^(d−1)≤Q,
    α−1≤dM^d c t/(1+t)≤dMQt=dMh,
    α≤1+dMh≤(1+Mh)^d.                         (5.1)

Retaining the strong bound until this absorption is essential. Replacing it
prematurely by ε≤h would leave an unwanted factor M^(d−1).

Let k(u)=π_K(u)/(d|K|) and p(u)=π_P(u)/(d|P|). The actual atomic argument
gives |p−k|≤(M+1)h/2 and p≤1/2. For e≤eSharp, Mh≤1, so (5.1) gives
α−1≤d2^(d−1)Mh. Consequently

    0≤π_P(u)−π_K(u)
      =d|K|[(α−1)p+(p−k)]
      ≤(d/2)(2R0)^d[1+M+d2^(d−1)M]h=Jh.

This is exactly the original J. The actual projection cap gives
ρ=d_H(K,P)≤L(Jh)^(1/(d−1)), with L=(d−1)(M+1).
Its dimension drop is genuine: project the separating direction onto a
(d−1)-space retaining that direction, place a disjoint ball of radius
s/[2(M+1)] in the projected cap, and use its contained cube. It is not a
full-dimensional volume cap relabeled as a sharper estimate.

The original threshold yields ρ≤1/(8Md). Since h_P≥1 on unit directions,
the Hausdorff support comparison gives (1−ρ)P⊂K. Apply maximality of the
**initially prescribed normalized S**, not of P or of an anchor simplex:

    |S|/|P|≥(1−ρ)^d≥1−dρ.

The actual barycentric matrix W of S in P is column-stochastic and its
absolute determinant is that actual volume ratio. For δ=dρ≤1/8, the already
proved stronger stochastic lemma gives a permutation whose every column has
l1-error ≤2δ. Here is its elementary reason: by multilinearity in the other
columns, |det W| is bounded by the largest entry of any fixed column; hence
each column has an entry ≥1−δ. Two columns sharing that row have l1-distance
≤4δ, and subtracting them would imply |det W|≤4δ<1−δ. The rows are distinct.

All P vertices lie within M of the original normalized centroid 0, so matched
vertices are at distance ≤2Mδ. Taking convex hulls and using B⊂S gives

    K⊂P⊂S+2Mdρ B⊂(1+2Mdρ)S.

This implies E(K,S)≤2Mdρ≤aSharp e^(1/(d−1)); the original aSharp has factor
4, so there is slack. The admissible set in the sInf definition has lower
bound 0 and contains this actual nonnegative dilation, justifying the excess
inequality without an empty-infimum convention. At e=0 all errors vanish;
no division by e or h is needed, and the exact permutation endpoint applies.

For e≥eSharp, the old coarse bound E≤R0−1 gives the second original gSharp
branch. Finally the same affine map f used to normalize the input S satisfies
f(c_S)=0 and f(c_S+(1+a)(S−c_S))=(1+a)f(S). Thus the literal original
centroid is restored. This chain preserves ∀S; auxiliary w and P are allowed
to depend on S and do not weaken the universal quantifier.

### Classical route versus the constructed law

The original paper's first-variation route is also mathematically sound:
the genuine surface-area cone law gives
I=V(K[d−1],P)/|K|, and Minkowski's first inequality yields α≤I^d.
For the formal compact-limit witness, that identification cannot merely be
asserted for a separately named surface law. It must be passed from the same
finite support sums, exactly as the conditional 627 interface proposed.
The new radial route avoids needing this additional classical formalization.

## 6. Actual-body negative control: brightness cannot supply scale

In R^3 let N be the four sign vectors in {−1,1}^3 whose coordinate product is
+1, and define

    P={x:n·x≤1 for every n∈N},
    K=P∩(−P)={x:|x_1|+|x_2|+|x_3|≤1}.

P is the actual regular tetrahedron with vertices −n, n∈N; K is the actual
octahedron. Their Euclidean volumes are |P|=8/3, |K|=4/3.
All four original support contacts remain: h_K(n)=h_P(n)=1.

P's four facets have unit normals n/√3, support height 1/√3 and area 2√3;
its actual cone law therefore places mass 1/4 at each n.
K's eight facets have unit normals ±n/√3, support 1/√3 and area √3/2;
its actual cone law places mass 1/8 at every ±n. Thus, for every u,

    ∫|u·x|dν_K = (1/8)Σ_{±n}|u·(±n)|
                 = (1/4)Σ_n|u·n| = ∫|u·x|dν_P.

Both laws are centered and all their weights are strictly positive. Cauchy's
actual formula gives normalized projection-volume equality in **every**
direction, while |P|/|K|=2 and π_P=2π_K, so absolute deficits are not zero.
Scaling both bodies by √3 puts a Euclidean unit ball inside K and puts P
inside the radius-3 ball; then all cone atoms have norm 1. Thus this is not
an artifact of a missing inner-ball or outer-radius normalization.

The missing scale is detected exactly by the non-even support test:
h_P(n)=1, h_P(−n)=3, so ∫h_Pdν_K=2, not 1. The actual assignment error is
nonzero. The candidate uses this support test and that error, so the example
is a negative control for an invalid shortcut, not a counterexample to Main.

More generally the same phenomenon occurs for a centered regular simplex P
and K=P∩(−P) in every d≥2: symmetry makes the actual laws uniform on w_i
and ±w_i respectively, giving identical absolute directional moments.

A second guard concerns polar boundedness: affinely independent actual
support anchors and an absolutely small cost do not suffice without a
uniform directional roundness gate. For K=L[−1,1]^d, its actual law is uniform
on ±e_i/L. Select anchors e_1/L, e_2/L, −e_2/L, e_3/L,…,e_d/L.
They are affinely independent actual support atoms; their largest-barycentric
assignment cost is (d−1)√2/(2dL)→0, but their polar is unbounded in negative
coordinate directions. The required h≤b relative to a fixed normalized
roundness excludes this example. There is no inference of boundedness from
support membership alone.

## 7. Candidate source-semantic inspection

`FiniteRadialSupportScale.lean` has six actual proofs. Its volume bound uses
measure subadditivity and finite compact cones, proves finiteness before
ENNReal.toReal monotonicity, and passes through the supplied μ,φ. No Q⊂P
hypothesis appears. Its finite lower-height and support-gap conditions are
discharged for actual supporting approximants.

`PolarSimplexConstruction.lean` uses the supplied affine basis, its coordinate
gradients and `q_i=−λ_i⁻¹ℓ_i`. Positive weights are proved using the interior
of that exact convex hull. Its simplex/halfspace identity, radius bound,
injective normalized normals, positive heights and exact facet-atom equality
are conclusions, not assumed geometry. Its original-radius wrapper consumes
the literal fixed-K polar-boundary level set from the same supplied anchors.

`OriginalRadialScale.lean` explicitly proves Q absorbs M^(d−1)c and consumes
the stronger same-assignment bound before Bernoulli's inequality. Its final
scale statement has no finite-Minkowski hypothesis.

`SharpUpperMain.lean` destructs `actual_body_joint_polar_pyramid_assignment`
once. It uses those same μ,φ,w and `largestCoordinate (anchorCoordinates w x)`
for roundness, the actual polar construction, and the radial cap consumer.
`sharpLocal` normalizes the caller's S and rewrites back with hE and hdef.
`sharpMain : sharpMainGoal` takes the original d,K,S,maximality arguments and
uses actual nonnegativity, that local theorem and the already proved coarse
bound. The interior hypothesis is unused because existence of a genuine
maximum d-simplex already guarantees the needed full dimensionality; this
does not weaken the statement.

No source-semantic substitution of a proxy invariant, preferred S, alternate
centroid, changed exponent or enlarged gSharp was observed. The candidate's
exact full-source and transitive-kernel audit is delegated separately.

## 8. Rational corroboration and reproducibility

Run `python3 exact_controls.py` and `python3 -O exact_controls.py` in this
directory. Both ran successfully and produced identical output. Checks use
explicit exceptions rather than removable Python assertions.

- d=2,…,6: exact affine inverses, polar pairings, positive λ, the additional
  λ≥b/(1+b), radius and dual barycentric reconstruction on 3262 rational
  convex combinations in total.
- The literal rational tetrahedron/octahedron example: exact volumes 8/3
  and 4/3, all support contacts, normalized projection equality in 124
  rational test directions, and support-test I=2. The preceding all-direction
  analytic proof is not replaced by these finite tests.
- Actual iid determinant enumeration for the octahedron cone law gives
  A=3/2, B=45/16, D=21/16; the already audited actual identity gives e=7/32
  and D/B=7/15. This is a corroborating geometric counterexample calculation,
  not new truncation work.
- d=3,…,8: exact rational original-Q absorption and root-free threshold
  inequalities, including zero cost and endpoint cases.

The final review deliberately claims a traditional proof and targeted
source-semantic PASS, not a fresh compilation or independent kernel PASS.

## 9. Formal-delivery blocker reported at handoff

At 20:07 UTC the parent reported that the new Main delivery is missing source
for `SelectedAnchorHullRoundness` and the author is supplying it. This is a
source-completeness / formal-reconstruction blocker, separate from this
traditional mathematical review. The same-anchor hull-roundness argument is
proved above from the actual directional lower bound and the assignment cost;
that mathematical proof does not replace the absent Lean source or permit
claiming an independent full-kernel PASS. No mathematical source was changed
by this reviewer, and no author build or cached proof was substituted for the
missing formal delivery.
