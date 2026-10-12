# The full Lp phase diagram and interval distances of a nested train-track family

Date: 8 October 2026. Status: new proof candidate, not independently audited. The previous 512-line positive-repair note is frozen and not modified by this extension.

## 1. Results

For every rational 1<alpha<2, the explicit deterministic nested construction below gives two compact separated planar sets E_- and E_+, and probabilities lambda and mu supported on them, such that:

* Both sets have Hausdorff dimension alpha and packing dimension two. Both probabilities are alpha-Frostman. Each coordinate marginal is singular with respect to Lebesgue measure.
* For the original cross-distance law nu_p=(y -> |y-p|)_*mu, uniformly for all pins p in a whole fixed rectangle containing E_-, the exact upper integrability statement is

      nu_p has an L^{q_alpha} density,

  where

      q_alpha = (2-alpha)/(3-2alpha)  if 1<alpha<3/2,
      q_alpha = infinity            if 3/2<=alpha<2.  (1.1)

* If 1<alpha<3/2, then for every p in E_-, the original density fails to belong to every finite L^q with q>q_alpha. Thus the finite critical exponent is attained, not merely approached.
* At alpha=4/3, the original laws are uniformly in L^2 for all p in P_-. For every p in P_- with p_1 in H=supp kappa (in particular, every p in E_-), they fail every L^{2+epsilon}; for p_1 outside H, the original density is continuous and bounded. At alpha=3/2, the original density is bounded and jointly continuous in the pin and distance variables. Joint continuity holds throughout 3/2<=alpha<2.
* For every 1<alpha<2, deleting the one fixed horizontal band |y_1-p_1|<epsilon gives a positive distance sublaw with a jointly continuous density bounded by C/epsilon. Its lost mass is at most K epsilon^{alpha-1}, uniformly in p.
* Consequently, for every 1<alpha<2, **every pin in E_- has an interval in its actual cross-distance set to E_+**, and the interval length has a positive lower bound independent of the pin. The reversed cross-distance conclusion also holds. Thus every pin in E_- union E_+ has an interval in its distance set to that union.

These are statements about one explicitly realized structured family. They are not unrestricted dimension thresholds. The finite-scale far-track smoothing idea is classical; the present candidates are the exact nested integrability phase diagram, its attained endpoints, and the quantitative fixed positive-filter route to interval distances.

## 2. The actual construction throughout 1<alpha<2

Put

    a=(alpha-1)/2,    b=alpha/2,    beta=alpha-1.

Thus 0<a<1/2<b<1 and b-a=1/2. Choose positive stage lengths L_j so that aL_j, L_j/2 and bL_j are integers. Write n_0=0 and n_j=sum_{i<=j}L_i, and impose only

    L_j/n_{j-1} -> infinity       (j>=2).             (2.1)

No condition involving 2-3alpha/2 is imposed in this enlarged family. That expression is relevant only to the earlier non-L^2 example, not to existence of the construction.

At each stage j, the free horizontal binary positions are [1,aL_j] and (L_j/2,L_j]; the free vertical positions are [1,bL_j]. All remaining digits are zero. Free bits are mutually independent and fair. Let kappa_X,kappa_Y be the resulting compactly supported coordinate probabilities.

Choose k with eta=2^{-k}<1/8 and choose L_1 sufficiently large that the first k positions are free in both coordinates. Condition kappa_X on its all-zero prefix of length k, obtaining kappa. Condition kappa_Y on the all-zero and all-one prefixes of length k, obtaining zeta_- and zeta_+. Define

    E_- = supp(kappa x zeta_-),    lambda=kappa x zeta_-,
    E_+ = supp(kappa x zeta_+),    mu=kappa x zeta_+.

These are coding-cylinder supports, so dyadic endpoint conventions do not introduce additional zero-mass points. In particular,

    E_- subset P_-=[0,eta]^2,
    E_+ subset P_+=[0,eta] x [1-eta,1].               (2.2)

For p in P_- and y in P_+, set

    v_0=1-2eta>0,    D_0=2.

Then y_2-p_2>=v_0 and |y-p|<=D_0. The positive vertical derivative |partial_{y_2}|y-p|| is therefore at least v_0/D_0. This is a real geometric separation, uniform over all stages and all pins in P_-.

A completely specified choice for any rational alpha is: let d be a positive integer with ad, bd and d/2 integral, choose L_1 a sufficiently large multiple of d, and set

    L_j=d(n_{j-1}+1)^2    for j>=2.

This realizes (2.1) and every stated integer condition.

### 2.1 Frostman, dimensions, and singular coordinates

At a relative stage depth 0<=l<=L, the new free-position counts are

    f_X(l)=min(l,aL)+max(0,l-L/2),
    f_Y(l)=min(l,bL).

Their sum is

    2l                         for 0<=l<=aL,
    l+aL                       for aL<=l<=L/2,
    2l-(1-b)L                  for L/2<=l<=bL,
    l+(alpha-1)L               for bL<=l<=L.

Each expression is at least alpha*l; at l=L the sum is exactly alpha L. Thus, at every depth n,

    F_X(n)+F_Y(n)>=alpha n,
    F_X(n_j)=F_Y(n_j)=b n_j.                          (2.3)

After the fixed prefix conditioning, every occupied depth-n square has mass 2^{2k-F_X(n)-F_Y(n)}. A ball of radius comparable to 2^{-n} meets a bounded number of such squares, so the measures are alpha-Frostman. At n=n_j, at most C2^{alpha n_j} squares cover the support. This gives Hausdorff dimension at most alpha; the Frostman bound gives equality.

Every fixed coding cylinder has upper box dimension two. Indeed, at arbitrarily late stages the first aL_j positions are free in both coordinates, giving at least 2^{2aL_j} occupied squares at depth n_{j-1}+aL_j inside a fixed later cylinder. By (2.1),

    2aL_j/(n_{j-1}+aL_j) -> 2.

Every nonempty relatively open support subset contains a coding cylinder. In any countable cover used in the modified-upper-box definition of packing dimension, take relative closures; closure preserves upper box dimension. By Baire's theorem one closure contains a nonempty relatively open subset, which has upper box dimension two. Hence the packing dimension is two.

At depth n_j each coordinate support is covered by at most C2^{bn_j} intervals of length 2^{-n_j}. Since b<1, their total lengths tend to zero. Both coordinate laws therefore have Lebesgue-null supports. They are nonatomic because their free-position counts tend to infinity. In fact

    F_X(n)>=beta n,
    kappa([u-epsilon,u+epsilon])<=K_X epsilon^beta    (2.4)

for all u and 0<epsilon<=1. The first inequality follows from f_X(l)>=beta l and b>=beta at stage endpoints; the interval bound then follows from the dyadic masses. The limiting measure is never given a hidden Lebesgue coordinate.

## 3. Filled tails and actual rectangular replacements

Fix a stage j_0 with n_{j_0}>=k. Let mu_j preserve the first n_j digits of mu and replace all later digits in both coordinates by independent fair bits. Thus mu_j is a finite probability mixture of uniform depth-n_j squares, and mu_j converges weakly to mu.

Inside a parent square Q of side h=2^{-n}, n=n_{j-1}, the conditional law of mu_{j-1} is uniform. The conditional law of mu_j is the affine image of

    xi_{A,w} x zeta_{B,v},

where

    xi_{A,w}=(1/A) sum_{i=0}^{A-1} Unif[i/A,i/A+w],
    zeta_{B,v}=(1/B) sum_{l=0}^{B-1} Unif[l/B,l/B+v],

and

    A=2^{aL}, B=2^{bL}, w=2^{-L/2}, v=2^{-L}, L=L_j.

The exact identities and inequalities are

    Bw=A,    Bv=2^{-(1-b)L},    w<=1/A,    v<=1/B.     (3.1)

Every parent keeps its exact original mass. These are geometrically placed rectangles and actual filled-tail approximants, not just prescribed child counts.

For a function H of bounded variation on [0,1], any probability assigning exactly 1/N mass to each equal bin satisfies

    |int H dxi-int H du|<=Var(H)/N.                  (3.2)

Indeed, bound the difference of conditional averages in each bin by its oscillation and sum with weight 1/N. Both xi_{A,w} and zeta_{B,v} have this property.

## 4. Two positive quadrature estimates

Write M_epsilon(p,y)=1_{|y_1-p_1|>=epsilon}. Let rho_Q be the rectangular replacement from Section 3, and U_Q uniform probability on Q.

### Lemma 4.1 (fixed band)

Their masked distance densities satisfy

    ||(D_p)_*(M_epsilon rho_Q)-(D_p)_*(M_epsilon U_Q)||_infinity
       <= (4D_0/h)[1/(v_0 A)+1/(epsilon B w)].         (4.1)

All pushforwards are unnormalized positive laws before their difference is taken.

**Proof.** Use local output t=|y-p|/h. Returning to physical distance multiplies a density by h^{-1}. On a horizontal strip of relative width w, and at fixed output radius r=ht, the two possible horizontal roots are

    X-p_1=+/-sqrt(r^2-(Y-p_2)^2).

On either retained side of the band, as Y increases, r/|X-p_1| is monotone. Membership of the root in the fixed strip cuts out an interval of Y. The density of the horizontal pushforward, with its original 1/w factor, is thus a sum of at most two zero-extended monotone interval functions. Each has supremum at most D_0/(epsilon w); its total variation is at most twice that supremum. The total vertical variation is at most 4D_0/(epsilon w). Use (3.2) to replace zeta_{B,v} by the full uniform vertical coordinate, at an error 4D_0/(epsilon Bw), and average the horizontal strips with weights 1/A.

With the vertical coordinate uniform, its single positive-root density is r/(Y-p_2), at most D_0/v_0. On each side of X=p_1 it is monotone, and the vertical rectangle bounds and the band leave at most one interval on each side. Its horizontal total variation is at most 4D_0/v_0. Apply (3.2) to xi_{A,w}, costing 4D_0/(v_0 A). Restore the physical output scale. This proves (4.1). The branch formula is a coarea formula on strictly monotone intervals; the fixed band excludes the only horizontal critical point. QED.

### Lemma 4.2 (harmonic gain)

At epsilon=h/A, the improved bound is

    ||difference||_infinity
       <= C D_0[1/(h v_0 A)+log(2A)/(h^2 Bw)].        (4.2)

**Proof.** On horizontal strip I_i, let d_i be its minimum retained physical horizontal distance from p_1, ignoring empty strips. The first variation estimate above is at most 4D_0/(w d_i), and d_i>=h/A. The strips lie in separate equal coarse bins of length h/A. Ordering the bins to each side of p_1 gives

    (1/A) sum_i d_i^{-1} <= C h^{-1}log(2A).         (4.3)

Apart from a bounded number of nearest bins, the l-th bin has separation at least a fixed multiple of l h/A; the nearest bins are covered by the cutoff. The same estimate holds if p_1 lies outside Q. Sum this sharper variation over strips before taking the vertical quadrature error. It is at most C D_0 log(2A)/(h Bw) in local output scale, hence the second term of (4.2) physically. The horizontal quadrature term is unchanged. QED.

These two estimates retain the same pin throughout. They are elementary structured-resolution estimates, and are not consequences of the Frostman inequality alone.

## 5. Fixed positive filters: bounded and jointly continuous densities

### Theorem 5.1

For every fixed 0<epsilon<=1,

    nu_{p,epsilon}=(D_p)_*(M_epsilon(p,.)mu)

has a jointly continuous density g_epsilon(p,r) on P_- x R, with

    0<=g_epsilon(p,r)<=C_*/epsilon,
    nu_{p,epsilon}(R)>=1-K_X epsilon^{alpha-1}.       (5.1)

The constant is finite for this one specified construction and independent of p.

**Proof of boundedness and limit identification.** Use Lemma 4.1 inside each parent and sum with its exact mass. Since Bw=A and the masses sum to one,

    ||g_{j,p,epsilon}-g_{j-1,p,epsilon}||_infinity
      <=4D_0(v_0^{-1}+epsilon^{-1})2^{n_{j-1}-aL_j}. (5.2)

The series S=sum_{j>j_0}2^{n_{j-1}-aL_j} is finite by (2.1). The initial filled-tail density is bounded by (D_0/v_0)2^{n_{j_0}}. Hence the stage densities converge in L-infinity uniformly in p, with one allowable bound

    C_*=(D_0/v_0)2^{n_{j_0}}+4D_0(1+v_0^{-1})S.

The two moving boundary lines y_1=p_1 +/- epsilon have zero mu-mass by (2.4). For each p, weak convergence therefore identifies the limit of the masked approximants with nu_{p,epsilon}. The mass estimate in (5.1) is (2.4).

**Proof of joint continuity.** Every mu_j has a bounded density f_j that is a finite linear combination of rectangle indicators. Polar coarea gives the version

    g_{j,epsilon}(p,r)
      = r int_0^{2pi} f_j(p+r omega(theta))
                          1_{|r cos(theta)|>=epsilon} dtheta,
                                                            (5.3)

for r>0, extended by zero where the separated source geometry forces no mass. Fix any p,r with r>0. A circle meets the finite rectangle boundaries at finitely many angular points. The equality |r cos(theta)|=epsilon likewise has only finitely many angular solutions when it has any. Consequently the integrand in (5.3) is continuous in (p,r) for almost every theta, and its finite bounded majorant permits dominated convergence. Thus (5.3) is jointly continuous. There is no issue at r=0: all source distances are at least v_0, uniformly in p.

A continuous function's supremum over r equals its essential supremum. Thus (5.2), already uniform in p, is a genuine uniform bound on P_- x R for these continuous versions. They converge uniformly to a jointly continuous function. Its fibers are the densities already identified. QED.

The raw law is absolutely continuous at every pin for every alpha>1: let epsilon decrease to zero, and use monotonicity of the positive masked laws and mu{y_1=p_1}=0. This assertion alone does not give an L^2 bound.

## 6. The full attained upper phase diagram

For 1<alpha<3/2, put q=q_alpha from (1.1); for 3/2<=alpha<2 put q=infinity. Interpret

    sigma=1-1/q,    1/infinity=0.

### Theorem 6.1

The unfiltered densities obey

    sup_{p in P_-} ||d[(D_p)_*mu]/dr||_q < infinity.   (6.1)

If q=infinity they can be chosen jointly continuous on P_- x R.

**Proof.** At stage j put n=n_{j-1}, L=L_j, h=2^{-n}, and use the auxiliary band epsilon_j=h/A. It is only a proof decomposition of the unfiltered stage increment.

**Away from the band.** Lemma 4.2 and Bw=A show that the global density increment away from the band is bounded in supremum norm by

    C(1+L)2^{2n-aL}.                                (6.2)

There is no cell-count factor because the parent masses sum to one. All outputs have support in the fixed bounded interval [v_0,D_0], so the same expression, with an adjusted constant, bounds its L^q norm for finite q. The series in (6.2) is summable. Indeed, eventually log_2(1+L)<=aL/2 and aL/2>=3n, leaving C2^{-n}.

**Inside the band.** At depth n each occupied horizontal prefix interval has kappa-mass 2^{k-bn}. The band of length 2h/A meets a bounded number of the next stage's globally aligned horizontal coarse bins, each of mass 2^{k-bn}/A. Thus the horizontal band masses for mu_j and mu_{j-1} satisfy

    M_j,M_{j-1} <= C_k A^{-1}2^{-bn}.                (6.3)

The filled-tail vertical densities are bounded by

    H_j=2^{k+(1-b)(n+L)},
    H_{j-1}=2^{k+(1-b)n}.                            (6.4)

These are actual global product laws. A horizontal-band restriction preserves independence from the vertical marginal. Vertical coarea implies that a product law with horizontal mass M and vertical density at most H has distance density bounded by (D_0/v_0)MH. Interpolating this bound with its mass M gives

    ||band density||_q <= C M H^sigma,              (6.5)

including q=infinity, where (6.5) is simply the supremum bound, not a limiting argument.

For the current stage the exponent on the right is

    C 2^{[-b+(1-b)sigma]n}
                         2^{[-a+(1-b)sigma]L}.      (6.6)

If alpha<3/2, the critical exponent gives (1-b)sigma=a, so (6.6) is exactly C2^{-(b-a)n}=C2^{-n/2}. If alpha>=3/2, sigma=1 and it is

    C 2^{-(alpha-1)n}2^{-(alpha-3/2)L}
       <= C2^{-n/2}.                               (6.7)

The previous stage has a still smaller bound. Hence the sum of the two inside-band L^q norms is summable in j.

Combining (6.2) and (6.6)-(6.7), the original, unmasked filled-tail densities are Cauchy in L^q, uniformly in p. Their finite initial density is bounded. Weak convergence mu_j->mu and continuity of distance identify the limit with the actual original distance law; no discontinuous mask remains in the final identification. For finite q, the common bounded support also gives L^1 convergence.

When q=infinity, the unmasked finite densities are jointly continuous by the argument (5.3) without its band indicator. The stage-increment estimates are uniform supremum bounds on continuous functions. Their uniform limit is jointly continuous and is the required raw density. QED.

The alpha=3/2 conclusion is therefore a real endpoint theorem: its inside-band estimate is precisely C2^{-n/2}. It is not obtained by formally letting a finite exponent tend to infinity.

## 7. Sharpness below alpha=3/2

Fix p in E_-. At stage j, let the source horizontal track be the occupied depth-(n+L/2) coding interval containing p_1. It has horizontal width 2^{-n-L/2} and source mass

    m_j=2^{k-bn-aL}.                                (7.1)

The vertical source support has at most

    N_j=2^{b(n+L)-k}

occupied depth-(n+L) intervals. For points in the indicated track,

    0<=|y-p|-(y_2-p_2)
      <=(y_1-p_1)^2/(2v_0)
      <=C2^{-(n+L)}.

Thus its distance image is contained in a set U_j of measure at most

    |U_j|<=C2^{(b-1)(n+L)-k}.                       (7.2)

The same assertion holds at coding endpoints by choosing a supporting closed coding interval; its exact mass and diameter bounds persist. If the raw distance density belonged to finite L^r, Holder's inequality and nu_p(U_j)>=m_j would give

    ||g_p||_r^r >= c_r
       2^{[r(3/2-alpha)-(1-alpha/2)]L
                      +[r(1-alpha)-(1-alpha/2)]n}.   (7.3)

For alpha<3/2, the coefficient of L is positive exactly when r>q_alpha. Superlacunarity makes the right side diverge, uniformly over the original pins. Hence g_p is not in L^r for any r>q_alpha. Since its support is bounded, this also excludes L-infinity.

Combining Theorem 6.1 and (7.3) gives the following phase diagram. The upper bounds hold for all p in P_-; every nonmembership statement in this list is restricted to p_1 in H (in particular, p in E_-). Off H, the original density is continuous and bounded:

    1<alpha<4/3:     attained finite q_alpha<2; no L^2
    alpha=4/3:       L^2, but no L^{2+epsilon}
    4/3<alpha<3/2:   attained finite q_alpha>2
    alpha=3/2:       bounded jointly continuous density
    3/2<alpha<2:     bounded jointly continuous density.

For the last two ranges all finite L^r spaces follow from boundedness and compact support. No statement about an optimal modulus of continuity is being made here.

## 8. Actual distance intervals for every alpha>1

### Theorem 8.1

For the one fixed construction, there is an ell>0 such that every p in P_- has an interval of length ell contained in D_p(E_+). In particular this holds for every p in E_-. The analogous reversed assertion holds from P_+ to E_-.

**Proof.** Choose one fixed epsilon_0>0 so small that K_X epsilon_0^{alpha-1}<=1/2. The jointly continuous nonnegative density g_{epsilon_0}(p,r) from Theorem 5.1 has mass at least 1/2 for every p. All these densities vanish outside [v_0,D_0]. If W=D_0-v_0, every pin therefore has some r_p with

    g_{epsilon_0}(p,r_p)>=1/(2W).

Joint continuity on the compact pin/output domain, with the densities extended continuously by zero, gives one delta>0 such that

    |r-r_p|<=delta  implies
    g_{epsilon_0}(p,r)>=1/(4W),

uniformly in p. Thus its support contains [r_p-delta,r_p+delta]. The submeasure is the pushforward of an actual positive restriction of mu. Its support is contained in D_p(E_+), which is compact as the continuous image of a compact set. Hence this whole interval belongs to the actual distance image. Taking ell=delta, or any smaller fixed length, proves the assertion without an endpoint convention.

For the reversed configuration, y_2-p_2<=-v_0. There is still one monotone vertical branch, the same absolute derivative lower bound, and the circle-branch variations are monotone with the reversed sign. All proofs above therefore apply with unchanged constants to source E_- and pins in P_+. QED.

For alpha<3/2, the raw density can be unbounded, and for alpha<4/3 its L^2 norm is infinite at every original pin. Neither fact prevents its actual distance set from containing an interval. The positive continuous sublaw, not raw boundedness, supplies the interval in those ranges.

## 9. Positive masks and the exact scope of stability

Fix epsilon>0. Any jointly Borel 0<=F(p,y)<=M_epsilon(p,y) produces an unnormalized distance density dominated pointwise by g_epsilon(p,r). If its source mass is m(p), then

    ||density||_2^2 <= (C_*/epsilon)m(p),
    ||normalized density||_2^2 <= C_*/[epsilon m(p)]  (m(p)>0).

The division by m(p)^2 in squared L^2 normalization is included; the first bound already contains one factor m(p). A uniform retained-mass lower bound must be supplied if uniform normalized estimates are wanted.

For alpha>=3/2, Theorem 6.1 bounds the original density itself. The same statements then hold for every 0<=F<=1 without first removing a band, with its raw L-infinity bound in place of C_*/epsilon. This gives an original-law positive common-pin gate on the entire high-alpha portion of this structured family.

A source displacement of at most A_delta*delta, using the same pin in both distances, only enlarges an original collision window delta to (1+2A_delta)delta. Therefore these bounded positive laws give the corresponding collision and whole-low-pass bounds, with the retained mass accounted for. They do not give decaying high-frequency shells for arbitrary scale-dependent masks or jitters.

The fixed-band theorem survives additional positive pruning by domination. Multiplying a prior filter by the band does not automatically preserve each cell's previously asserted relative retained mass. Such local mass requirements must still be checked or re-pruned with their actual budget.

## 10. Inputs, literature, and limitations

The source geometry and every bound used here are proved above. The analysis uses elementary quadrature for functions of bounded variation, one-variable coarea, weak convergence, dominated convergence, interpolation between L^1 and L-infinity, and Holder's inequality. No generalized-projection theorem, random-martingale theorem, or unrestricted common-pin result is an input.

[Guth-Iosevich-Ou-Wang, arXiv:1808.09346v1](https://arxiv.org/html/1808.09346v1), Section 1.2, already describes why tracks far from a pin have well-distributed distances; Section 6 presents the train-track obstruction. That finite-scale insight is not new here. The present candidate identifies a complete nested all-pin conclusion for this explicit family, including its attained L^q index and interval support. No claim that the full result is absent from the entire literature has been verified.

The actual stagewise rectangular placement and the resolving relation Bw=A are essential hypotheses. Frostman dimension, packing dimension, or a branching-count profile alone does not imply them. Arbitrary rotated descendants, arbitrary masks inserted before the replacement comparison, and the full family-073 recursion are not covered. The exact index proof additionally uses the true global product structure to estimate the narrow horizontal band.

The prior positive-repair candidate is preserved at:

    research_math/round8_pinned_traintrack_repair_20261008/TRAINTRACK_POSITIVE_REPAIR.md
    SHA-256 aa85b4e46f8752754ce187d8413d200763d87639997f73b0782f874eefb79f81.

The present file extends its range and adds joint continuity and actual interval distances; it does not overwrite that earlier candidate. Neither file has yet received the deferred independent review.
