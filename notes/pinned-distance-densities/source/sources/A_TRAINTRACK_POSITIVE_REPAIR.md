# A fixed positive repair of the nested train-track obstruction

Date: 8 October 2026. Status: complete proof for review; no independent audit yet. This note makes no unrestricted pinned-Falconer claim and no claim of priority over all related literature.

## 0. New conclusion and its relation to the old obstruction

For the **same nested digit train-track source and pin sets** constructed in `common_pin_traintrack_received/source/nested-train-track-obstruction.md`, with the already permitted superlacunarity condition, the following are simultaneously true:

* Every original pin's original distance probability is absolutely continuous. Its density is uniformly in L^{q_*}, where q_*=(2-alpha)/(3-2alpha). Together with the lower bound below, this determines its exact L^q integrability range, including the endpoint. A simpler fixed-mask argument also gives a uniform weak-L^alpha bound.
* None of those original distance laws is in L^2 when 1 < alpha < 4/3. More generally, the proof below rules out L^q for q > (2-alpha)/(3-2alpha).
* For every fixed epsilon > 0, delete only the horizontal diagonal band |y_1-p_1| < epsilon. The actual positive surviving source law has a distance density bounded by C/epsilon, **simultaneously for every pin**. The deleted mass is at most K epsilon^(alpha-1), uniformly in the pin.
* This one scale-independent positive mask controls every further positive pin-dependent mask. It is not a sequence restoring the original source law while retaining a uniform L^2 bound.

The main new proof obligation, not supplied in the old obstruction, is a two-step bounded-variation quadrature estimate. It quantifies the density error of a whole train-track replacement and makes the errors summable in a genuinely nested construction. The raw-law absolute-continuity conclusion is stronger than saying its distance support has positive measure, and compatible with the old all-pin L^2 obstruction.

The finite-scale intuition that tracks away from a pin have well-distributed distances already appears in GIOW, Section 1.2. The contribution asserted here is the explicit theorem and proof for this nested model, including its fixed positive mask, boundary limit, weak-L^alpha bound, and all-pin quantifiers. Literature novelty beyond that comparison remains unestablished.

## 1. Exact construction and hypotheses

Fix rational 1 < alpha < 4/3 and put

    a = (alpha-1)/2,    b = alpha/2,    beta = alpha-1,
    e = 2-3alpha/2 > 0.

Let L_j be positive integers for which a L_j, L_j/2 and b L_j are integers. Set n_0=0 and n_j=sum_{i<=j} L_i. We assume the conditions already used by the old construction:

    e L_j - alpha n_{j-1} -> +infinity,
    L_j / n_{j-1} -> +infinity.                         (1.1)

The second statement is understood for j>=2. It alone implies the summability needed in the positive proof:

    S = sum_{j>j_0} 2^[n_{j-1}-a L_j] < infinity         (1.2)

for every fixed j_0. Indeed, eventually a L_j >= 2 n_{j-1}, and n_{j-1} >= j-1; the tail is bounded by sum 2^{-(j-1)}.

In each stage, the free binary positions of the horizontal coordinate are

    [1,a L_j] union (L_j/2,L_j],

and those of the vertical coordinate are [1,b L_j]. All other digits are zero; all free digits are independent fair bits. Let kappa_X and kappa_Y be the resulting coordinate probabilities.

Choose eta=2^{-k}<1/8, with the first k positions free in both coordinates. As in the old construction, condition kappa_X on the all-zero length-k prefix to obtain kappa, and condition kappa_Y on the all-zero and all-one length-k prefixes to obtain zeta_- and zeta_+. Define

    lambda = kappa x zeta_-,    mu = kappa x zeta_+.

These are exactly the old separated pin and source laws. In particular,

    supp lambda subset [0,eta] x [0,eta],
    supp mu subset [0,eta] x [1-eta,1].                 (1.3)

The positive proof actually works for every pin in the whole rectangle

    P = [0,eta] x [0,eta].

Throughout, use the fixed geometric constants

    v_0 = 1-2eta > 0,
    D_0 = 2.

For every p in P and every source point or filled-tail source approximant, y_2-p_2 >= v_0 and |y-p| <= D_0. Thus the second-coordinate distance derivative is bounded below by v_0/D_0. This is furnished by the original geometry, not an additional hypothesis on the fractal coordinates.

Let j_0 be any fixed stage endpoint with n_{j_0}>=k. For j>=j_0, let mu_j have the same first n_j digits as mu, and replace all later digits in each coordinate by independent fair bits. Equivalently, mu_j is uniform inside each occupied depth-n_j dyadic source square, carrying that square's exact mu-mass. Then mu_j converges weakly to mu. The fixed prefix conditioning is included throughout.

### A fully specified realization

For example, take alpha=13/10, eta=1/16, L_1=40, and

    L_j=20(n_{j-1}+1)^2   for j>=2.

All required integer positions exist, the first four digits are free in both coordinates, and both conditions (1.1) hold. The first error exponent after the base stage is n_1-aL_2=40-5043=-5003. This is one completely determined pair of compact digit sets and probabilities, not a formal assignment of profiles. No finite computer representation of its enormous later generations is needed for the proof.

### Horizontal nonconcentration

For each depth n, the number F_X(n) of free horizontal digits satisfies

    F_X(n) >= beta n.                                  (1.4)

Within a stage this follows from

    min(l,aL) + max(0,l-L/2) >= beta l,

and it also holds at previous endpoints since b>=beta. An interval of length comparable to 2^{-n} meets a bounded number of depth-n dyadic intervals. Conditioning on the fixed prefix costs only 2^k. Consequently, for some fixed K_X,

    kappa([u-epsilon,u+epsilon]) <= K_X epsilon^beta    (1.5)

for all real u and 0<epsilon<=1. In particular kappa is nonatomic. Neither kappa nor zeta_+ has an absolutely continuous coordinate law: infinitely many prescribed digits remain frozen.

For reference, the old note proves that lambda and mu are alpha-Frostman, with Hausdorff dimension alpha and, under (1.1), packing dimension two. No one of those dimension conclusions is used as a substitute for the explicit geometry in this positive proof.

## 2. The quadrature fact

Let U be uniform probability on [0,1]. If a probability xi assigns mass exactly 1/N to each of the N half-open intervals [i/N,(i+1)/N), then for every function H of bounded variation,

    |int H dxi - int H dU| <= Var(H)/N.                (2.1)

The same bound holds with endpoint conventions that assign each mass to its own closed bin. To prove it, compare the two conditional averages in each bin. Their difference is bounded by the oscillation of H there. Sum with weight 1/N; the sum of bin oscillations is at most total variation. At jump endpoints one can use one-sided representatives or approximate the quadrature measures. Our applications are either absolutely continuous within bins or have explicit nonambiguous endpoint limits.

For integers A,B>=1 and numbers 0<w<=1/A, 0<v<=1/B, put

    xi_{A,w} = (1/A) sum_{i=0}^{A-1} Unif[i/A,i/A+w],
    zeta_{B,v} = (1/B) sum_{l=0}^{B-1} Unif[l/B,l/B+v].

Both satisfy (2.1), with N=A and N=B respectively. Notice that no randomness or Fourier cancellation is being assumed.

## 3. A positive density comparison for one whole replacement

### Lemma 3.1 (two-coordinate resolution)

Let Q=[q_1,q_1+h] x [q_2,q_2+h], with 0<h<=1. Let p satisfy

    y_2-p_2 >= v_0,    |y-p| <= D_0      for every y in Q.

Let U_Q be uniform probability on Q, and let rho_Q be the affine image of xi_{A,w} x zeta_{B,v} under (u,z) -> (q_1+hu,q_2+hz). Define the same hard positive mask for both laws by

    M_epsilon(p,y) = 1_{|y_1-p_1| >= epsilon}.

Then both masked distance pushforwards have densities, and

    || (D_p)_*(M_epsilon rho_Q)
          - (D_p)_*(M_epsilon U_Q) ||_{L-infinity}
      <= (4D_0/h) [1/(v_0 A) + 1/(epsilon B w)].       (3.1)

Here and below D_p(y)=|y-p|. The norm in (3.1) is the norm of the difference of densities. No probability normalization after the mask is performed.

#### Proof

Use the output coordinate t=D_p(y)/h, which contributes the final h^{-1} on returning to physical distance. Additive constants in t are immaterial. Write X=q_1+hu and Y=q_2+hz.

**First average in the vertical coordinate.** Fix one horizontal strip i/A <= u <= i/A+w, and retain its part with |X-p_1|>=epsilon. This is the union of at most two intervals, one on either side of p_1. For each fixed z, the distance image of uniform horizontal measure, with its original density 1/w and with the mask, has density at t

    G_i(z,t) = (1/w) sum over allowed roots X
                         [ |y-p| / |X-p_1| ].          (3.2)

For a fixed output t, the physical radius r=ht is fixed. The two possible roots are

    X-p_1 = +/- sqrt(r^2-(Y-p_2)^2).

On either branch, Y-p_2 is positive. As z increases, |X-p_1| decreases, so r/|X-p_1| increases monotonically. Requiring the root to lie in one specified horizontal interval cuts out an interval of z; the additional epsilon cutoff only shortens it. The zero-extended branch function is therefore a monotone function on an interval with two endpoint jumps, and its total variation is at most twice its supremum. Each nonzero branch is at most D_0/(epsilon w). There are at most two branches. Therefore

    Var_z G_i(z,t) <= 4D_0/(epsilon w),                (3.3)

uniformly in t and i. This argument is valid for the coarea density almost everywhere in t; choosing Borel versions gives the same essential-supremum bound. The cutoff excludes the only horizontal critical point.

Apply (2.1) to replace zeta_{B,v} by U. After averaging over i with weights 1/A, the change in the t-density is at most

    4D_0/(epsilon B w).                               (3.4)

No bound depends on the vertical microinterval length v other than v<=1/B.

**Then average in the horizontal coordinate.** With the vertical coordinate now uniform, for each fixed u the distance image has the density

    H(u,t) = 1_{allowed positive vertical root}
             1_{|X-p_1|>=epsilon}
             [ r/(Y-p_2) ].                          (3.5)

There is only one possible vertical root because Y-p_2>=v_0>0. Its value is r/sqrt(r^2-(X-p_1)^2), bounded by D_0/v_0. On either side of X=p_1 it is monotone as a function of |X-p_1|. Requiring the root to lie in [q_2,q_2+h] gives at most one interval on each side; intersecting with the hard cutoff preserves this. The zero-extended density consequently has

    Var_u H(u,t) <= 4D_0/v_0.                         (3.6)

Applying (2.1) to xi_{A,w} gives a further error at most 4D_0/(v_0 A). Summing (3.4) and this error, then converting the t-density to the physical distance density, proves (3.1). All comparisons used the same pin and the same hard mask. QED.

**What supplies resolution.** It is the deterministic inequality B w >> 1: the vertical sampling spacing is much finer than the horizontal interval width, in a coordinate where distance is noncritical after the fixed cut. A cell-count/Frostman profile by itself does not supply this property.

### Lemma 3.2 (harmonic improvement at one coarse-bin width)

Under Lemma 3.1, set epsilon=h/A. Then the same difference of masked distance densities satisfies

    ||difference||_infinity
      <= C D_0 [1/(h v_0 A) + log(2A)/(h^2 B w)].     (3.7)

The improvement over (3.1) comes from summing the actual inverse horizontal separations, rather than applying their worst value to every strip.

**Proof.** For horizontal strip I_i=[q_1+hi/A,q_1+hi/A+hw], let d_i be the infimum of |X-p_1| on its retained part |X-p_1|>=h/A. Empty retained strips contribute zero. The proof of (3.3) gives the sharper bound 4D_0/(w d_i). Each I_i lies inside its own coarse interval of length h/A, and d_i>=h/A. There are only O(1) coarse intervals at each successive bin-distance from p_1. Therefore, uniformly in the location of p_1,

    (1/A) sum_{nonempty i} d_i^{-1}
       <= C h^{-1} [1+sum_{l=1}^A l^{-1}]
       <= C h^{-1} log(2A).                          (3.8)

One direct verification labels intervals by their order to the left and right of the coarse interval containing p_1; apart from at most four neighbors, the l-th interval has separation at least l h/(2A). If p_1 lies outside Q, the same ordering only increases separations, except for the nearest bounded number, which are covered by the cutoff.

The first quadrature error before returning to physical distance is now at most

    C D_0 log(2A)/(h B w).

Multiply by h^{-1}. The second quadrature error from (3.6) is unchanged. This proves (3.7). QED.

## 4. The exact nested transition

Inside any occupied depth-n_{j-1} square, mu_{j-1} is uniform. The conditional law of mu_j is exactly the pattern in Lemma 3.1 with

    h = 2^{-n_{j-1}},
    A_j = 2^{a L_j},       w_j = 2^{-L_j/2},
    B_j = 2^{b L_j},       v_j = 2^{-L_j}.

The initial horizontal free digits choose the A_j strip positions, the middle frozen digits leave gaps, and the final free horizontal digits together with the filled tail give each entire interval of width w_j. The vertical free digits choose B_j positions; its frozen suffix and filled tail give microintervals of width v_j. In particular,

    B_j w_j = A_j.                                    (4.1)

All source squares have the same geometry and the same h at this stage. Multiply (3.1) by the original parent masses and sum. Those masses sum to one, so there is no cell-count loss. If g_{j,p,epsilon} is the density of (D_p)_*(M_epsilon mu_j), then

    ||g_{j,p,epsilon}-g_{j-1,p,epsilon}||_infinity
      <= 4D_0 (v_0^{-1}+epsilon^{-1})
                         2^{n_{j-1}-aL_j}.           (4.2)

This holds uniformly for every p in P. At the initial endpoint j_0, vertical coarea on each filled square gives

    ||g_{j_0,p,epsilon}||_infinity
      <= (D_0/v_0) 2^{n_{j_0}}.                     (4.3)

For 0<epsilon<=1, (1.2), (4.2), and (4.3) show that these densities are Cauchy in L-infinity, uniformly in p, and that their limits satisfy

    ||g_{p,epsilon}||_infinity <= C_*/epsilon,         (4.4)

where one valid constant is

    C_* = (D_0/v_0)2^{n_{j_0}}
                 +4D_0(1+v_0^{-1}) S.               (4.5)

No claim is made that C_* is universal across arbitrary choices of the early stages. It is finite for each one fixed nested construction.

### Identification of the limit, including hard-cut boundaries

For each fixed p, the discontinuity set of M_epsilon(p,.) lies on the two vertical lines y_1=p_1 +/- epsilon. Their mu-mass is zero by (1.5). Therefore weak convergence mu_j -> mu, applied to any bounded continuous distance test function times this mask, yields

    (D_p)_*(M_epsilon mu_j) -> (D_p)_*(M_epsilon mu)

weakly. All distance laws lie in the same bounded interval [v_0,D_0]. The L-infinity convergence already proved implies L^1 convergence on that interval, so its density limit is exactly the latter pushforward. This establishes (4.4) for the **actual** infinite source law. It is not merely a family of unrelated finite-scale estimates.

There is no common-pin exceptional set in this argument: every fixed p in P has the same boundary-null property and the same bounds. The coarea formulas for the finite approximants are jointly Borel. Their limit in the separable L^1 space can be chosen jointly measurable, which also makes all pin averages below legitimate.

## 5. Main theorem: fixed positive good laws and raw weak-L^alpha regularity

### Theorem 5.1

Under Section 1, for every p in P and 0<epsilon<=1, the positive submeasure

    nu_{p,epsilon} = (D_p)_*(M_epsilon(p,.) mu)

has a density g_{p,epsilon} with

    mass nu_{p,epsilon} >= 1-K_X epsilon^beta,
    ||g_{p,epsilon}||_infinity <= C_*/epsilon.          (5.1)

The constants do not depend on p or a finest observation scale. For any prescribed retained fraction 1-delta, choose one fixed epsilon with K_X epsilon^beta<=delta. This single mask then works at every later scale.

The unfiltered distance probability nu_p=(D_p)_*mu is absolutely continuous for every p in P. If g_p is its density, then

    Leb{t : g_p(t)>T} <= C T^{-alpha}     (T>0),       (5.2)

uniformly in p. Consequently, for every 1<=q<alpha,

    sup_{p in P} ||g_p||_{L^q} < infinity.            (5.3)

#### Proof of the raw-law statements

Let epsilon_l decrease to zero. The masks increase to one off the line y_1=p_1, and that line has mu-mass zero by (1.5). Each nu_{p,epsilon_l} is absolutely continuous. A Lebesgue-null set has zero measure under every member of the increasing sequence, hence under its limit nu_p. This proves absolute continuity without a uniform L^2 estimate as epsilon tends to zero.

Write g_p=g_{p,epsilon}+b_{p,epsilon}, with b nonnegative. Its integral is at most K_X epsilon^beta. For sufficiently large T, take epsilon=2C_*/T<=1. Then g_{p,epsilon}<=T/2 and Markov's inequality gives

    Leb{g_p>T}
      <= (2/T) int b_{p,epsilon}
      <= 2 K_X (2C_*)^beta T^{-(1+beta)}.

Since 1+beta=alpha, this is (5.2) for large T. For smaller T enlarge the constant using the common bounded output interval. Integrating the distribution function proves (5.3); one can for example split the layer-cake integral at T=1. QED.

## 6. Compatibility with the all-pin non-L2 obstruction

For p in the original pin support, the old stage-j horizontal track around p_1 has source mass

    m_j = 2^{k-b n-a L},

where n=n_{j-1} and L=L_j. Its distance image lies in at most

    M_j = 2^{b n+b L-k}

intervals of length C 2^{-(n+L)}, since its horizontal width is 2^{-n-L/2} and vertical separation is fixed. This is exactly the old geometric track argument. Thus its distance image is contained in a Borel set U_j of Lebesgue measure at most

    |U_j| <= C 2^{(b-1)(n+L)-k}.                      (6.1)

If the now established density g_p belonged to L^q, q>1, Holder's inequality would give

    ||g_p||_q^q >= m_j^q / |U_j|^{q-1}
      >= c_q 2^{[q(3/2-alpha)-(1-alpha/2)]L
                    +[q(1-alpha)-(1-alpha/2)]n}.     (6.2)

The coefficient of L is positive exactly when

    q > q_* = (2-alpha)/(3-2alpha).                   (6.3)

By L_j/n_{j-1}->infinity, the lower bound then diverges uniformly over the original pins. Therefore no original pin's raw density is in L^q for q>q_*. Since q_*<2 when alpha<4/3, the old non-L^2 conclusion is recovered and strengthened to this range.

The next two subsections prove the matching upper range and then the endpoint q=q_* itself. Thus the exact attained integrability range is 1<=q<=q_*.

The conclusion is especially explicit at alpha=13/10:

    all raw pins: g_p in L^{7/4},
    all original pins: g_p not in L^q for q>7/4,
    every fixed diagonal-band deletion: bounded density.

### 6.1 Matching upper bound: the exact critical L^q index

**Theorem 6.1.** For every 1<=q<q_*,

    sup_{p in P} ||d[(D_p)_*mu]/dt||_q < infinity.       (6.4)

Consequently, for every pin in the original pin support,

    sup{q>=1 : d[(D_p)_*mu]/dt belongs to L^q}=q_*.    (6.5)

This is a statement about the original, unmasked probability. Section 6.2 strengthens it to the endpoint.

**Proof.** It suffices to treat 1<q<q_*, since q=1 is the probability normalization. Put sigma=1-1/q and choose

    theta = (1 + (1-b)sigma/a)/2,
    c_q   = [a-(1-b)sigma]/2 > 0.                    (6.6)

The inequality c_q>0 is exactly q<q_*; thus 0<theta<1.

We compare the unmasked stage-j replacement and the filled parent law inside one square Q of side h=2^{-n}, where n=n_{j-1}. Write A=2^{aL}, B=2^{bL}, w=2^{-L/2}, v=2^{-L}, with L=L_j. In this comparison only, use the auxiliary physical band width

    epsilon_j = h d,    d=A^{-theta}.                 (6.7)

This is a proof decomposition of a signed difference, not the fixed positive good-law mask in Theorem 5.1 and not a claimed uniform L^2-restoration sequence.

**Away from the band.** Lemma 3.1 and Bw=A give an L-infinity error at most

    C h^{-1}[A^{-1}+(h d A)^{-1}]
      <= C h^{-2} A^{-(1-theta)}.

Both distance laws from Q are supported in an interval of length at most sqrt(2)h, by the Lipschitz property of distance. The L^q error of the two away-band laws is therefore at most

    C_q h^{-(2-1/q)} A^{-(1-theta)}.                 (6.8)

**Inside the band.** The horizontal coordinate law of the replacement puts mass 1/A in each bin of length 1/A. An interval of relative length 2d consequently has mass at most 2d+2/A<=4d, since d>=1/A. The filled parent gives at most 2d.

The replacement's vertical relative-coordinate density is bounded by (Bv)^{-1}. For each fixed horizontal coordinate, physical vertical coarea has derivative at least v_0/D_0. Hence the distance density of the band-restricted replacement is bounded by

    C h^{-1} d (Bv)^{-1},

and its L^1 norm is at most 4d. Interpolation between this L^1 bound and the displayed L-infinity bound gives

    ||band density||_q <= C_q h^{-sigma} d (Bv)^{-sigma}. (6.9)

The filled parent has the same estimate with Bv replaced by one. Since Bv<=1, (6.9), with an adjusted constant, bounds their difference as well. This use of a density bound is legitimate at every finite stage: both filled-tail laws have a bounded vertical density, even though the limiting vertical marginal is singular.

Combining (6.8)-(6.9), and using Bv=2^{-(1-b)L}, the conditional unmasked density increment is bounded in L^q by

    C_q [ h^{-(2-1/q)} 2^{-a(1-theta)L}
               + h^{-sigma} 2^{-[a theta-(1-b)sigma]L} ]
      <= C_q 2^{(2-1/q)n-c_q L}.                     (6.10)

The two exponents in L agree and equal c_q by (6.6).

Now weight these conditional differences by their exact parent masses and use the triangle inequality in L^q. The masses sum to one and the geometry is uniform, so (6.10) also bounds the full stage-j density difference, with no number-of-cells factor. By L_j/n_{j-1}->infinity,

    sum_j 2^{(2-1/q)n_{j-1}-c_q L_j} < infinity.       (6.11)

For example, eventually c_q L_j >= (3-1/q)n_{j-1}, leaving a summable 2^{-n_{j-1}} bound. The finite initial filled-tail law has a uniformly bounded density by vertical coarea. Thus the **unmasked** stage densities form a Cauchy sequence in L^q, uniformly for p in P.

Weak convergence mu_j->mu and continuity of D_p identify the limit with the actual unmasked distance probability, without a cut-boundary issue. Since all output measures lie in a fixed bounded interval, L^q convergence also implies L^1 convergence. This proves (6.4). Combining it with (6.2)-(6.3) proves (6.5). QED.

**Scope of the strengthening.** The new critical index uses the specific stage relation Bv=2^{-(1-b)L}, in addition to Bw=A and superlacunarity. The more general weighted template criterion (8.2) below still supplies the fixed-mask and absolute-continuity conclusions, but is not asserted by itself to imply this exact L^q index.

### 6.2 The critical endpoint is attained

**Theorem 6.2.** For the same construction,

    sup_{p in P} ||d[(D_p)_*mu]/dt||_{q_*} < infinity. (6.12)

For every pin in the original pin support the density therefore belongs to L^q exactly for 1<=q<=q_*. The nonmembership assertion is for finite q>q_* and consequently excludes L-infinity as well.

**Proof.** Continue to write n=n_{j-1}, L=L_j, h=2^{-n}, A=2^{aL}, B=2^{bL}, w=2^{-L/2}, and v=2^{-L}. Use the auxiliary band width

    epsilon_j=h/A.                                   (6.13)

Let sigma_*=1-1/q_*. The exact identity is

    (1-b)sigma_*=a,    b-a=1/2.                     (6.14)

**Away-band increments.** Apply Lemma 3.2 inside each parent square. Since Bw=A, its conditional L-infinity error is at most

    C h^{-2} A^{-1} log(2A).

Weight by the parent masses and sum, retaining the same physical pin and the same band (6.13). Their masses sum to one. All global outputs lie in the common bounded interval [v_0,D_0], so the full away-band L^{q_*} increment is at most

    C (1+L) 2^{2n-aL}.                              (6.15)

This is summable in j: eventually log_2(1+L)<=aL/2 and aL/2>=3n, leaving a bound C2^{-n}.

**Inside-band increments.** Here the actual global product structure of this source is used. At a stage endpoint n, every occupied horizontal prefix interval has kappa-mass 2^{k-bn}. Each is divided into A coarse horizontal bins at the next replacement, with mass 2^{k-bn}/A in each occupied strip. The interval |X-p_1|<h/A meets only a bounded number of these globally aligned coarse bins. Thus the horizontal band masses for both filled-tail laws obey

    M_j <= C_k A^{-1}2^{-bn},
    M_{j-1} <= C_k A^{-1}2^{-bn}.                   (6.16)

For mu_{j-1}, the second inequality follows equally from its piecewise constant horizontal density and the band length 2h/A.

The vertical marginal of mu_j has density bounded by

    H_j = 2^{k+(1-b)(n+L)},                          (6.17)

because every occupied depth-(n+L) interval has mass 2^{k-b(n+L)}. Similarly H_{j-1}=2^{k+(1-b)n}. Horizontal band restriction does not alter these vertical marginals: mu_j and mu_{j-1} are product laws, and the mask depends only on p_1 and the horizontal source coordinate.

For any product law restricted to a horizontal mass M and having vertical density at most H, vertical coarea gives a distance density of supremum at most (D_0/v_0)MH. Its mass is M, so its L^{q_*} norm is at most

    C M H^{sigma_*}.                               (6.18)

Using (6.14)-(6.17), the stage-j bound becomes

    C A^{-1}2^{-bn} 2^{(1-b)sigma_*(n+L)}
      = C 2^{-aL-bn+a(n+L)}
      = C 2^{-n/2}.                                (6.19)

For the previous filled-tail law there is the extra favorable factor A^{-1}; in particular the same C2^{-n/2} upper bound holds. The two band densities' difference is bounded by their sum, so its L^{q_*} norm is summable over j.

Combining (6.15) and (6.19) proves

    sup_{p in P} ||g_{j,p}-g_{j-1,p}||_{q_*}
      <= C[(1+L_j)2^{2n_{j-1}-aL_j}+2^{-n_{j-1}/2}], (6.20)

where g_{j,p} is the unmasked distance density of mu_j. Both terms are summable. The finite initial density is bounded, and weak convergence identifies the L^{q_*} limit with the actual raw distance law exactly as in Section 6.1. This proves (6.12). Combine with the lower bound (6.2) to obtain the precise integrability range. QED.

**No contradiction with the old restoration obstruction.** When 1<alpha<4/3, q_*<2. The original laws have a uniform L^{q_*} bound, and still have infinite L^2 norm at every original pin. The changing bands in this proof are used solely to bound increments in L^{q_*}; they are not assigned a uniform L^2 gate.

**Parameter extension.** The proofs of the exact L^q index use only 1<alpha<3/2 and L_j/n_{j-1}->infinity. Thus the same digit construction, with the first growth requirement eL_j-alpha n_{j-1}->infinity dropped, has the same attained critical index q_* throughout 1<alpha<3/2. For instance alpha=7/5 gives q_*=3. The restriction alpha<4/3 in the main statement is to address the earlier all-pin non-L^2 example without changing that example. The endpoint alpha=4/3 gives q_*=2 and the positive proof applies; the earlier strict non-L^2 lower bound no longer does.

## 7. Arbitrary inherited masks, normalization, and perturbations

Fix epsilon once. Let 0<=F(p,y)<=M_epsilon(p,y) be any jointly Borel mask, and put

    sigma_p = (D_p)_*(F(p,.) mu),    m(p)=int F(p,y)dmu(y).

Positive domination, applied to the actual measures, gives

    0 <= d sigma_p/dt <= g_{p,epsilon}(t) <= C_*/epsilon. (7.1)

In particular,

    ||d sigma_p/dt||_2^2 <= (C_*/epsilon) m(p).        (7.2)

If the fiber is normalized and m(p)>0, then

    ||d(sigma_p/m(p))/dt||_infinity
           <= C_*/[epsilon m(p)],
    ||d(sigma_p/m(p))/dt||_2^2
           <= C_*/[epsilon m(p)].                   (7.3)

The usual m(p)^{-2} normalization rule is not omitted: it is applied to (7.2), and the factor m(p) already present there leaves the sharper m(p)^{-1} bound. In particular a uniform mass bound m(p)>=c costs at most c^{-1} in (7.3). There is no bound independent of retained mass when m(p) is allowed to vanish.

For every pin probability supported on P, integrate (7.2) or (7.3) against that very same pin law. No independent copy of the pin enters either distance factor.

### Preserving a previously given decreasing family

If 0<=Gamma_N<=1 decreases and int Gamma_infinity d(lambda x mu)>=c_*>0, choose epsilon with K_X epsilon^beta<c_*/2. Then

    F_N=M_epsilon Gamma_N

is one decreasing family, loses at most K_X epsilon^beta additional pair mass, and has limiting pair mass at least c_*/2. Every fiber is controlled by (7.1), and the limiting family supplies actual nonzero absolutely continuous distance laws on a positive pin set. All earlier tests encoded in Gamma_N remain imposed.

Multiplying by this band mask need not preserve a previously established lower fraction in every individual spatial cell. If such local fractions are separately required, they must be re-pruned with their actual budget. The energy estimate survives any additional positive pruning that leaves the requisite total/fiber mass; it does not manufacture that mass.

### Observation-scale endpoint errors

Let a retained endpoint be moved by at most A delta, possibly depending on both p and y and through a probability kernel. Pull the retained coupling back to an original marginal F(p,y)mu with F<=M_epsilon and mass m(p). A perturbed distance collision of width delta implies an original collision of width (1+2A)delta. By (7.1), for an unnormalized fiber,

    collision <= 2(1+2A)delta (C_*/epsilon) m(p).      (7.4)

After normalization this becomes at most

    2(1+2A)delta C_*/[epsilon m(p)].                  (7.5)

A shared pin error of magnitude A_p delta changes 1+2A to 1+2A+2A_p. These are positive collision/whole-low-pass bounds. They are **not** a claim of decaying high-frequency shells for arbitrary varying masks or jitters; the previous phase-sector and jitter obstructions to such a claim remain valid.

For clarity, the standard whole-low-pass comparison is

    int_{-R}^R |tauhat(r)|^2 dr <= C R collision_{1/R}(tau)

for positive measures. It follows from Gaussian Fourier domination, a partition into intervals of length 1/R, and Cauchy-Schwarz for the resulting summable off-diagonal bin weights. Applying it to (7.4)-(7.5) gives the corresponding uniform low-pass gates.

## 8. The precise new structural input and its limit

The sufficient multiscale condition in this proof is not the Frostman/profile condition. It is the **actual stagewise rectangular placement**, with a whole horizontal interval of width w_j at each horizontal position, a vertical sampling rate B_j resolving it, and the summable replacement error

    sum_j 2^{n_{j-1}} [A_j^{-1}+(B_j w_j)^{-1}] < infinity. (8.1)

The temporary filled tails are a proof device; the limiting source is still the original purely singular product-digit measure. The same physical pin and the same fixed positive band mask are used before every replacement and through the limit.

### A genuinely multiscale sufficient condition

The same proof is not confined to one product-digit example. Suppose a sequence of probabilities rho_j is given by finite unions of filled dyadic squares, converges weakly to rho, and all its source squares lie in the fixed vertically separated source rectangle. At step j, each parent Q of side h_Q and mass m_Q is replaced, without changing its mass, by the affine product template of Lemma 3.1, with parameters A_Q,B_Q,w_Q,v_Q. Assume the new filled leaves refine the old ones, their maximum diameter tends to zero, and

    E = sum_j sum_{Q at step j} (m_Q/h_Q)
                     [A_Q^{-1}+(B_Q w_Q)^{-1}] < infinity. (8.2)

Parameters and parent masses may depend on Q; a globally product source is not required. Suppose the first-coordinate marginal of rho has no atoms. Then for every epsilon>0 the same fixed horizontal-band mask has an L-infinity distance-density bound C(1+epsilon^{-1}) at every pin in the fixed pin rectangle, and the original distance law is absolutely continuous at every such pin. If the limiting horizontal marginal obeys a beta-Frostman interval bound, the raw densities are uniformly weak-L^{1+beta}.

**Proof.** Sum (3.1) with weights m_Q at each step. The density increments sum absolutely in L-infinity by (8.2). The finite initial filled-square law has a bounded distance density by vertical coarea. Nonatomicity makes both hard-cut boundary lines rho-null, so exactly the weak-limit identification in Section 4 applies. Increasing the cut laws as epsilon decreases proves raw absolute continuity; the same Markov argument gives the weak-L^{1+beta} bound. This proves the stated sufficient condition with no missing upper-level input.

This criterion records spatial resolution and the actual weighted accumulated error. Numerical child counts alone do not establish it. It permits adaptive, nonuniform, parent-dependent templates with a common coordinate orientation, but does not assert a theorem for arbitrarily rotated templates.

The old no-TV-restoration theorem is not evaded. Fixing epsilon gives a good law with a fixed, arbitrarily small but generally nonzero deletion. Letting epsilon_N->0 restores the original law, while the available bound C_*/epsilon_N diverges; the original all-pin non-L^2 theorem forbids retaining a uniform full L^2 bound in such a restoration.

Arbitrary descendants, rotations changing with scale, or uncontrolled source masks inserted **before** the replacement comparison are not covered. The later domination result covers arbitrary masks of the actual fixed good law, which is a different statement. No existing family-073 regularization is claimed to manufacture (8.1) or the required rectangular placement in general.

This thus closes a real positive-mask gap for the exact previously constructed nested counterexample, but does not close the unrestricted common-pin recursion.

## 9. Source and novelty ledger

1. Local prior input: the exact digit construction and old lower-bound geometry are in `common_pin_traintrack_received/source/nested-train-track-obstruction.md`. Sections 2-5 above prove the positive theorem independently of that note's external radial-projection preparation theorem.
2. [Guth-Iosevich-Ou-Wang, arXiv:1808.09346v1](https://arxiv.org/html/1808.09346v1), Sections 1.2 and 6, already explain the finite-scale distinction between a pin's own track and tracks far from it. Their good-source method in the general theorem is a wave-packet construction, rather than the fixed positive diagonal-band filter proved here for this explicit model. The new claim is not that this finite-scale intuition originated here.
3. [Peres-Schlag, Duke Math. J. 102 (2000), 193-251](https://doi.org/10.1215/S0012-7094-00-10222-0) provides the classical generalized-projection transversality framework. The tempting enclosing-circle s+t>2 route is therefore not advanced as a new main result. No theorem from that paper is used in the train-track proof above.
4. No random-martingale theorem, unproved family-073 common-pin estimate, or unverified current threshold is an input. Apart from elementary weak convergence, coarea in one strictly monotone variable, bounded variation, and Holder/Markov inequalities, the proof is self-contained.
5. A literature search did not establish novelty of the complete nested quantitative conclusion. It must not be advertised as a new general threshold or a settled publication claim before independent audit and broader literature review.
