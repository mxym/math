# Exact pin strata and the fixed-ratio boundedness boundary

Date: 8 October 2026. Status: fourth mathematical candidate; no independent audit has yet been run. The three earlier candidate files remain frozen.

## 1. Scope and notation

Use the explicit rational-alpha digit constructions in the companion notes. The source is mu=kappa x zeta_+ on the upper rectangle, pins range over P=[0,eta] x [0,eta], and

    H=supp kappa subset [0,eta],    B=H x [0,eta].

All statements concern the regularity of the **specific original cross-distance probability** nu_p=(D_p)_*mu. These are not exceptional sets for positive-measure distance images: the preceding fixed-positive-filter theorem already gives an interval in the actual distance set at every pin in P.

We consider:

* The superlacunary schedule L_j/n_{j-1}->infinity, for rational 1<alpha<2.
* The fixed-ratio schedule L_j=K n_{j-1}, with integer K and aK>2, where a=(alpha-1)/2, b=alpha/2 and c=1-b.

All digit positions are exact integers. No stagewise rounding is used.

## 2. Outside the closed horizontal projection

### Proposition 2.1

If p_1 is not in H, the original distance law has a bounded continuous density, and its density depends jointly continuously on p and r locally on P\B. Quantitatively,

    ||d nu_p/dr||_infinity <= C/dist(p_1,H)           (2.1)

after adjusting C on gaps of macroscopic size.

**Proof.** Since H is compact, d=dist(p_1,H)>0. Set epsilon=d/2. The fixed horizontal-band mask equals one on the entire source support at p. On a neighborhood where dist(p'_1,H)>epsilon, it is likewise identically one. The bounded jointly continuous positive-filter density from the companion theorem is therefore the original density on that neighborhood. Its bound C/epsilon proves (2.1). QED.

There is no intermediate membership stratum determined by a rate of approximation to H for a single fixed off-H pin: every such pin has a positive gap. The constants can diverge as pins approach H, which is a different, quantitative issue.

## 3. Every pin above H has the same track lower bound

The previous lower-bound proof did not use membership of p_2 in the vertical pin Cantor set. It used only the uniform vertical separation and the fact that p_1 belongs to H. Thus it holds for every p in B.

At stage j, set n=n_{j-1}, L=L_j. A coding interval of horizontal depth n+L/2 containing p_1 has width 2^{-n-L/2} and kappa-mass

    m_j=2^{k-bn-aL}.                                (3.1)

Its source distance image is contained in a set U_j with

    |U_j|<=C2^{(b-1)(n+L)-k}.                       (3.2)

These statements remain true at coding endpoints by choosing one supporting coding cylinder. Therefore the whole original horizontal projection, not just almost every point of it, satisfies the same localized Holder lower bounds.

## 4. Exact Lq-exceptional pin sets

Let Bad_q be the pins p in P for which nu_p does not have a density in L^q. Let Bad_C0 be the pins without a continuous density on R. Compact support makes every continuous density bounded.

### 4.1 Superlacunary schedule

If 1<alpha<3/2, put q_*=(2-alpha)/(3-2alpha). The proved upper theorem, Proposition 2.1, and (3.1)-(3.2) give exactly

    Bad_q = empty    for 1<=q<=q_*,
    Bad_q = B        for q_*<q<=infinity,
    Bad_C0 = B.                                       (4.1)

For 3/2<=alpha<2, all these exceptional sets are empty: the original density is bounded and jointly continuous over P x R.

### 4.2 Fixed-ratio schedule, D_K>0

Put

    D_K=K(3/2-alpha)+1-alpha,
    q_K=c(K+1)/D_K.

Under aK>2, the exact statement is

    Bad_q = empty    for 1<=q<q_K,
    Bad_q = B        for q_K<=q<=infinity,
    Bad_C0 = B.                                       (4.2)

The critical endpoint is included in Bad_q. At q=q_K, the track images U_j shrink in Lebesgue measure while the localized integral of g_p^{q_K} is bounded below by a fixed positive constant. This contradicts integrability at every p in B, not merely at pins from the original product pin measure.

### 4.3 Fixed-ratio schedule, D_K<=0

If D_K<0, all these exceptional sets are empty. If D_K=0, every finite Bad_q is empty. Section 6 below proves

    Bad_C0=B                                          (4.3)

at this boundary. The bounded-density exceptional set Bad_infinity is still only known to be a subset of B; its exact identity is not claimed.

## 5. Dimensions of the actual exceptional set B

These dimension statements are proved from the same digit construction, not inferred from the two-dimensional Frostman exponent.

### 5.1 Superlacunary case

The horizontal free count is at least (alpha-1) times depth, giving an (alpha-1)-Frostman horizontal law. At depths n_{j-1}+L_j/2 its ratio to depth tends to

    2a=alpha-1.

The occupied-interval covers along those depths give the matching Hausdorff upper bound. At depths n_{j-1}+aL_j the ratio tends to one. Every fixed cylinder has upper box dimension one, and the usual countable-cover/Baire argument gives packing dimension one. Hence

    dim_H H=alpha-1,    dim_P H=1,
    dim_H B=alpha,      dim_P B=2.                    (5.1)

For the product with a whole interval, the lower Hausdorff bound follows from the horizontal Frostman law times Lebesgue measure. The endpoint covers of H times an interval grid give the matching upper Hausdorff bound. The packing conclusion follows by the same upper-box counts and Baire argument on coding cylinders times nondegenerate intervals.

### 5.2 Fixed-ratio case

At a stage beginning at n, the horizontal free count is bn+f_X(l). Its ratio to n+l is increasing up to l=aKn, decreasing until l=Kn/2, and increasing afterwards. Its minimum and maximum asymptotic values are therefore

    s_K=(b+aK)/(1+K/2)
       =[alpha+(alpha-1)K]/(K+2),

    t_K=(b+aK)/(1+aK)
       =[alpha+(alpha-1)K]/[2+(alpha-1)K].            (5.2)

The finitely many initial depths change only Frostman constants. At all later depths the first ratio is at least s_K, so the horizontal law is s_K-Frostman. The middle-stage covers prove dim_H H<=s_K. All fixed cylinders have upper box dimension t_K, and Baire's argument supplies the matching packing lower bound. Thus

    dim_H H=s_K,    dim_P H=t_K,
    dim_H B=1+s_K,  dim_P B=1+t_K.                    (5.3)

The following identities are useful but are conclusions about this family only:

    D_K=(K+2)(1/2-s_K),
    q_K=(1-s_K)/(1-2s_K)       when D_K>0.           (5.4)

The superlacunary formula is the same expression in s=alpha-1. The endpoint behavior nonetheless differs between the schedules.

At the fixed-ratio boundary D_K=0,

    s_K=1/2,    t_K=(K+1)/(K+2),
    dim_H B=3/2,
    dim_P B=2-1/(K+2).                              (5.5)

For example K=9, alpha=29/20 gives an exact non-C0 pin set of Hausdorff dimension 3/2 and packing dimension 21/11, inside the separated pin rectangle. This remains an exception to continuity of the original law, while every pin's actual distance image contains an interval.

## 6. At D_K=0, no original-horizontal pin has a continuous density

Let r_0=1-eta, the minimum source vertical coordinate. For p in B, the minimum source distance is exactly

    r_min(p)=r_0-p_2>0,                              (6.1)

attained by the source point (p_1,r_0). Let delta_j=2^{-(n+L)}. Combine the horizontal track from (3.1) with the lowest occupied source vertical interval of length delta_j. That interval has zeta_+-mass 2^{k-b(n+L)}. The product source subset therefore has mass

    2^{2k-2bn-(a+b)L}.                              (6.2)

Its vertical distances lie between r_min(p) and r_min(p)+delta_j. Its horizontal quadratic error is at most C2^{-2n-L}<=C delta_j. Hence its actual distance image lies in

    [r_min(p),r_min(p)+C_0 delta_j].                  (6.3)

Dividing (6.2) by delta_j gives

    2^{2k}2^{(1-alpha)n+(3/2-alpha)L}
       =2^{2k}2^{D_K n}.                            (6.4)

When D_K=0, this is a fixed strictly positive constant. Consequently, uniformly for all p in B,

    nu_p([r_min(p),r_min(p)+C_0 delta_j])
         >=c delta_j.                              (6.5)

Suppose nu_p had a continuous density g on R. It vanishes on the open interval to the left of r_min(p), because there is no source distance there. Continuity forces g(r_min(p))=0. Its supremum on the shrinking interval (6.3) then tends to zero, contradicting (6.5). Thus no p in B admits a continuous density. Proposition 2.1 proves the converse off B, giving (4.3).

This argument does not contradict possible boundedness: a bounded density can have a jump at its support endpoint. L-infinity at D_K=0 remains open here.

## 7. An O(log q) upper bound for boundary Lq norms

The same D_K=0 laws have much stronger integrability than merely membership in every finite L^q. The result below is only an O(log q) upper bound for their L^q norms; no matching lower bound in q is proved.

### Theorem 7.1

Under the fixed-ratio hypotheses aK>2 and D_K=0, there is C<infinity such that

    sup_{p in P} ||g_p||_q <= C log(e+q),    1<=q<infinity. (7.1)

Consequently, there are constants c_1,c_2,T_0>0 with

    sup_p Leb{r:g_p(r)>T}
       <= exp[-c_1 exp(c_2 T)]     for T>=T_0.       (7.2)

In particular, for some c_3>0 and the fixed bounded output interval I,

    sup_p int_I exp(exp(c_3 g_p(r))) dr < infinity.    (7.3)

**Proof.** In the fixed-ratio stage proof, the away-band density increments have a summable L-infinity bound C(1+Kn)2^{-(aK-2)n}; this bounds their L^q norms uniformly for all q>=1 because their common output support is bounded.

For the inside-band law, the interpolation bound is C M H^{1-1/q}. Its constants can be chosen independently of q>=1: coarea contributes (D_0/v_0)^{1-1/q}, and the fixed prefix factors remain bounded by their q=infinity values. At D_K=0 the bound is

    C 2^{-c(K+1)n/q}.                               (7.4)

Thus the full moment bound is at most a fixed constant plus

    C sum_{j>=2} 2^{-c(K+1)n_1(K+1)^{j-2}/q}.       (7.5)

There are O(1+log q) terms before the exponent is of order one. The remaining terms are bounded by a convergent series of the form sum_l exp[-C(K+1)^l], uniformly in q. This proves (7.1).

For large T choose the real moment order q=exp[T/(4C)], increasing C if needed. Then C log(e+q)<=T/2. Markov's inequality gives

    Leb{g_p>T} <= (||g_p||_q/T)^q <=2^{-q},

which is (7.2). Integrating this distribution bound against the derivative of exp(exp(c_3 T)), for c_3 sufficiently smaller than c_2, proves (7.3). The integral is over the finite output interval; no nonzero constant is inadvertently integrated over all of R. QED.

The double-exponential upper tail does not imply essential boundedness, and is not used to claim it. The rigorous boundary description is: every finite moment with an O(log q) upper bound on its L^q norm, without a matching lower bound; no continuous-density version at any p in B; and an unresolved L-infinity question.

## 8. Literature and meaning of the pin stratification

[Guth-Iosevich-Ou-Wang, Section 1.2](https://arxiv.org/html/1808.09346v1) already distinguishes a pin's own train track from distant tracks. The present result is an exact all-pin classification for the original natural measure in these particular nested models, together with dimensions of the full exceptional curtain H x [0,eta]. It is not a new general bound for the exceptional set in a pinned-distance existence theorem.

All pins here have absolutely continuous original cross-distance laws and interval distance sets. The nonempty Bad_q and Bad_C0 sets concern stronger density regularity. Thus their Hausdorff/packing dimensions must not be described as dimensions of pins with zero-measure distance sets.

The earlier files and hashes are unchanged:

* Positive repair: aa85b4e46f8752754ce187d8413d200763d87639997f73b0782f874eefb79f81.
* Full phase and intervals: d91c8031c1ab5fecd2980d9048b3f630e2fc925882b9a052f3440a9649ccb0a7.
* Fixed-ratio endpoint switch: 4ab70460deb7c4cce215ab442b2590017001dfbb3ffc4952c5ab81787eef3505.
