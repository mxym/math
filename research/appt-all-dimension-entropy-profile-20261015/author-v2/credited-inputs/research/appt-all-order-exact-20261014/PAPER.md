# Exact eventual entropy and every minimizing spectrum at all APPT orders

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID0009-0000-3864-3536.14 October2026. No external funding.
OpenAI AI assistants assisted. All rights reserved for original material.
Natural logarithms. Ordinary written mathematics, same APPT programme.

## 1. Actual objects and the complete conclusion

Fix an integerm>=3, let every integern>=m grow, and set

    D=mn, R=m(m-1)/2, K=m(m+1)/2, H=R-1,
    q=(m+1)/(m-1)=K/R, t=q-1,
    kappa=1/ln(3/q),
    X(D)=kappa[lnD-lnlnD-ln(et kappa)].                 (A1)

All states are actual positive trace-one complex matrices onC^m tensorC^n,
APPT under EVERY global unitary conjugation. S_alpha is spectral Renyi
entropy, with the vonNeumann value at1, S_0=ln rank and
S_infinity=-lnlambda_max. Put E_D(alpha)=lnD-min_(actualAPPT)S_alpha.
For alpha>1 let M_alpha(rho)=D^(alpha-1)Tr rho^alpha.

The following credited actual APPT families are written as matrix states:

    hole: (I-P)/(D-1), rankP=1;
    bulk: (I+tP)/(D+tk), rankP=k, 1<=k<=D-1;
    pole: (I+2P)/(D+2), rankP=1.                        (A2)

Their deficits are respectively

    H_D=ln[D/(D-1)],
    g_q(alpha,k/D)=
      {ln[1+(k/D)(q^alpha-1)]-alpha ln[1+t k/D]}/(alpha-1),
    p_D(alpha)=
      {ln[(3^alpha+D-1)/D]+alpha ln[D/(D+2)]}/(alpha-1).
                                                              (A3)

Use the continuous values at1 and0; both full-rank families have deficit0
at0. At infinity g_q=ln[qD/(D+tk)] andp_D=ln[3D/(D+2)]. Define
G_D(alpha)=max_(1<=k<=D-1)g_q(alpha,k/D), with all maximizing ranks
retained. For every finite alpha>0 they are the exactly winning neighbors
ofD theta_alpha, clipped to[1,D-1], where

    theta_alpha=(q^alpha-1-alpha t)/[t(alpha-1)(q^alpha-1)], alpha!=1,
    theta_1=(q lnq-t)/t^2.                              (A4)

Always compare the exact two values, preserving any tie. At infinity
G_D=ln[qD/(D+t)] and its maximizing rank is1.

**Theorem A.** For each fixedm>=3 there is ONE D0(m) such that every
actualn>=m withD>=D0 and EVERY extended real0<=alpha<=infinity satisfy

    E_D(alpha)=max{H_D,G_D(alpha),p_D(alpha)}.           (A5)

Every entropy minimizer, and only a minimizer, belongs to the winning
families inA2. In the bulk family retain every rank attainingG_D. This is
a classification of matrices, including all their global unitary orbits.
At a positive-order tie there are no additional nontrivial mixtures.

**Theorem T.** At those dimensions there are exactly TWO transitions
tau_D in(0,1) andeta_D>2. The hole is the unique decreasing minimizing
spectrum for0<=alpha<tau_D. Only the selected bulk spectra minimize for
tau_D<alpha<eta_D, and only the pole minimizes foreta_D<alpha<=infinity. At each
transition exactly both neighboring families occur, preserving bulk rank
ties. The low transition is the exact solutionG_D(tau_D)=H_D. The high
transition is the UNIQUE solution inalpha>1 of

    P_D(alpha)=Q_D(alpha),
    P_D(alpha)=(D/(D+2))^alpha(3^alpha+D-1)/D,
    Q_D(alpha)=max_(1<=k<=D-1)
          [1+(k/D)(q^alpha-1)]/[1+t k/D]^alpha,         (A6)

andeta_D=X(D)+o_m(1). The integer maximization is kept in this exact
definition. The old small-order paper supplies, withL=lnq,

    C0=ln(t/L)-1+L/t,
    theta0=(t-L)/(tL), C1=C0-theta0(1-theta0)L^2/2,
    tau_D=1/(C0 D)+[1/(2C0)-C1/C0^3]/D^2+O_m(D^-3).    (A7)

The credited hole, pole, projection spectra and scalar optimization are
known inputs. The new step is complete eventual ACTUAL-SET equality at
all orders with a unique high-order transition, extending the earlier
exact low-order band and high-order pole theorem. Fixedm and sufficiently
largeD are essential. We do not assert all finite dimensions, growingm,
the smallest or an effective threshold, or the ASEP bulk minimum.
This is neither full Lean formalization nor a new independent major count.

## 2. Physical inputs with their actual-set meanings

For an actual decreasing APPT spectrumlambda, the m-Schmidt maximally
entangled witness placed by a global unitary gives

    sum_(i=1..R)lambda_i <= sum_(i=D-K+1..D)lambda_i.   (A8)

Set b=lambda_(D-K+1). The physical rank-two test giveslambda1<=3b,
so b>0. Thusz_i=lambda_i/b satisfy

    1<=z_i<=3 fori<=H,
    1<=z_i<=q forR<=i<=D-K,
    0<=z_i<=1 fori>D-K,
    Db<=D/(D-K+1).                                    (A9)

The actual three-Schmidt test in the unchanged critical-window paper
also proves

    (z1-1)^2+(z2-1)^2<=4.                             (A10)

It follows thatz1>=3-eta,0<eta<1, forces all remaining nonbottom ratios
to be at mostv=1+sqrt(4eta-eta^2). None ofA8-A10 is claimed sufficient
for APPT. Their underlying global-unitary witness proof is inherited
ordinary mathematics, not a newly executed Lean audit.

For y_i=Dlambda_i putu=3D/(D+2), delta=u-y1>=0,
mu=(D-y1)/(D-1), b0=D/(D+2). The inherited physical trace estimate says

    y_i>=mu-2delta fori>=2,
    delta=0 iff lambda is the pole.                    (A11)

Choose a fixed smallh>0 such that

    W=1+4sqrt(h)<q, Lh=3-2h, Lh/W>3/q.

For0<=delta<=h, sufficiently largeD, the same actual circle and variance
argument gives, at everyalpha>=2,

    sum_i y_i^alpha-[u^alpha+(D-1)b0^alpha]
      <=alpha delta W^(alpha-1)
          [1+(alpha-1)(D-1)-(Lh/W)^(alpha-1)].          (A12)

For EACH fixedS this is strictly negative wheneverdelta>0 and
alpha>=X(D)-S at all sufficiently largeD. Indeed, at the lowest order
T=alpha-1, (Lh/W)^T/[1+T(D-1)] tends to infinity since
kappa ln(Lh/W)>1; its logarithmic derivative is positive for all largerT
onceT>1/ln(Lh/W). This controls arbitrary tiny deviations from the pole.

We also use the unchanged low-order theorem: for each fixed
0<c0<1/ln(m-1), all0<=alpha<=c0 lnD have exactly the hole/bulk
minimum and all those equality families, with unique crossingtau_D andA7.
Finally, the unchanged critical-window theorem gives the unique actual
pole at ALLalpha>=X(D)+1, eventually. Those ranges will overlap the
new proof below; no monotonicity of unknown minimizers is assumed.

## 3. The complete geometry of a restricted head

Fix ANYp in(q,3). LetOmega_p be the ordered probability simplex cut byA8
andlambda1<=p lambda_(D-K+1). It is an outer spectral polytope.
Its pivot is positive: lambda1>=1/D andb>=lambda1/p.
The projective maplambda ->x=lambda/b identifiesOmega_p with

    p>=x1>=...>=x_(D-K)>=1,
    x_(D-K+1)=1>=...>=x_D>=0,
    h(x):=sum_(1..R)x_i-sum_(D-K+1..D)x_i<=0.          (A13)

The inverse islambda=x/Z, Z=sumx_i. Both maps take line segments onto
line segments with positive reparametrization, hence take vertices to
vertices. More explicitly, ifx=sum_v a_v v, sum a_v=1, then
lambda=sum_v {a_v(sumv)/Z} (v/sumv); all weights are positive whena_v>0.
Thus strict convexity ofsumlambda_i^alpha foralpha>1 applies in the
original trace-one polytope and excludes every nonvertex maximizer.

Before theh cut,A13 is a PRODUCT of two ordered simplices. Its vertices
are all

    v_(i,s)=(p repeatedi, 1 repeatedD-i-s, 0 repeateds),
    0<=i<=D-K, 0<=s<=K-1,
    h(v_(i,s))=(p-1)min(i,R)+s-m.                      (A14)

Every edge varies just one ofi,s. In each factor all pairs of distinct
vertices form edges; restricting to adjacent integer pairs would miss
vertices. A single halfspace cut has exactly surviving old vertices and
opposite-sign edge intersections. A boundary old vertex is retained;
an edge with both endpoints onh=0 adds no new vertex.

Since(p-1)R>m, every surviving old vertex hasi<R, and so has only a
bounded number of heads. A cut on a lower-simplex edge also hasi<R:
ifi>=R its fixed upper block already exceeds the largest possible
bottom sumK. Such a vertex has at mostR-1 heads, at mostK-1 fractional
or zero bottom entries, and all other entries equal1.

On an upper-simplex edge betweeni<j, withs fixed, a cut has

    x=(p repeatedi, r repeatedj-i, 1 repeatedD-j-s, 0 repeateds),
    1<r<p.                                            (A15)

Ifj<R it again has only bounded heads. Ifj>=R, the lower-sign endpoint
necessarily hasi<R and the exact equationh=0 is

    r=1+[m-s-(p-1)i]/(R-i).

Fori=s=0 this is EXACTLYr=q, withR<=j<=D-K: the bulk vertices.
Every other such vertex has

    r<=r_star:=max{1,q-min(1/R,(p-q)/(R-1))}<q.         (A16)

Only an attainable r>1 is used; the harmlessmax with1 covers degenerate
endpoints. These cases exhaust ALL product edges and hence every vertex.

## 4. Strict bulk dominance in the restricted polytope

Forr>1 andalpha>1 let

    F_r(alpha)=max_(0<=theta<=1)
                 [1+theta(r^alpha-1)]/[1+(r-1)theta]^alpha,
    F_1(alpha)=1.                                     (A17)

The chord inequality forx^alpha on[1,r] bounds any normalized two-level
middle moment byF_r. The unique maximizingtheta isA4 withq replacedr,
andF_r~r^alpha/[e(r-1)alpha] asalpha->infinity. At each fixedtheta
in(0,1), the logarithmic derivative with respect tor has sign
r^(alpha-1)-1>0, soF_r<F_q for1<=r<q. Consequently for each fixeda>1,

    sup_(alpha>=a)F_(r_star)(alpha)/F_q(alpha)<1.       (A18)

Continuity covers boundedalpha and the large-alpha ratio tends to0.
AlsoF_q(alpha)>=c_a q^alpha/alpha for allalpha>=a, withc_a>0.

Fixc>0 satisfyingc ln(p/q)<1. Uniformly fora<=alpha<=c lnD, the
exact integer bulk maximumQ_D fromA6 satisfies

    exp[-C_(m,a,c) alpha^2/D^2] <= Q_D/F_q <=1.         (A19)

To see this directly,theta_alpha is comparable to1/alpha at largealpha,
and is bounded away from1 on[a,infinity). Its two adjacent mesh points
lie in[R/D,(D-K)/D] at all sufficiently largeD. On their1/D neighborhood
the second derivative ofln[1+theta(q^alpha-1)]-alpha ln(1+t theta)
is bounded in absolute value byC alpha^2. Taylor at its stationary point
givesA19; it also proves the exact adjacent-rank rule by the sign of the
first derivative. This is uniform over the whole continuous order band.

For a bounded-head vertex of Section3, sumx>=D-C_m and
sumx^alpha<=D+C_m p^alpha, giving

    M_alpha(x/Z)<= [D/(D-C_m)]^alpha[1+C_m p^alpha/D].  (A20)

For an A15 vertex withr<=r_star, remove itsi heads ands zeros. The
remainingL=D-i-s entries lie in[1,r], with mean at least1, andZ is at
least their sum. Their chord bound therefore gives

    M_alpha(x/Z)<= (D/L)^(alpha-1)F_(r_star)(alpha)
                     +(D/L)^alpha i p^alpha/D.        (A21)

The discarded heads and zero ranks remain explicitly counted. On the
band, each normalization factor is1+O_m(alpha/D). Further,

    sup_(a<=alpha<=c lnD) p^alpha/[D F_q(alpha)]
       <=C_(m,a,c) lnD D^[c ln(p/q)-1] ->0.            (A22)

Thus A18-A22 make EVERY nonbulk vertex strictly smaller thanQ_D at
all sufficiently largeD. A20 uses the positive uniform gapF_q(a)>1.
All winning vertices are the exact selected q-bulk spectra; strict
convexity excludes nonvertices. This proves the conditional cap lemma
for everyfixeda>1,c ln(p/q)<1, without treatingOmega_p as APPT.

## 5. Exhaustion of all actual states through the high transition

Fixc>kappa, and choosep in(q,3) sufficiently close toq that
c ln(p/q)<1. EventuallyX(D)+1<c lnD. Choose a fixed small
0<eta<3-p such thatv=1+sqrt(4eta-eta^2)<q, and chooseh as inA12.
All constants now depend only onm and these fixed choices.

For everyalpha in[2,X(D)+1], a state withz1<=p is dominated exactly
byQ_D by Section4, with equality only for the selected bulk spectra.
Ifz1>p, A8 and order imply

    z_R<=r0:=(K-p)/(R-1)=q-(p-q)/(R-1)<q.              (A23)

Herer0>1 becausep<3 andm>=3. If alsoz1<=3-eta, the middle
L0=D-H-K ratios lie in[1,r0], theH heads are at most3-eta and
theK bottom ratios at most1. Retain normalization by their middle
sum and apply the chord bound to obtain

    M_alpha(rho)<=(D/L0)^(alpha-1)F_(r0)(alpha)
                    +(D/L0)^alpha[H(3-eta)^alpha+K]/D. (A24)

Uniformly for2<=alpha<=X(D)+1,

    (3-eta)^alpha/[D F_q(alpha)] ->0.                  (A25)

Indeed the global lower bound afterA18 reduces it to
C alpha[(3-eta)/q]^alpha/D. If that base exceeds1, its supremum is
at the upper endpoint and is a power oflnD times
D^[-kappa ln(3/(3-eta))]; otherwise it isO(lnD/D).
The strict gapF_(r0)/F_q andA19 showM_alpha<Q_D throughout this case.

Finally supposez1>=3-eta. A10 bounds EVERY tail ratio byv except
theK bottom entries. PutL1=D-K-1. Ifdelta>=h, retain the peak
boundy1<=u-h<3-h and the tail chord to get

    M_alpha(rho)<=(3-h)^alpha/D
                 +(D/L1)^(alpha-1)F_v(alpha)+(D/L1)^alpha K/D. (A26)

The argument ofA25 withh replacingeta, and the fixed strict gap
F_v/F_q, again givesM_alpha<Q_D uniformly on[2,X(D)+1].

If0<=delta<=h, letd_v>0 satisfyF_v/F_q<=1-d_v foralpha>=2.
For the lower orders useA26 with3 in place of3-h. The function
3^alpha/F_q(alpha) is strictly increasing: the logarithmic derivative
of any maximized two-level moment is at mostlnq, so that of this
ratio is at leastln(3/q)>0. The explicit scalar asymptotic therefore gives

    3^[X(D)-S]/[D F_q(X(D)-S)] ->exp(-S/kappa).        (A27)

Choose ONCE a finiteS>0 such that this limit is less thand_v/4.
ThenM_alpha<Q_D for ALL2<=alpha<=X(D)-S, eventually, withA19
and the normalization/bottom errors included. At EVERY remaining
alpha>=X(D)-S, A12 givesM_alpha<=P_D, strictly unlessdelta=0.
This includes the whole transition neighborhood, not just orders with a
fixed positive distance from a candidate crossing.

These cases exhaust every actual spectrum. They prove

    max_(actualAPPT)M_alpha=max{Q_D(alpha),P_D(alpha)},
                            2<=alpha<=X(D)+1,        (A28)

with exactly the winning bulk and pole equality spectra. Both candidates
are actual APPT. The unchanged low theorem supplies[0,2], at which
the actual pole is strictly losing since it is distinct from every listed
low-order equality spectrum. The unchanged high theorem supplies every
finitealpha>=X(D)+1; there the unique pole beats every actual candidate.
The known maximal-eigenvalue cap gives the same unique pole at infinity.
Taking the maximum of the finitely many dimension thresholds proves ONE
D0(m) valid on the full extended axis and proves TheoremA.

## 6. The unique exact high transition, without an optimizer assumption

For an integerk withtk<=2, the pole majorizes the q-bulk spectrum.
Atj=k the difference of the two largest-j partial sums has numerator
(D-k)(2-tk)>=0 over the positive common denominator(D+2)(D+tk).
Forj>=k the numerator is(D-j)(2-tk)>=0. Forj<=k the difference is
affine decreasing inj and is smallest atj=k. The spectra are distinct
whenm>=3, so strict convexity givesP_D>the rank-k moment atalpha>1.

Fortk>2 putA=3/(D+2), B=q/(D+tk), C=1/(D+2), F=1/(D+tk).
Their strict order isA>B>C>F>0. Define the analytic exponential sum

    f_k(alpha)=A^alpha-k B^alpha+(D-1)C^alpha-(D-k)F^alpha.
                                                              (A29)

It has zeros atalpha=0 and1 and is positive for all sufficiently large
alpha becauseA is the largest base. A nonzero sum of four distinct real
exponentials has at most THREE real zeros, counted with multiplicity:
divide by one exponential and differentiate, then induct using Rolle's
theorem; the derivative has three terms. Restricting to a finite interval
containing any proposed zeros proves the bound on the entire real line.

Consequently eitherf_k>0 at everyalpha>1, or there is a unique SIMPLE
rootr_k>1, withf_k<0 throughout(1,r_k) andf_k>0 throughout(r_k,infinity).
If a negative value exists, positivity at infinity gives one later root;
any earlier sign reversal or tangency, in addition to0 and1, would exceed
the three-zero bound. If no negative value exists, a zero above1 would
have even multiplicity and would also exceed that bound.

At least one rank has a negative value at2: the unchanged low-order
classification makes the pole strictly worse than the selected actual
bulk spectrum there. Leteta_D be the largest of the finitely manyr_k.
It is>2. For ALL1<alpha<eta_D its attaining rank beats the pole;
ateta_D at least one rank ties and none beats it; foralpha>eta_D
the pole beats every rank. This proves precisely the unique crossingA6.
Ranks tied at that crossing are exactly the ranks maximizingQ_D.

The low-order paper provesG_D strictly increasing on the positive axis,
by strict convexity of each normalized log-moment and its secant slope
through1, and supplies the unique crossingtau_D withH_D. Its expansion
puts it in(0,1) eventually. SinceG_D>H_D aftertau_D, the hole cannot
return at a larger order. TheoremA, the strict loss of the pole below2,
and the high crossing above2 give every phase and equality in TheoremT.

For each fixedepsilon>0 the unchanged critical theorem proves that an
actual bulk projection beats the pole atX(D)-epsilon, while the pole
is the unique actual winner at everyalpha>=X(D)+epsilon. The exact
single crossing just proved therefore lies between those two orders at
all sufficiently largeD. Sinceepsilon is arbitrary,eta_D=X(D)+o_m(1).
The previous eventual uniqueness-cutoff asymptotic is thereby connected
to a unique ACTUAL finite-order crossing; its old asymptotic is credited.

## 7. Scope and provenance

This settles eventual fixed-local APPT entropy optimization at every
nonnegative order, including exact integer ranks and all equality orbits.
It does not settle joint growing dimensions, every finite dimension,
effective smallest thresholds, ASEP bulk attainability, next asymptotic
orders of all transitions, or the general APPT=ASEP problem.
The prior low-order and critical-window manuscripts retain their literal
source and ordinary-review scopes. No prior Lean/kernel/48-page primary
audit is expanded. Finite diagnostic vertex or protocol computations are
controls, not an infinite proof certificate or external human peer review.
