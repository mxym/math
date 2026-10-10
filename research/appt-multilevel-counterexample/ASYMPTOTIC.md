# Further mathematical progress: the proportional-dimension obstruction

> Subsequent sharp result: [SHARP_ASYMPTOTIC.md](SHARP_ASYMPTOTIC.md) closes the remaining leading-constant gaps for every aspect ratio, and gives an equivalent uniform over all dimension pairs as total dimension grows. The proofs below remain valid; descriptions of then-open asymptotic gaps record intermediate progress. Exact finite maxima and absolute separability remain unresolved.


This continues the working proof in PROOF.md. No new manuscript or Release is prepared. The result here is a lower bound on the unrestricted maximum, and a matching upper bound only on a precisely specified three-level subclass.

## 1. A rational APPT construction in every fixed aspect ratio

Let m<=n tend to infinity with n/m -> gamma, where 1<=gamma<infinity. Put D=mn, h=ceil(sqrt(m)), and

    k=ceil((m-1)n/2),
    c=2/(m+h),
    q=2-(m-3)c=2(h+3)/(m+h),
    a=2-2(m-2)c^2/q = 2-4(m-2)/[(m+h)(h+3)].                    (A1)

These parameters are rational. Let P be any rank-k orthogonal projection and v a unit vector in its range. Normalize the positive operator

    B=I+cP+(a-c)|v><v|.                                        (A2)

The PSD criterion (9) in PROOF.md applies with b=1, d=a-c. Indeed q>0,

    (2-a)q=2(m-2)c^2,
    (a-c)q=[2-(m-1)c](2+c)>=0.                                 (A3)

Thus (A2) is APPT for every m>=4,n>=m. The selected rank satisfies

    binom(m,2)<=k<=D-binom(m+1,2).

For the lower inequality use n>=m. For the upper, subtract (m-1)n/2 from the integer D-m(m+1)/2; the difference is (m+1)(n-m)/2>=0, so its ceiling still lies below that integer. This puts the construction in the exact-membership rank regime, not just the sufficient regime.

The three unnormalized eigenvalues are 1+a (once), 1+c (k-1 times), and 1 (D-k times). Define

    T=a+(k-1)c,      S=a^2+(k-1)c^2.

For rho=B/(D+T), exact arithmetic gives

    Tr(rho^2)=(D+2T+S)/(D+T)^2,
    D^2[Tr(rho^2)-1/D]=(S-T^2/D)/(1+T/D)^2.                    (A4)

Now h/m->0, h->infinity, mc->2, a->2 and k/D->1/2. Consequently

    D c^2 ->4 gamma,
    S ->4+2 gamma,
    T^2/D ->gamma,
    T/D ->0.

Applying (A4) proves

    lim D^2[Tr(rho^2)-1/D] = 4+gamma.                           (A5)

No limit of a numerical optimizer is used. All inputs are explicit rational eigenvalues, and their APPT property holds at every finite parameter pair.

## 2. Why the conjecture fails in every such growth regime

For the rank-one-spike candidate P1 in Conjecture 6.7,

    D^2(P1-1/D)=4D(D-1)/(D+2)^2 ->4.

The other candidate P2 is the two-level projection spectrum with contrast c0=2/(m-1) and rank k from (A1). Its centered scaled purity is

    [k c0^2-(k c0)^2/D]/(1+k c0/D)^2 ->gamma.

The ceiling in k does not affect this limit. Therefore the conjectured value M(m,n) obeys

    D^2[M(m,n)-1/D] -> max(4,gamma).

Subtracting this from (A5) yields the STRICT limiting violation

    lim D^2[Tr(rho^2)-M(m,n)] = min(4,gamma)>0.                 (A6)

Thus the general conjecture fails eventually along EVERY sequence of integer local dimensions with m->infinity and n/m->gamma in [1,infinity). In particular it fails in square systems as well as rectangular ones. The explicit 10x38 witness in PROOF.md gives a concrete finite example; the asymptotic result is not needed to validate that example.

For unrestricted maximal purity Pmax(m,n), the proved consequence is only

    liminf D^2[Pmax(m,n)-1/D] >=4+gamma.                       (A7)

An equality in (A7) for unrestricted APPT spectra has NOT been established.

## 3. A sharp asymptotic result within the full one-spike/plateau class

Let C(m,n) consist of all APPT spectra with unnormalized entries

    1+a,  1+c [k-1 times],  1 [D-k times],

where a>=c>=0 and binom(m,2)<=k<=D-binom(m+1,2). Scale by their trace. In this rank regime the exact criterion (9) of PROOF.md is both necessary and sufficient.

It implies a<=2. Applying its PSD matrix to the all-ones vector also gives

    2m-m(m-1)c-2(a-c)>=0,

so c<=2/(m-1). Let y=k-1. Direct expansion gives

    S-T^2/D = (1-1/D)a^2 + y(1-y/D)c^2 -2ayc/D
             <= a^2 + D c^2/4
             <=4+D/(m-1)^2.

The denominator in (A4) is at least one. Hence EVERY spectrum in this subclass satisfies the finite bound

    D^2[Tr(rho^2)-1/D] <=4+D/(m-1)^2.                         (A8)

The explicit construction (A1) belongs to C(m,n) and attains the limiting value of (A8). We therefore obtain the complete subclass asymptotic

    lim D^2[max_{rho in C(m,n)} Tr(rho^2)-1/D] =4+gamma.       (A9)

This identifies the failure mechanism quantitatively: a concentrated spike contributes the constant 4, while a near-maximal low-contrast plateau contributes gamma. The original proposed maximum took the larger of these contributions; the three-level construction realizes their sum at leading centered-purity order.

## 4. The remaining central problem

The original formula is refuted, but the unrestricted sharp maximum is not determined. The immediate structural question is whether every APPT spectrum satisfies a matching upper bound with scaled leading constant 4+gamma in proportional growth, or whether additional levels yield an even larger constant. Equation (A8) proves such a bound only in C(m,n). It cannot be extended to arbitrary spectra by asserting that all maximizers have one spike or two plateau values.

This is a concrete revised target on the original problem, not an assumption used to prove the counterexamples. The scalar computations in (A4), (A8) are elementary identities; the all-unitary physical implication remains the analytic proof in PROOF.md. No new global-maximality, minimum-dimension, absolute-separability, or Lean claim is made.

## Subsequent progress: the unrestricted balanced constant is 8

The proposed comparison with 4+gamma cannot be promoted to a global bound. MESOSCOPIC.md gives coefficient 6 outside this note's rank regime; GRAPH_LIMIT.md analyzes a four-level sector; MULTISCALE.md matches the unrestricted balanced upper bound at 8 with many separated plateaus. The exact subclass statement (A9) is unchanged. The current remaining leading-constant question concerns gamma>1, not gamma=1. No new preprint or Release is created.
