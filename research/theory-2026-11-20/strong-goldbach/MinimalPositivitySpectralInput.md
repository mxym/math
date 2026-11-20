# A positivity-only spectral reduction for Li–Liu, and what the full hypothesis additionally asks for

**Scope.** This follows the primary [Li–Liu November paper](https://mrc.sdu.edu.cn/english/info/1018/1514.htm), but does not prove a new bound on the actual-prime spectral discrepancy. The point is to separate single-representation existence from a uniform density assertion, and to give a deterministic model threshold, optimized beyond the original symmetric centered probes. Prime powers can be removed exactly rather than estimated in the positivity test. The conditional full-operator consequences use Li–Liu's GRH(N); the arithmetic compression and all equivalences in §§1–3 do not.

## 1. Arbitrary positive probes and their energy

Fix a∈(0,1/2), I=(a,1−a), L=log N, R u=1−u. Use any real f,g∈C_c^∞(I), not necessarily symmetric. Put

    W_N(r)=exp(−2r/L)+exp(−r/4),
    V_f(u)=√u [f(u)/2−u f'(u)],
    (J_N f)(r)=V_f(e^r/N)/√(2π W_N(r)),
    Q_N(f)=∥J_N f∥²
           = ∫_I |f(u)/2−u f'(u)|²/[2π W_N(log(Nu))] du.

The formula uses Li–Liu's actual companion Φ(u)=√u f(u) and V=Φ−uΦ' (eqs. (2.5), (2.36)–(2.37)); it is not a new Hardy norm convention. For each fixed I this is an equivalent norm on H₀¹(I): integration by parts gives ∫|f/2−u f'|²=∫(u²|f'|²+3|f|²/4), and W_N is positive and bounded on the compact log support. Let

    C(f,g)=∫_I f(u)g(1−u)du,
    A_N(f,g)=N^(−1) Σ_{p+q=N; p,q prime} (log p)(log q) f(p/N)g(q/N),
    B_N^P(f,g)=S(N) C(f,g)−A_N(f,g).

The arithmetic form B_N^P corresponds to a compact self-adjoint operator on the Q_N space. The continuous form is compact by one-dimensional Rellich and the second is finite rank by point evaluations. Equivalently one may define it directly by the cumulative kernel in CentralMeanSquare.md on log(N)+log I; its compactness and identity do not need the full Hardy operator. All n,m in this interval are <N, so no positive difference family and no sum of size 2N or larger survive. The cross identity follows by multiplication and Fubini, or polarizing the original Mellin calculation. Restricting either to symmetric weights or to a single f is optional.

With GRH(N), the analogous operator with coprime Λ weights identifies with the compression of the original full T_N to the closed image of J_N. Relative to it, B_N^P adds exactly the finite operators from coprime proper-power pairs and subtracts the diagonal prime pair when N=2p; the latter case is already Goldbach. This sign follows from B=main−count. For fixed I the norm of the total change is O_a(N^(−1/2)(log N)^3), but there is no need to discard it as error in a microscopic test; one may use the prime-only definition above.

## 2. An exact positivity threshold and its stability

Define two quantities using Q_N-normalized probes:

    μ_N^0= max_{Q_N(f)=1} C(f,f),
    ν_N= sup_{Q_N(f)=1, f≥0} B_N^P(f,f).

Here μ_N^0 is the top eigenvalue of a **known continuous model**, not that of the arithmetic kernel. It is positive and simple and has a continuous strictly positive interior eigenfunction f₀, normalized with Q_N(f₀)=1. To see this, transfer the energy to g=f/√u. Then

    Q_N(f)=∫_I p_N(u)|g'(u)|²du,
    p_N(u)=u³/[2π W_N(log(Nu))],
    C(f,f)=∫_I √(u(1−u)) g(u)g(1−u)du.

The first identity makes replacing g by |g| cost-free, while the second can only improve the Rayleigh quotient. A nonnegative normalized maximizer exists by compactness, and its Euler equation has a nonnegative reflected RHS; the Dirichlet Green function of −(p_N g')' is strictly positive on I×I, so the maximizer is strictly positive in the interior. Any real eigenfunction at this top value has constant sign: its absolute value is also a nonnegative maximizer, hence has no interior zero. Thus a two-dimensional top eigenspace is impossible, since one could linearly combine two eigenfunctions to vanish at an interior point. A negative eigenvalue of equal magnitude would give equality after taking absolute values; the original eigenfunction would then need opposite signs at reflected points, so it would vanish at the reflection center, contradicting strict positivity of its absolute value.

For every individual even N for which the arithmetic model is defined, one has the exact criterion

    ν_N < S(N) μ_N^0   ⇔   N has a true prime pair with both p/N,q/N in I.       (P)

Indeed if there is no such pair the model is unchanged. Otherwise for each nonnegative probe A_N(f,f)≥0. If a sequence of probes comes arbitrarily close to the model top level, the simple eigenvalue and spectral gap force it to converge in Q_N to f₀ (the negative sign is ruled out by nonnegativity), so every existing pair contributes positively at the limit by continuity of evaluations. This gives strictness without a fixed fraction of the Hardy–Littlewood count. The restriction to nonnegative probes matters: for sign-changing f the prime cross term can have either sign. The ordinary positive spectral endpoint on the full compressed real Hilbert space is still a valid **sufficient** upper bound on ν_N, not in general a necessary one.

A quantitative version makes the microscopic requirement explicit. Put g_N=μ_N^0−max(spec(C)\{μ_N^0})>0, where C denotes the model operator in the Q_N norm, including the possible accumulation point zero. Let M_N be a bound for the embedding ∥f∥_∞≤M_N√Q_N(f). If x=p/N, Rx=q/N is one prime pair, write d_x=min(f₀(x),f₀(Rx)), w_x=(log p)(log q)/N. Then

    S(N)μ_N^0−ν_N ≥ d_x² min{S(N)g_N/(8M_N²), w_x/4}.                         (3)

To prove it, for a normalized f≥0 write b=⟨f,f₀⟩_{Q_N}=C(f,f₀)/μ_N^0≥0. Its model deficit is at least S g_N(1−b²)≥(Sg_N/2)∥f−f₀∥²_{Q_N}. If the distance is ≥d_x/(2M_N), this gives the first term in (3). Otherwise both values of f at the pair are ≥d_x/2, giving the second term. Counting one of the ordered atoms suffices, including p=q. For a fixed rational endpoint a and fixed I, all model constants in this estimate are uniformly bounded away from degeneracy for large N. For instance Q_N converges in equivalent form norm to a fixed limiting energy, so the first two generalized eigenvalues converge by min–max; the positive ground state converges in H¹ and, from the one-dimensional Euler equation with coefficients converging smoothly, in C¹. Its endpoint derivatives are nonzero by the Green formula (positive forcing). Thus d_x≳_a dist(x,∂I), and for a genuine interior lattice point this is at least c_a/N. The worst-case scale in (3) is consequently ≳_a (log N)²/N³, or ≳_a (log N)²/N for a pair in a fixed smaller interior window.

This is an effective calibration of what a one-representation certificate would need, **not** an independent proof of strictness. A non-strict upper bound follows from the sign of A_N for every N and is attained in the absence of a pair. A numerical margin finer than the discarded proper-power norm cannot, without exact correction, distinguish primes from proper prime powers. The arithmetic prime-only form avoids that issue.

## 3. Deterministic optimizers beyond the symmetric central window

On each fixed interval I, the limiting energy is

    Q_∞(f) = (e²/(2π)) E(f),       E(f)=∫_I (u²|f'|²+3|f|²/4)du.

Consider now the union of such compact probes over 0<u<1. Let H be its completion in E. Equivalently set u=e^(−x) and F(x)=e^(−x/2) f(e^(−x)); then E=∫₀^∞(|F'|²+|F|²)dx, with F(0)=0 and no artificial boundary condition at u=0. The involution f(u)↦f(1−u), paired by the ordinary integral, induces a compact self-adjoint form on H: for E(f),E(g)≤1, at 0<u<ε, the vanishing right endpoint gives |g(1−u)|≪√u; hence ∫₀^ε|f(u)g(1−u)|du≪ε by Cauchy–Schwarz. The analogous upper-end error is the same, and compactness on the middle interval follows by Rellich. Thus the full-support threshold is an actual model eigenvalue, the top value of the compact self-adjoint operator defined via

    L₀ = −(u² d/du)' + 3/4,        L₀ f = λ f(1−u);

in this differential equation λ is **the reciprocal** of the E-normalized top Rayleigh quotient. The Green kernel is explicit:
    G(u,v)= (1/2) min(u,v)^(1/2) [max(u,v)^(−3/2)−max(u,v)^(1/2)].
The homogeneous solutions u^(1/2),u^(−3/2) and their Wronskian, weighted by u², verify it. The positive Green kernel and the same absolute-value argument prove that the full-support top eigenvalue is positive and simple; the endpoint singularity at u=0 causes no loss of compactness of the reflected form.

Allowing nonsymmetric probes is **strictly** beneficial, even on each symmetric fixed I. If a symmetric top maximizer for E were also a maximizer over all weights, its differential equation and its reflection would give ((2u−1)f'(u))'=0. Regularity at u=1/2 makes the constant zero on both sides. The Dirichlet condition would force f=0, contradiction. This is a genuine change of optimization domain rather than a refinement of the symmetric decimal.

For a clean exact trial, take f(u)=1−u² in the full weighted domain. It is admissible by approximation with nonnegative smooth compact cutoffs: near u=0 the cutoff derivative is multiplied by u in the energy, and near u=1 f vanishes linearly. Direct integration gives

    E(f)=6/5,              C(f,f)=11/30,
    C(f,f)/Q_∞(f)=11π/(18e²).

Therefore any fixed t<11π/(18e²) admits one fixed smooth nonnegative asymmetrical probe supported in (a,1−a) for some predetermined rational a>0, with C/Q_N eventually larger than t. The sufficient condition that the ordinary compressed positive endpoint be at most t S(N) at all sufficiently large even N then yields Goldbach, with no GRH required for its formulation. This enlarged compression/threshold is not ordered against the narrower [1/3,2/3] test: it is larger and tests a larger support. By contrast, it is directly implied by either full S or R wherever the analytic construction exists. To avoid requiring a positive fraction of the expected count, use the prime-only, exact threshold (P) instead.

## 4. Additional consequences hidden in the full S/R norm bound

In the November paper let δ_N=√(S(N)/N)(log N)^(3/2). The paper itself, eqs. (2.28),(2.30), gives
    S(N;h) ⇔ ∥T_N∥ ≤ S(N)/(2h(N)√(1−η_N)),
    R(N)   ⇔ ∥T_N∥ ≤ δ_N.
The spectral product squares every eigenvalue: neither condition is a one-sided positive-branch assertion. Both would also control families that have nothing to do with the original central Goldbach proof.

For example, fix integer k≥1 and nonnegative independent smooth weights f supported in a short interval J⊂(1/5,3/10) and g in k+J. The cross character projection excludes its diagonal and every sum n+m=lN (their normalized sum lies strictly between k and k+1), and leaves only the positive difference m−n=kN. In the Beta-model evaluation the polarized test has signed pushforward in the scale t>0:
    H(t)=∫ f(u)g(u+t)du + ∫ f(u+t)g(u)du − ∫₀ᵗ f(u)g(t−u)du.
Its integral over t>0 vanishes, since the first two terms partition the integral over the quadrant by x<y or x>y, whereas the third covers the whole quadrant. Hence the same Mellin shift in their Lemma 7.2 cancels the density-series pole at w=1; the only surviving integer value is H(k)=∫ f(u)g(u+k)du. The cutoff Riesz norms are O_{f,g,k}(1) because their u-supports are fixed positive compact intervals. Thus GRH(N) and the full operator hypothesis give

    N^(−1) Σ_{m−n=kN, (nm,N)=1} Λ(n)Λ(m) f(n/N)g(m/N)
      = S(kN) ∫ f(u)g(u+k)du + O_{f,g,k}(∥T_N∥).

Prime-power removal costs o(1) for fixed k, and the primes dividing N are negligible; S(kN)≈_k S(N). Full S therefore entails the corresponding pointwise prime-difference asymptotics at every sufficiently large even target, in addition to Goldbach. This makes precise why one should not require a uniform full-operator estimate just to seek one prime pair.

In contrast, the [August Li–Liu 1+1.9 theorem](https://arxiv.org/abs/2606.05224v2) derives a lower bound for representations N=p+rq with r=1 **or** a prime satisfying r≤q^(9/10), by weighted sieving (EH strengthens the exponent, not to 1). The r>1 branch does not put any atom in A_N; a lower bound for this mixed support cannot certify strictness in (P) unless one independently controls the composite branch. This conclusion uses the August paper and does not rely on the further November aiXiv 1+1.75 claim.
