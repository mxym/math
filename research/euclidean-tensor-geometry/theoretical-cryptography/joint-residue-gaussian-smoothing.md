# Joint smoothing with a Gaussian residue label

**Scope.** This is a statistical lemma about a standalone discrete Gaussian, an independent ordinary Gaussian, and a finite residue label. It measures the error of a Gaussian approximation before any output wrapping. No secret, cryptanalysis, practical sample parameters, or solver is considered.

In the proof of [Lyubashevsky–Peikert–Regev, Lemmas 4.7–4.8](https://sites.cc.gatech.edu/fac/cpeikert/pubs/ideal-lwe.pdf), a discrete Gaussian residue is first made close to uniform, then the noisy value conditioned on each residue is made close to a continuous Gaussian. [Peikert–Regev–Stephens-Davidowitz, Lemma 6.8](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf) uses the elliptical analogue. The two-way Gaussian identity underlying the mixed convolution is standard (see also [Peikert 2010, Theorem 3.1](https://eprint.iacr.org/2010/088.pdf), [Genise et al.](https://web.eecs.umich.edu/~cpeikert/pubs/gaussians.pdf), and [Luzzi et al., Lemma 2.4](https://eprint.iacr.org/2019/1171.pdf)). The question here is what is necessary and sufficient for the **joint** total-variation comparison in an orthogonal lattice, with arbitrary labels and noise-width ratios. This is not a new mixed-convolution identity or a new hardness reduction.

## 1. Exact finite-index likelihood

For a positive-definite real matrix A, let G_A have the density proportional to exp(-π x^T A^{-1}x), hence covariance A/(2π). Let h_{A,L} be its density when reduced modulo lattice L, relative to probability Haar measure. Poisson summation gives

    h_{A,L}(u) = sum_{v in L*} exp(-π v^T A v) exp(2π i v·u).

Take full lattices L0 ⊂ L with finite index M, and a fixed shift t. Let X be G_A restricted to t+L and normalized as a discrete mass. Independently choose G_B, let Y=X+G_B, and label X by Z=X mod L0. Write P for the pair law and Q for independent uniform Z on (t+L)/L0 and Y from G_{A+B}.

Set S=A+B, C=(A^{-1}+B^{-1})^{-1}, T=A S^{-1}, and D=A-C=T S T^T. These identities hold without commutativity. Under Q put U=T Y-Z mod L0. Then

    (dP/dQ)(Z,Y) = h_{C,L0}(U) / h_{A,L}(t),
    d law_Q(U)/d Haar_{L0}(u) = h_{D,L}(u+t).

Indeed, completing the square gives g_A(x)g_B(y-x)=g_S(y)g_C(x-Ty). The normalizing sum on t+L is h_{A,L}(t)/covol(L); the numerator sum over label Z uses h_{C,L0}(Ty-Z)/covol(L0). Symmetry and the factor M cancel the covolumes. Under Q, uniform averaging of the changes by L/L0 removes exactly the frequencies outside L*. In particular E_Q h_{C,L0}(U)=h_{A,L}(t); this also follows by integrating the likelihood. All distinctions in this joint comparison are preserved by the single phase U; this is a statement about the mathematical experiment, not a claim about computing a phase from cryptographic data.

Thus the exact TV is

    (1/(2 h_{A,L}(t))) integral_{R^n/L0}
         h_{D,L}(u+t) |h_{C,L0}(u)-h_{A,L}(t)| du.

Writing b_v=exp(-π v^T C v), the exact χ² is

    sum_{v,w in L0*} b_v b_w [φ(v+w)-φ(v)φ(w)] / h_{A,L}(t)^2,
    φ(v) = 1_{v in L*} exp(-π v^T D v) exp(-2π i v·t).

Absolute convergence follows from positive definiteness of C. In particular, low frequencies may disappear in the mean without disappearing in the second moment.

A dimension-free consequence: if ε=||h_{D,L}-1||_∞≤1/4, joint TV differs relatively from d_TV(h_{C,L0},Haar) by at most 4ε. Put m=h_{A,L}(t). Since h_{D,L} integrates to one also over R^n/L0, the mean difference |m-1| is at most ε||h_{C,L0}-1||_1. The change from the unweighted integrand |h_C-1| is bounded by (weight change) plus (mean change), together at most 2ε||h_C-1||_1. Finally m is between 1-ε and 1+ε by averaging h_{D,L} against h_{C,L0}. This proves the relative estimate, including the zero case. In this regime the correct criterion uses L1 flatness at C rather than L∞ at C. [Luzzi, Ling and Bloch](https://eprint.iacr.org/2022/808.pdf) previously use L1 flatness and uniform dithering for a different rounding experiment; the two conditions here concern the joint residue label and the conditional Gaussian posterior phase.

## 2. Orthogonal theorem: all shifts and noise ratios

Divide each orthogonal coordinate by the step of L0 in that coordinate. For each coordinate i, then L0=Z, L=q_i^{-1} Z, q_i≥1 an integer; let a_i,b_i>0 be the scalar entries of A,B in these units, and t_i any shift. We assume diagonal A,B in the same coordinates. The result also covers any independent product of such coordinates, e.g. across separately simulated samples.

Write c_i=a_i b_i/(a_i+b_i), d_i=a_i-c_i>0, u_i=exp(-π c_i), and θ_i=2π t_i. Define the following explicitly nonnegative number V_i:

    q_i >= 3:  V_i = 2 u_i^2;
    q_i = 2:   V_i = 2 u_i^2 [1+e^(-4π d_i) cos(2θ_i)];
    q_i = 1:   V_i = 2 u_i^2 [
                           cos^2(θ_i) (1-e^(-2π d_i))^2
                         + sin^2(θ_i) (1-e^(-4π d_i)) ].

Put V=sum_i V_i. For sufficiently small absolute u0>0, uniformly over all products with max_i u_i≤u0,

    c min(1,sqrt(V)) ≤ d_TV(P,Q) ≤ C min(1,sqrt(V))

for absolute constants c,C>0. In triangular arrays with max_i u_i→0, there is also the exact profile:

* If V→v in (0,∞), TV→2 Φ(sqrt(v)/2)-1, with Φ the standard-normal CDF.
* If V→0 and max_i V_i/V→0, TV~sqrt(V/(2π)).
* If V→∞, TV→1.

The condition on max_i V_i/V for the relative small-TV profile is not needed for the comparison bound. Product coordinates are independent under both laws, but neither width ratios nor label multiplicities need be constant across coordinates.

### Proof of the orthogonal theorem

Fix one coordinate and suppress i. Under Q the phase is U=G_d-t-J/q mod one, with J uniform in {0,...,q-1} independent of G_d. Write F_k=cos(2π k U), m=E_Q h_{c,Z}(U)=1+O(u), and L=h_{c,Z}(U)/m. The theta series gives

    L-1=(2/m) sum_{k≥1} u^{k^2}(F_k-E F_k).

The first mode has 4u² Var(F_1)=V_i: use E exp(2π i k G_d)=exp(-π d k²) and the finite sum of q-th roots of unity. Crucially, even when d is arbitrarily small and the first mode nearly vanishes, its variance still controls the centered remainder. For any fixed p≥2 there is K_p, independent of d,t,q,k, with

    ||F_k-E F_k||_p ≤ K_p k² sqrt(Var(F_1)).

For q≥3 this follows from boundedness and Var(F_1)=1/2. For q=1 use

    ||cos(2π k G_d)-E cos(2π k G_d)||_p ≤ K_p k² min(d,1),
    ||sin(2π k G_d)||_p ≤ K_p k min(sqrt(d),1).

These follow from the sine bound, the quadratic bound for 1-cos, and Gaussian moments, using boundedness when d≥1. The addition formula and |sin(kθ)|≤k|sin θ| give an upper bound proportional to k²[min(d,1)+|sin θ|min(sqrt(d),1)]. The q=1 variance formula gives a comparable square root (if |cos θ| is small, the sine term already dominates min(d,1)). For q=2 odd k, the centered cosine carries the independent sign (-1)^J and has mean zero. The odd multiple inequality |cos(kx)|≤k|cos x| bounds its norm by K_p k[|cos θ|+min(sqrt(d),1)]. For even k, remove the sign, apply the q=1 Gaussian fluctuation estimates, and use the same upper bound with k². The q=2 variance is comparable to [|cos θ|+min(sqrt(d),1)]² since it equals (1-e^(-4π d))/2 + e^(-4π d)cos²θ.

Consequently, in L² the centered series after its first mode is O(u^4 sqrt(Var(F_1))); the division by m and the first mode give

    E_Q(L-1)^2=V_i(1+O(u_i)),
    E_Q|L-1|^p≤K'_p V_i^{p/2},       ||L-1||_∞=O(u_i).

These bounds are uniform. Set δ_i=L_i-1 and v_i=E δ_i². Then sum v_i is comparable to V and asymptotic to V when max u_i→0. Independence gives E(prod_i L_i-1)²=prod_i(1+v_i)-1. It proves the upper estimate for bounded V. For the lower estimate at small V, write prod_i(1+δ_i)-1=sum_i δ_i+R. Orthogonality of disjoint subset monomials implies E R²=O(V²). The independent centered sum W=sum_i δ_i has E W² comparable to V and E W^4=O(V²) by the fourth moment bound. Hölder interpolation gives E|W|≥(E W²)^(3/2)/(E W⁴)^(1/2), hence TV≥c sqrt(V) when V is sufficiently small. For all remaining V, the Hellinger affinity is prod_i E sqrt(1+δ_i)≤exp(-c' V) by the second-order expansion with uniformly small sup norm. Since TV is at least one minus the affinity, this gives the remaining lower bound and the V→∞ limit.

For finite positive v, the Lyapunov bound follows from sum_i E|δ_i|³ ≤ O(max_i u_i)sum_i v_i. Also sum_i(δ_i²-v_i) tends to zero in L² by the same sup-norm bound. Taylor expanding log(prod_i(1+δ_i)) gives convergence under Q to N(-v/2,v). TV equals E_Q[(1-exp(log(dP/dQ)))_+], a bounded continuous functional; direct Gaussian integration gives the displayed profile. For V→0 with max V_i/V→0 apply Lyapunov to W/sqrt(sum v_i) using the moment bound. Uniform integrability then gives E|W|~sqrt(2V/π). The remainder R=O_{L²}(V) is lower order.

## 3. Consequences and boundaries

For centered nested cubic lattices (all t_i=0 and q_i=q≥2), the leading variance is bounded between 2u_i² and 4u_i² even for d_i→0. In particular, no additional phase-mixing assumption is necessary. For equal c,d and N independent coordinates, V=2N e^(-2πc) for q≥3 and differs by the factor 1+e^(-4πd) for q=2. With q≥3, or q=2 and d→∞, a critical width-squared c=(log N+s)/(2π) gives limiting TV 2Φ(e^(-s/2)/sqrt(2))-1. Above it TV→0, below it TV→1, provided the stated max u condition holds. In contrast, the L∞ smoothing hypothesis on Z^N asks N e^(-πc)→0 in this range: the constant in front of log N for vanishing TV is halved in squared-width units. For equal widths in the same q≥3 or q=2, d→∞ regimes above this threshold, TV~sqrt(N/π) e^(-πc); for a fixed target N^{-K} this gives the coefficient (K+1/2) rather than (K+1) in front of (log N)/π. In this equal-width model, requiring negligible error in N, as opposed to a fixed inverse-polynomial error, still takes c/log N→∞.

The unrestricted formula does not say only the harmonic width matters. With q=1 and integer t, d→0 suppresses V by an additional factor of order d²; with q=1 and a quarter shift it is order d instead. With q=2 and a quarter shift it is again order d. With q=3 the label preserves the first-mode variance even in those extreme ratios. Thus the labelled and unlabelled experiments are genuinely different, and shifted and centered label models must not be conflated.

For the original statistical step, rescale z before convolution so that X=z/q is supported on q^{-1}I, and use the label X mod I. The independent continuous perturbation following multiplication by a fixed nonzero e can be written, before wrapping, as an elliptical additive Gaussian on the X side of that invertible multiplication. Label relabelling and output wrapping cannot increase joint TV. Thus the finite-index identity applies directly to this comparison. The sharp orthogonal specialization applies only when the lattice and both covariances really separate in one orthonormal basis (for example, a scaled cubic canonical lattice from a power-of-two cyclotomic and spherical covariances). Multiplication by a general e need not make this an orthogonal product in that lattice basis. The lower bounds concern the unwrapped joint comparison and need not survive the final loss of information. No claim is made that the worst-case Ring-LWE theorem's parameter has changed for all ideals or error distributions.

### Checking the formulas

The adjacent JS file uses only generated arithmetic examples. It verifies the label Fourier selection rule, the first- and second-moment factors by exact rational enumeration of toy phase laws on roots of unity represented in a cyclotomic integer basis, and the scalar completed-square identity by exact fractions. A separate floating check compares finite theta expansions with quadratic products of independent formal Fourier modes. These checks are not a substitute for the proof or an experiment on Ring-LWE.
