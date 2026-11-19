# Centering before averaging: a first-order weighted degree-square Max-Cut bound

Let G be any finite undirected loopless graph with nonnegative real edge weights, total W>0, weighted degrees d_i, and maximum cut weight C. Write p_i=d_i/(2W), P=Σp_i², and (for independent uniform signs ε_i) m=Σp_i ε_i. Then
$$
 \frac CW\ \ge\ \frac12+\frac{P}{2(1+2\sqrt P)}
 \ \ge\ \frac{1+P}{2}-P^{3/2}.
$$
Thus uniformly as P→0 the cut surplus is at least (1−o(1))P/2, with no conditions on support order, maximum ordinary degree, weight ratios, or limiting profile. This is an asymptotic form of the Braverman–Efremenko–Kol–Saxena–Zhang degree-square conjecture (ECCC 1.5 / ITCS 5), not the exact conjecture at positive P.

**Proof.** Normalize the weights by W, so Σ_{i<j}w_ij=1, Σ_j w_ij=2p_i, and Σp_i=1. In particular Σ_{i<j}w_ij(p_i+p_j)=2P. Define f(x)=Σ_{i<j}w_ij x_i x_j, and A=2C/W−1≥0. For every x∈[−1,1]^n, independent signs with respective means x_i have mean energy f(x) by looplessness. The minimum energy of an integral sign vector is −A, so f(x)≥−A.

Take an auxiliary scalar λ≥0. For every original sign vector ε, the vector with entries (ε_i−λm)/(1+λ|m|) belongs to the unit cube. Multiply its energy inequality by (1+λ|m|)². Since Σ_{i<j}w_ij(ε_i+ε_j)=2m, this is exactly
$$f(\varepsilon)-(2\lambda-\lambda^2)m^2\ge -A(1+\lambda|m|)^2.$$
Average this **before dividing**: Ef(ε)=0 and Em²=P by independence and zero means. Therefore for any 0≤λ≤2,
$$
 A\ge \frac{(2\lambda-\lambda^2)P}{1+2\lambda\,\mathbb E|m|+\lambda^2P}
 \ge \frac{(2\lambda-\lambda^2)P}{(1+\lambda\sqrt P)^2}.
$$
The last step uses E|m|≤√P and the nonnegative numerator. Taking λ=1/(1+√P) yields A≥P/(1+2√P). Finally (1+x)^{-1}≥1−x for x≥0, giving the stated asymptotic error. For the same first-order conclusion, no optimization is needed: λ=1 already yields A≥P/(1+√P)². No fourth moment, invariance principle or approximation algorithm is used.

The odd equally weighted cliques have P=1/n and C/W=(1+P)/2, so leading coefficient 1/2 cannot be increased uniformly with o(P) error. This does not establish optimality of the residual order or constant. Balanced cuts already give the leading conclusion whenever nP→1; our scope also allows that product to diverge. For example, for disjoint uniform cliques on k and k² vertices given equal total weight, P=(1/k+1/k²)/4 and n=k+k². This illustrates the distinction of parameters, not a new claim on cliques. Parallel edges aggregate and zero-weight edges/isolates do not matter. W=0 is trivial in the unnormalized problem and P is undefined.
