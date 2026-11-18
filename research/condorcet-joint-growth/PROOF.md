# Strict Condorcet winners at two growing parameters

Setup: m independent voters choose uniform complete strict orders on n alternatives (impartial culture). A strict global Condorcet winner beats each other alternative by strictly more than m/2 votes. No restriction on growth rates or relative parity for the global theorem.

**Theorem.** If m,n both tend to infinity, the probability Q(m,n) of a strict global Condorcet winner obeys
$$
             Q(m,n)=n^{-1+o(1)}.
$$
This is a logarithmic equivalence, not a ratio asymptotic. For arbitrary m≥1 the uniform lower bound below also applies. The odd-m hypercube application is a distinct local statement.

## Setup (classical rank representation)

Let d=n-1, L=log d. Give each voter independent U[0,1] scores for each alternative, and rank higher scores first. Conditional on the designated candidate's score vector u, versus one competitor its votes are independent Bernoulli(u_i). Write S for the sum, b(u)=P_u(S≤m/2). Votes against different competitors are conditionally independent. Hence θ(d,m)=E[(1-b(U))^d] is the probability of a designated winner, and Q(m,n)=nθ(n−1,m) since two strict winners cannot coexist. This integral is due to earlier work; see [Sauermann](https://arxiv.org/abs/2203.13713) and [Pittel, equation (1.5)](https://arxiv.org/html/2506.20613v5).

For a≥0 write
$$
h_a(u)=(1-u)e^a+ue^{-a},\quad X_a=-\sum_i\log h_a(u_i),\qquad
q_a(u)=ue^{-a}/h_a(u).
$$
Two distinct tilts operate on different sample spaces. Conditional on u, exponential Markov applied to exp[a(m−2S)] gives b≤exp(−X_a). Unconditionally,
$$
\mathbb E_U e^{2X_a}=1. \tag{1}
$$
for each deterministic a, because the integral of the inverse square of an affine function with positive endpoint values A,B equals 1/(AB) (including A=B).

## Uniform lower bound

Tilt the law of U by the density exp(2X_a) from (1). In this tilted law the summands Y=−log h_a(U_i) are iid, with density exp(y)/(2 sinh a) on [−a,a] for a>0 (a direct substitution). Its mean and variance are μ=a coth a−1 and v=1−a²/(sinh a)², by integrating exp(ty) on that fixed interval at t=1 and differentiating its log. The function μ is continuous, strictly increasing (sinh a cosh a>a) from 0 to infinity. One has v≤5μ: for a≤1, v≤a² as Y lies in [−a,a], and μ=(∫_0^a t sinh(t)dt)/sinh a≥a²/(3 cosh 1); for a≥1 use v≤1 and monotonicity. In particular σ²=Var_tilt X_a≤5E_tilt X_a.

Set H=log(2d), choose a deterministically by mμ=(√H+10)². Chebyshev gives tilted mass at least 3/4 within 2σ of the mean; this interval lies in [H,H+25√H+145] since σ≤√5(√H+10). There b≤exp(−H)=1/(2d), so (1−b)^d≥1/2. Undoing the density,
$$
\theta(d,m)\ge (3/8)\exp[-2(H+25\sqrt H+145)]. \tag{2}
$$
Uniform in m≥1.

## Uniform upper bound along m→∞

Take d large enough that L=log d≥1 and 4L/d<3/4. It suffices to bound the old U-probability of b≤4L/d, since on the complement (1−b)^d≤d^{-4}. Assume m≥256. For a given environment u with b≤4L/d, one has sum u_i>m/2−√m (otherwise variance ≤m/4 and Chebyshev gives b≥3/4). Outside a null set all u_i∈(0,1). As a increases from 0 to infinity the sum of q_a(u_i) decreases continuously to zero. There is therefore a unique random a>0 such that
$$
\sum_i q_a(u_i)=m/2-\sqrt m. \tag{3}
$$
Each conditional Bernoulli vote is tilted from success probability u_i to q_a(u_i), giving the product Radon–Nikodym derivative from the new law back to the old law exactly exp[−X_a+a(2S−m)]. In the new law, with probability at least 3/4 the sum is strictly within √m of its (3) mean, hence m/2−2√m<S<m/2. Consequently
$$
b \ge (3/4)\exp[-X_a-4a\sqrt m],\qquad
X_a\ge L-\log(16L/3)-4a\sqrt m. \tag{4}
$$

**Uniform cutoff.** Let c=1/[4(1+3 exp(12))] and fix C=max(100,10/c). Let A=C(√(L/m)+L/m). The old U-probability that (3) has a solution a>A is ≤d^{-4}. In fact this event requires sum q_A>m/2−√m. If 0<A≤6, E q_A≤1/2−cA: derivative in a of q_a is −2q_a(1−q_a); on 1/4≤U≤3/4 and 0≤a≤6 one has q_a≥1/(1+3exp(12)), q_a≤3/4. Integrate over that half interval. Since cA≥10√(L/m)≥2/√m, Hoeffding for independent variables in [0,1] gives exp(−mc²A²/2)≤d^{-4}. If A≥6 then m/2−√m≥3m/8; whenever sum q_A>3m/8 at least m/6 indices have q_A≥1/4. A single index has that event with probability 3/(exp(2A)+3)≤3exp(−2A). A union bound over index sets gives at most
$$
2^m(3e^{-2A})^{m/6}\le e^{-mA/6}\le d^{-4}.
$$
Here log2+(log3)/6≤1≤A/6 and mA≥CL. No pointwise bound on random a is asserted.

**Discretization in the original law.** X'_a=2∑q_a−m, and X''_a=−4∑q_a(1−q_a)∈[−m,0]. At (3), X'_a=−2√m. For a≤A choose gridpoint j/√m within 1/√m, 0≤j≤ceil(A√m). Taylor gives X_{j/√m}≥X_a−5/2. For each fixed gridpoint (1) gives P(X_j≥t)≤e^{-2t}, valid even if t<0. By (4), outside the cutoff exception, b≤4L/d implies such a gridpoint exceeds t=L−log(16L/3)−4A√m−5/2. There are ≤2+A√m gridpoints. Thus
$$
\theta(d,m)\le 2d^{-4}+(2+A\sqrt m)e^{-2t},\qquad
A\sqrt m=C(\sqrt L+L/\sqrt m). \tag{5}
$$
When d,m→∞ the correction in t is o(L), and the log grid size is O(log L); there is no condition on their relative growth rates. Combining (2),(5) with the rank integral proves the theorem. No claim for a sharp multiplicative constant, nor for fixed-m exponents (those are already known).

## Local hypercube application

Let alternatives be the 2^d vertices of the hypercube, with the same impartial-culture full rankings. A hypercube Condorcet winner (HCW) beats its d neighbors, not necessarily any other alternative. For odd m there are no pairwise ties. A specified vertex is an HCW with probability θ(d,m), hence E W=2^d θ(d,m) for their count W. Greedily selecting a vertex and removing the Hamming ball of radius 2 produces ≥2^d/B selected vertices, B=1+d+binom(d,2). Their closed radius-one stars are disjoint, so their HCW events are independent by the score coupling (not by independence of incident edge directions). It follows
$$
P(W=0)\le\exp[-2^d\theta(d,m)/B]
\le\exp[-2^d d^{-4-o(1)}],
$$
uniformly over odd m, including fixed m. Variance satisfies Var W ≤2^d B θ (ordered covariance pairs; pairs of distance ≥3 give zero, all others ≤θ). Thus W/EW→1 in probability uniformly and W=2^{d-o(d)} whp. In the joint m,d→∞ case EW=2^d d^{-2+o(1)}. By contrast under the independent fair orientation model W→Poisson(1) (already known via [random games](https://arxiv.org/abs/2007.08518)), so eventual strict existence-probability separation, uniformly in odd m. This only proves the comparison for all sufficiently large d, not at every d≥2.
