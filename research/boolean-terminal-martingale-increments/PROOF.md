# Maximum increments of bounded martingales with nearly Boolean terminal values

Let (X_i,F_i) for 0≤i≤n be a real martingale, n≥1, on any probability space, with 0≤X_i≤1 a.s. and deterministic X_0. Set μ=min(X_0,1−X_0), v=E[X_n(1−X_n)], and M=max_(1≤i≤n)|X_i−X_(i−1)|. No regular conditional law or finite filtration is required.

**Theorem.** For every a>0 with θ=1/4−(n+1)a²>0,

    Pr[M≥a] ≥ max{0, θ μ−(1+2θ)v}.                        (1)

This is a bound on a random variable in a stochastic process. It does not depend on how the process is sampled and does not analyze a cryptographic protocol.

## 1. Conditional stopped variance

Write Δ_j=X_j−X_(j−1) and V(x)=x(1−x). At a deterministic time i<n, let A_i^+= {max_(i<j≤n)|Δ_j|≥a}. Stop at the first j>i with |Δ_j|≥a, or at n if none occurs, denoting the bounded stopping time by T. Then

    V(X_i) = E[Σ_(j=i+1)^T Δ_j² + V(X_T) | F_i].          (2)

To see this, for j>i the indicator of T≥j is F_(j−1)-measurable: the process has not reached the stopping condition before j. Thus the stopped differences Δ_j 1_{T≥j} have conditional mean zero and are pairwise conditionally orthogonal given F_i. Expanding their sum gives E[X_T|F_i]=X_i and E[(X_T−X_i)²|F_i]=E[Σ_(j=i+1)^T Δ_j²|F_i]. Substituting V(x)=x−x² gives (2). The same identity is trivial at i=n with an empty sum.

On the complement of A_i^+, T=n and all the summands have size at most a². On A_i^+ all but the last have size at most a². If x,y∈[0,1] are the states on either side of that last jump, then

    (y−x)² + V(y) = x² + (1−2x)y ≤ max{x²,(1−x)²} ≤ 1.

Hence in either case the variable in (2) is at most

    (n−i)a² + V(X_n) + 1_(A_i^+).

In particular, with p_i=Pr[A_i^+|F_i],

    p_i ≥ V(X_i)−(n−i)a²−E[V(X_n)|F_i].                 (3)

These inequalities also hold at i=n if A_n^+ is defined as empty. We use (3) on events selected by F_i, not by conditioning on future success.

## 2. Clean midpoint crossing

By reflection X↦1−X we may assume X_0=μ≤1/2. Let H be the first i∈{0,…,n} with X_i≥1/2, with H=∞ if there is no such i, and let C={H≤n}. Even with a non-Boolean terminal value,

    Pr[C] ≥ Pr[X_n≥1/2] ≥ E[X_n 1_{X_n≥1/2}]
          = μ − E[X_n 1_{X_n<1/2}] ≥ μ−2v.              (4)

The last step uses x≤2V(x) at x≤1/2. For each i define B_i={H=i and |Δ_j|<a for 1≤j≤i}. This event belongs to F_i. If i=0, then X_0=1/2 on B_0; if i>0, then X_(i−1)<1/2 and the crossing jump is smaller than a. In either case X_i∈[1/2,1/2+a] on B_i, and V(X_i)≥1/4−a². Combining with (3), then taking expectations after multiplication by 1_(B_i), gives

    Pr[B_i ∩ A_i^+] ≥ θ Pr[B_i] − E[1_(B_i) V(X_n)].

Let D=C\∪_i B_i. It is a set of crossings with a gap already observed, so D⊆{M≥a}. The events D and B_i∩A_i^+ are disjoint and all contained in {M≥a}. Summing the last bound and using V≥0, 0<θ≤1, gives

    Pr[M≥a] ≥ Pr[D]+θΣ_i Pr[B_i]−v ≥ θ Pr[C]−v.

With (4) and nonnegativity this proves (1). In particular X_0=0 or 1 is allowed (then the entire martingale is constant). The equality convention M≥a agrees with recognizing a jump of exactly a while “clean” means every earlier jump is strictly below a. There is no requirement to observe a jump beyond time n.

## 3. Boolean case, scope, and calibrations

If X_n∈{0,1} a.s. then every X_i=E[X_n|F_i] is automatically in [0,1] and v=0. At a=1/sqrt(12(n+1)), θ=1/6 and

    Pr[M≥a]·a ≥ μ/(12 sqrt(3(n+1))) ≥ μ/(12 sqrt(6n)).

An observed-prefix stopping time at the first step with magnitude at least a, or n+1 on no such step, realizes this probability exactly when X_(n+1)=X_n. This equivalence is just event bookkeeping for the mathematical maximum; no earlier-than-observed decision is claimed. It gives the AICR c/0030 formulation for all n≥1 and 0<μ≤1/2. No inference about a protocol, its security, or the optimality of constants is drawn.

For fixed a in the theorem and μ<a, revealing a Bernoulli(μ) variable at one step and repeating that terminal value for the other steps yields Pr[M≥a]=μ. Thus the linear dependence on μ for a fixed threshold cannot be improved to a higher probability order uniformly in sufficiently small μ. This example does not upper-bound the best product over all thresholds. Without a terminal hypothesis an interior constant martingale has positive μ and no gaps at all; the purely literal unqualified sentence in the primary source would then be false. The non-Boolean estimate (1) quantifies one way of weakening the terminal condition, rather than omitting it.
