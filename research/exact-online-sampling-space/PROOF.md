# Zero entropy loss in exact finite-state sampling

Let $p$ be a law on a finite or countable alphabet. Call it **dyadic** if each positive atom is an integral power of $1/2$, not merely a rational number with power-of-two denominator. Use the exact online sampling model of Draper and Saad, [*Space–Entropy Lower Bounds for Random Sampling*, arXiv:2607.14503v1](https://arxiv.org/pdf/2607.14503v1), Definitions 4 and 6, with a fixed target law. All logarithms are base two.

Starting from one fixed state, the sampler in each round reads a finite prefix $c$ of fresh fair bits and emits a letter $x$ and a new state $t$. The choices of $c$ at each current state form an exhaustive prefix code (their cylinder probabilities sum to one); the empty string is permitted. The same rule is used on every round. Arbitrary per-round local computation and unbounded prefix lengths are permitted. Exactness means the unconditional output process from the specified start is iid $p$; it need not be iid conditional on every hidden state.

**Theorem.** There exists such a sampler with finitely many persistent states and zero asymptotic entropy loss per sample if and only if $p$ is dyadic. Here the loss after $n$ rounds is the expected pathwise difference between the total bits used and $-\log(\prod_{i=1}^n p(X_i))$. Zero rate means this expected difference is $o(n)$. This definition also applies without subtracting infinite expectations when $H(p)=\infty$.

This proves the zero-loss characterization asked in the unnumbered *Distribution Dependence* conjecture of [Draper and Saad, §9, p. 17](https://arxiv.org/pdf/2607.14503v1). It is not the SODA 2026 worst-case space conjecture, which they already proved in their Theorem 1. The converse construction is classical.

## 1. Recurrent paths are tight

Write $s_0$ for the initial state. Discard unreachable states. If an edge emits $x$ then $p_x>0$, by exactness and positive probability of the reaching path. Give that codeword edge weight $d=|c|+\log p_x$. Every finite path from $s_0$ has nonnegative total weight: the event of that particular codeword path has probability $2^{-L}$, at most the probability $p_u=\prod_i p_{u_i}$ of its output word $u$. Define $h(s)$ as the infimum of total weights of paths from $s_0$ to $s$. It is real and nonnegative (each state is reachable), with $h(s_0)=0$. By appending one edge,
$$
  \sigma(s,c,x,t)=|c|+\log p_x+h(s)-h(t)\ \ge 0.
$$
This is the state information potential and slack of Draper and Saad, §§4–5; the preceding observations give it directly for this fixed law. The sum of the slacks is the total pathwise information loss plus $h(s_0)-h(S_n)$. Since $h$ is bounded on the finite state space, the expected sum of slacks is $o(n)$ under the zero-rate hypothesis.

The states under fresh bits form a finite homogeneous Markov chain. Fix a reachable closed irreducible class $C$. Every state $s$ in $C$ has positive limiting Cesàro occupation probability starting from $s_0$: a finite prescribed path enters $C$ with positive probability, and conditional occupation averages within this class converge to its stationary probabilities. If a particular codeword leaving $s$ had positive slack, it would contribute its slack times $2^{-|c|}$ times the expected number of visits to $s$, which is of positive linear order. Hence **each codeword edge in $C$ has zero slack**.

## 2. A finite-valued likelihood ratio

Fix $s\in C$. Write $Q_s(u)$ for the probability of emitting a specified finite word $u$ starting in state $s$; this is not assumed to be $p_u$. For every such word using letters of positive $p$-mass, including the empty word, define $R(u)=Q_s(u)/p_u$. Take any particular codeword path from $s_0$ to $s$, with output $v$ and probability $b>0$. Since the future has fresh bits, unconditional iid exactness yields $bQ_s(u)\le p_vp_u$, so $R(u)\le p_v/b$, a bound uniform over words.

A particular path from $s$ emitting $u$ ends at some $t\in C$, and telescoping zero slack gives its probability as
$$
    2^{-L}=p_u\,2^{h(s)-h(t)} .
$$
These path events are disjoint by prefix-freeness, including when zero-length edges occur (the deterministic parsing is unique for the fixed number of rounds). Consequently
$$
 R(u)=\sum_{t\in C}m_t(u)\,2^{h(s)-h(t)}
$$
with $m_t(u)$ counting the possible codeword paths. They are finite nonnegative integers: the bound on $R(u)$ divided by the positive coefficient at $t$ bounds even the number of any finite selection of distinct such paths. All the integers thus belong to fixed finite ranges, independent of $u$. Two conclusions follow: (i) $R(u)$ takes finitely many values; (ii) for each $u$, $Q_s(u)$ is a finite sum of dyadic rationals $2^{-L}$ and is therefore rational.

The maximum of $R$ is attained at some word $u_*$ and is positive, since $R(\varnothing)=1$. For all $u$,
$$
 R(u)=\sum_{x:p_x>0}p_xR(ux).
$$
Indeed the probability of $u$ is the sum over its possible extensions, and no reachable transition can emit a zero-mass letter. At a maximizer every summand of $p_x(\max R-R(ux))$ is nonnegative and their sum is zero. Hence $ux$ is itself a maximizer for **every** positive-probability $x$; this holds also for countably many atoms. In particular
$$
 p_x=Q_s(u_*x)/Q_s(u_*)\in\mathbb Q,
 \qquad Q_s(u_*x^j)>0 \quad(j\ge1).
$$

## 3. The constant-letter cycle and the converse

In a path realizing the last display with $j=|C|$, at least one state repeats during the final run of $x$'s. The intervening cycle has length $1\le k\le |C|$ rounds and consumes a nonnegative integer $m$ bits. By telescoping its zero slacks, $p_x^k=2^{-m}$. Since $p_x$ is positive and rational, prime factorization of its numerator and denominator forces $p_x=2^{-a_x}$ for a nonnegative integer $a_x$. This applies to each positive atom.

Conversely, if $p_x=2^{-a_x}$, then $\sum_x2^{-a_x}=1$. Kraft's theorem gives a countable binary prefix code with these lengths. For completeness, enumerate leaves by nondecreasing length (only finitely many of each length) and take successive half-open intervals of lengths $2^{-a_x}$ filling $[0,1)$; at each step the left endpoint is a multiple of the current length. The corresponding dyadic cylinders give an exhaustive code, including the empty word for the point mass. Decode one fresh codeword each round and keep only one persistent state. The pathwise loss is identically zero. This is the standard instantaneous dyadic code, not a new sufficiency claim. ∎
