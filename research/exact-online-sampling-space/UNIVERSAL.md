# A cardinality-independent repair for exact online sampling

Use the abstract prefix-code model of [Draper and Saad, arXiv:2607.14503v1, Definitions 4 and 6](https://arxiv.org/pdf/2607.14503v1). In particular target laws can have countable support, arbitrary real probabilities, and are available to the per-round map; there is no temporary computation or oracle bound in this model. Logs are base two except for $\ln$.

**Theorem.** For every integer $L\ge16$ there is an exact online sampler with $L+1$ persistent states, simultaneously for every sequence of target distributions on $\mathbb N$. Its expected pathwise information loss after $n$ draws is at most
$$
 \log L+2+n\frac8L\left(2\log L+8+\frac1{\ln 2}\right).
$$
Consequently, for the unrestricted family of target laws, the minimum number of persistent bits for a redundancy rate $\varepsilon$ is $\log(1/\varepsilon)+O(\log\log(1/\varepsilon))$. In particular the leading multiplicative coefficient is **one**. The lower bound is prior: [Draper and Saad, Theorem 1(1.2)](https://arxiv.org/pdf/2607.14503v1) gives at least $1/\varepsilon$ states even on their infinite Bernoulli subfamily. The upper bound is uniform over laws and alphabets, not a lower bound for every individual law. This concerns persistent space, not time, temporary space, computable-real oracles, or pointwise worst-case input length.

**State law.** The active states $s\in\{L,\ldots,2L-1\}$ have target distribution $\pi_s=1/(Zs)$ with $Z=\sum_{s=L}^{2L-1}1/s>1/2$. In the initial round, from one extra deterministic state, first generate $s\sim\pi$ by the classical Knuth–Yao tree at cost at most $\log L+2$ in expectation. Then use the round rule below. We maintain $\pi$ conditional on the public output history.

**Dyadic tickets with release times.** For the current target $p$, ignore zero masses. For each $p_x>0$ put
$$
 b_x=\lfloor\log(1/p_x)\rfloor,\quad w_x=2^{-b_x},\quad v_x=p_x/w_x,\quad a_x=\lfloor Lv_x\rfloor-1.
$$
Here $1/2<v_x\le1$, $1\le a_x\le L$, $\sum_x w_x\le2$, and $\sum_x w_xv_x=1$. For each integer $z\in[a_x,2a_x)$ make one ticket $(x,z)$ of size $w_x$. It may be assigned to row $s$ only when $z+1\le v_xs$. Rows $L,\ldots,2L-1$ have capacity one each. Total ticket mass $W=\sum_x a_xw_x$ satisfies
$$
                 L-4\le W\le L.
$$
Indeed $Lv_x-2\le a_x\le Lv_x$. After row $s$, the number of tickets of label $x$ whose release condition was not yet met is at most
$$
  (2a_x-\lfloor v_xs\rfloor)_+ \ \le\ (2L-1-s)v_x .
$$
For the latter inequality use $2a_x\le2Lv_x-2$, $\lfloor v_xs\rfloor\ge v_xs-1$ and $v_x\le1$. Thus the total unreleased mass after row $s$ is at most $2L-1-s$, the remaining capacity.

These inequalities suffice for a packing with no ticket discarded. At each row take from the available, unassigned tickets total mass exactly one if their sum is at least one; otherwise take them all. The exact-fill claim for dyadic sizes $\le1$ holds also for a countable multiset: if its total is one take the whole set; if greater than one take a finite subset of sum at least one and fill greedily by decreasing size. At each size any positive remaining capacity is an integer multiple of that size, so a greedy failure would have used everything. Before the first row the remaining mass is at most the remaining capacity. Filling a row preserves this inequality; when the row cannot be filled, only unreleased mass remains, bounded above as just proved. After the last row nothing remains. All choices can be fixed deterministically, for example using the first sufficient finite prefix in a fixed enumeration, with fixed tie-breaking. No effectiveness assumption about the input law is needed.

**Normal and escape words.** In each row assign its tickets distinct binary prefix words of lengths $b_x$ by arranging their dyadic intervals in nonincreasing order of size, consecutively starting at zero. There are finitely many tickets of each size in a row. The intervals are aligned, and the unused part is one interval of length $e_s$ at the right end. If the random bit stream lies there, its minimal dyadic prefix contained in this interval selects the escape branch; endpoints on null binary encodings do not affect exhaustiveness.

Upon drawing a normal ticket $(x,z)$ from state $s$, emit $x$, then append fresh bits to $z$ via $z\gets 2z+b$ until reaching a new state $t\ge L$. Always $t<2L$, and the continuation is exhaustive. For each $(x,t)$ there is exactly one ticket and one such continuation: successively remove low bits of $t$ until reaching $[a_x,2a_x)$, which is possible since $t\ge L\ge a_x$. Every intermediate after at least one removal is $<L$, so the reverse path indeed stops for the first time at $t$. If this path uses $k$ appended bits, its normal joint mass satisfies
$$
 q_{xt}=\pi_s2^{-b_x-k}\le p_x\pi_t=:r_{xt},
$$
since $t/2^k<z+1\le v_xs$. This renormalization is related to asymmetric numeral systems; exactness is supplied by the one-sided packing and the following correction, not an assumption on a standard ANS decoder.

The escape mass is
$$
 \delta=\sum_s\pi_s e_s\le \frac2L\sum_s e_s
         =\frac2L(L-W)\le 8/L .
$$
The nonnegative deficits $r_{xt}-q_{xt}$ sum to $\delta$. Conditional on escape, use fresh bits to sample the pair $(x,t)$ from the normalized deficits $d_{xt}=(r_{xt}-q_{xt})/\delta$. If $\delta=0$ no repair is necessary. The joint law becomes exactly $p\otimes\pi$, so the state invariant holds independently of the emitted symbol. Induction gives the full product law for any sequence of target laws. The same conditional argument applies to public-history-adaptive choices made without access to the private state or its fresh bits. At each row the normal words, their continuations, and the escape words followed by repair words form an exhaustive prefix code. Concatenating the initial tree and the first round gives the required deterministic-start model.

**Loss without subtracting infinite entropies.** Sample the repair law by partitioning $[0,1)$ into intervals of masses $d_{xt}$ and reading a dyadic prefix until its cylinder is contained in one interval. Conditional on an interval of length $w>0$, the probability of needing more than $j$ bits is at most $\min(1,2^{1-j}/w)$: only the two boundary cells can still be unresolved. Summation from $j=0$ gives conditional expected length $\le\log(1/w)+4$ (split at $\lceil\log(1/w)\rceil+1$). The same estimate holds for the first escape prefix conditional on its residual interval $e_s>0$.

For a complete word of length $K$ from $s$ to $(x,t)$, define
$$
        D=K+\log(p_x\pi_t/\pi_s).
$$
This quantity is nonnegative pathwise: the unconditional mass $\pi_s2^{-K}$ of the particular word is bounded by the total mass $r_{xt}$. The normal contribution to its expectation is bounded by
$$
   \sum_{x,t} q_{xt}\log(r_{xt}/q_{xt})\le\delta/\ln2 .
$$
For an escape from state $s$ write $\alpha_s=\pi_se_s$. Conditional on $s$, escape and repair output $(x,t)$, the expected adjusted loss is at most $\log(r_{xt}/d_{xt})-\log\alpha_s+8$, by the two conditional word-length estimates and fresh independent repair bits. On the support of $d$, $r_{xt}/d_{xt}\ge\delta$; the positive part of its logarithm is integrable under $d$ since $\log^+u\le u/\ln2$ and $\sum_{d>0} r_{xt}\le1$. Jensen therefore gives $\sum d_{xt}\log(r_{xt}/d_{xt})\le0$. Summing the escape contribution bounds it by
$$
    8\delta+\sum_s\alpha_s\log(1/\alpha_s)
       \le \delta\big(8+\log(L/\delta)\big).
$$
The last inequality uses that $\alpha/\delta$ is a probability law on $L$ points. For $L\ge16$ the function $v\log(L/v)$ increases on $0<v\le 1$, so substituting $\delta\le8/L$ gives the stated looser rate. Summing adjusted losses cancels the state terms in expectation because $\pi$ is preserved; these terms are bounded, so this is valid also when $H(p)=\infty$. Add the one-time initialization cost. Taking $L$ of order $C\varepsilon^{-1}\log(1/\varepsilon)$ with a sufficiently large universal constant $C$ yields the upper coding-space bound. ∎
