# The information missing from the central prime slice: a sharp rank threshold for masks on genuine primes

Write $L=\log P$, $H=\log\log P$, $C=[P/3,2P/3]$ for an even target $P$, and let $G(P)$ be its number of ordered genuine central Goldbach pairs. Fix $A,B,c>0$, put $D=\exp(L/H^A)$ and $W=\operatorname{lcm}(1,\ldots,\lfloor cH\rfloor)$. Partition $C$ into $\lceil L^B\rceil$ equal intervals (fix any disjoint endpoint convention). A *prime mask* is a subset of the **actual primes**, agreeing with them outside $C$. Factorizations below are ordinary factorizations; every prime factor of an odd composite in $C$ is $\le2P/9$, so its factors are present in either mask.

**Theorem.** For every fixed $1<t<e$ and every sufficiently large even $P$, there are two masks, on and off, with these properties.

1. On retains every central Goldbach pair; off has none. The masks contain **equal numbers** of primes in every interval of the partition and each individual residue class modulo $W$.
2. Both masks retain all the actual incidences $P=p+dq$ for $1<d\le D$ odd squarefree, $p,q$ primes and $dq\in C$, and all $P=p+drs$ for $d\le D$ odd squarefree, $P^{.1}<r<s$ primes and $drs\in C$. In particular all signed sums or arbitrary labelled selections of these non-atom incidences are identical, exactly, not asymptotically. They are the nontrivial kernels and amplified boundary rows of the [critical tilt](https://github.com/mxym/math/commit/c8319147) and [selective Chen tradeoff](https://github.com/mxym/math/commit/778ba8e6).
3. Both masks preserve **every** original central prime-versus-composite incidence $P=p+m$ with $2\le\Omega(m)\le tH$, including all nonsquarefree composites. This is stronger than equality of count or of squarefree ranks alone. Neutral replacement primes are not required to have squarefree complements.

The constant $e$ is sharp as a transition constant in this information statement. For any fixed $t>e$ the conditions are impossible on a positive proportion of even $P$ in every sufficiently large dyadic interval: even equal global mask cardinality inside $C$ and equal counts for the low composite ranks, together with the on/off requirements, are impossible there. No assertion is made at $t=e$ or on every target; the full composite ledger (including nonsquarefrees) is essential to this upper obstruction.

This is an obstruction to determining the one target atom from the stated data. The masks depend on $P$, and need not share all analytic distribution properties of the *full* prime sequence. Neither fake primes nor a single alternative sequence working simultaneously at many targets is asserted. In particular this does not refute a signed estimate proved for ordinary primes with additional prime-specific input.

## 1. Disjoint vertices and the matching required

A true central Goldbach endpoint cannot be the $p$ of any genuine prime-versus-composite row: its complementary integer is prime. In a nontrivial $K_d$ above, $d\ge3$ gives $q\le2P/9$; in a $V_d$ row the two other prime slots are also $\le2P/9$. All prime divisors of $d\le D$ are outside $C$. Consequently removing central Goldbach endpoints never removes any such non-atom incidence. For an exact compensation we use *neutral* primes $b\in C$ for which
$$
  \Omega(P-b)>tH,\qquad g\mid(P-b)\ \hbox{for some prime }P^{.02}<g<P^{.03}.
$$
No such prime can occupy a $p$-slot of a retained kernel: the medium factor $g$ is too big for $d$, too small for either macro prime in $V_d$, and cannot equal the unique $q\gg P/D$ of $K_d$. It cannot be another slot by size. The high-rank inequality protects the entire low-rank composite ledger. It remains to supply enough neutral primes in each interval/residue cell.

If $p<P-p$ select the larger endpoint of each unordered central Goldbach pair, and select the diagonal $p=P/2$ once if it is prime. These are all distinct since the graph of different endpoints is a matching. Within each cell inject the selected endpoints there into distinct neutral primes there. Such injections can be made deterministic, for example by increasing order. Let off be all primes except the selected endpoints, and on all primes except the matched neutral primes. Their stated properties follow once the cell counts are proved. When $G(P)=0$ the masks may coincide.

## 2. Individual cell counts and a conditional large-deviation lower

Chebyshev's bound $\log W\ll cH$ gives $W\le L^{O_c(1)}$. Let $I$ be any interval of the partition and $b_0$ any reduced class mod $W$. Put $X_I=|I|/(\varphi(W)L)$. Nonreduced cells contain no central primes for $P$ large. If $P-b_0$ is nonunit modulo $W$, this cell has no central Goldbach endpoints because the possible common prime divisor is $\le cH$. In a unit/unit cell the total number of endpoints is
$$
 \ll X_I\,\mathfrak S(P)(W/\varphi(W))/L
    =X_I L^{-1+o(1)}\ \text{as an upper bound}.
 \tag{1}
$$
Indeed upper sieve $Wk+b_0$ and $P-Wk-b_0$ on an interval of length $|I|/W$. Outside $PW$ there are two forbidden roots; at primes dividing $P$ but not $W$ one; at primes dividing $W$ zero. Dimension-two upper sieving at a small fixed power of $|I|/W$ with level its square root gives $\ll (|I|/W)\mathfrak S(P)(W/\varphi(W))^2/L^2$: changing two roots to zero costs at most $(1-1/p)^{-2}(1+O(p^{-2}))$ outside $P$ (the prime 2 contributes a harmless constant). Elementary class remainders are divisor-bounded times the level and hence power smaller. The two displayed local products are $L^{o(1)}$ uniformly, by Mertens up to $L$ and the bound on the number of prime divisors of $P$ above $L$. This is the standard two-linear-form upper sieve; compare [*Opera de Cribro*](https://doi.org/10.1090/coll/057).

We show that in each unit cell the number of neutral primes is at least
$$
 X_I L^{-I(t)+o(1)},\qquad I(t)=t\log t-t+1,                             \tag{2}
$$
where the $o(1)$ is uniform in the cells (constant factors are included in the exponent). This gives the needed comparison since $I(t)<1$ for $1<t<e$.

Take $k=\lfloor tH\rfloor+1$. Let $\mathcal S$ be the primes in $[L^2,\exp(L/H^4)]$ not dividing $P W$; let $g\in(P^{.02},P^{.03})$ range over primes not dividing $P W$. The ranges are disjoint for large $P$. Count the primes $b\in I$, $b\equiv b_0\bmod W$ for which $g\mid P-b$ and *exactly* $k$ distinct members of $\mathcal S$ divide $P-b$. Such primes have the required strict rank even if some prime powers repeat.

For each $k$-element subset $S\subset\mathcal S$, let $d$ be its product. Require $d\mid P-b$ and exclude every prime in $\mathcal S\setminus S$ from $P-b$. Use the lower Bonferroni sum to odd order $J=2\lceil 6H\rceil+1$ on these excluded primes. Every resulting modulus is $Wg d f$, where $f$ is a product of at most $J$ distinct excluded primes, coprime to $Wgd$. It is $\le P^{.03+o(1)}$ since $(k+J)/H^4=o(1)$. The required residue is uniquely reduced by CRT. Each modulus has at most a bounded number of choices for $g$ and at most a fixed divisor power for choices of $d,f$; in particular there is **no** factorial-multiplicity coefficient in the level error. Ordinary prime BV, maximal for residue and interval endpoints, gives an absolute total error $O_E(PL^{-E})$ in a single cell for arbitrary $E$. Divisor weights are absorbed by Cauchy from unweighted BV with strengthened log accuracy, the trivial discrepancy $O(P/\varphi(q))$ here, and reciprocal divisor moments. Choose $E$ after $B,c,t$; the error is negligible relative to the rare right side of (2).

In the principal, each enforced $w\not\mid W$ contributes $a_w=1/(w-1)$. Uniformly $\sum_{w\in\mathcal S} a_w=H+O(\log H)$: prime Mertens at the two endpoints gives this, and $w\mid P$ above $L^2$ cost $O(1/L)$. The full probability none of $\mathcal S\setminus S$ occurs is $\prod_{w\notin S}(1-a_w)$, where only $w\in\mathcal S$ are meant; it is at least $\exp(-H-O(\log H))$. Its deficit in the odd lower truncation is at most $(H+O(\log H))^{J+1}/(J+1)!\le\exp(-10H)$ for all large $P$, by the elementary Bonferroni next term and Stirling. This is a **relative** $o(1)$ uniformly in every selected $S$, before summing them; no global fixed-density error is compared to the final rare class. The positive $g$-mass $\sum_g 1/(g-1)=\log(3/2)+o(1)$ is uniform in $P$.

The full principal after selecting $S$ contains the factor
$$
 \prod_{w\in\mathcal S}(1-a_w)
 \sum_{|S|=k}\prod_{w\in S}\frac{a_w}{1-a_w}
   =\exp[-H+O(\log H)]\,
           \frac{(H+O(\log H))^k}{k!}(1+o(1)).
$$
For the symmetric-sum equality, draw $k$ primes independently with probabilities proportional to $1/(w-2)$. The probability of any repeated draw is $\ll k^2\sum_{w>L^2}(w-2)^{-2}/(H+O(\log H))^2=o(1)$. A second use of Stirling gives the exponent $-I(t)H+o(H)$. A true row with exactly $k$ small marks has a unique such set $S$ and can have at most $50$ possible $g$ since $P-b<P$. Divide by this fixed bound, keeping a lower bound for distinct actual primes. Equations (1)–(2) now supply the injection. This proof is unconditional and does not assume a high-rank squarefree reservoir.

## 3. Why a larger transition constant cannot work

Fix $t>e$. Among central genuine primes the number with $\Omega(P-p)\ge tH$ is $o(\mathfrak S(P)P/L^2)$, uniformly in even $P$. Open one largest prime $q$ of $P-p=hq$; then $h$ is odd, $(h,P)=1$ outside the central prime diagonal, and if $k=\Omega(P-p)$ then $q\ge(P/3)^{1/k}$. The dimension-two prime-pair upper bound for $q,P-hq$ is $\ll (\mathfrak S(P)P/L^2)k^2/\varphi(h)$, exactly as in [the critical-rank estimate](https://github.com/mxym/math/commit/c8319147); allowing powers in $h$ is valid. Choose $e<v<\min(t,3)$ and then $v<v_1<\min(3,t\log v)$. For $k\ge tH$ apply $1\le v^{k-tH}$ and absorb $k^2v^{k-1}\ll_{v,v_1}v_1^{k-1}$. The odd-prime Euler product satisfies
$$
 \sum_{w\mid h\Rightarrow 3\le w\le P}
      \frac{v_1^{\Omega(h)}}{\varphi(h)}
  = \prod_{3\le w\le P}\left(1+\frac{w}{w-1}\frac{v_1}{w-v_1}\right)
  \ll_{v_1} L^{v_1}
$$
with prime product index $w$. Thus the normalized upper is $O(L^{v_1-t\log v})=o(1)$. Oddness matters for the $v_1<3$ repeated-factor moment.

On a positive proportion of even targets in each sufficiently large dyad, $G(P)\gg\mathfrak S(P)P/L^2$; this follows from the elementary dyadic pair area, the two-form upper and the bounded dyadic second moment of $\mathfrak S(P)$ ([critical tilt, Section 3](https://github.com/mxym/math/commit/c8319147)). On retains all $G(P)$ central prime endpoint vertices (an ordered pair corresponds to its first vertex). Off misses at least one per unordered pair, hence at least $G(P)/2$ of those vertices, with the diagonal counted once. Each other central prime is a vertex with a uniquely determined odd composite complement. Equality of low-rank counts, even without equality incidence by incidence, makes the mask cardinalities on those vertices equal: all their prime factors are outside the central interval and unmasked. Total central cardinality equality would then require at least $G(P)/2$ genuine high-rank vertices to balance the deficit, whereas the preceding uniform upper is $o(\mathfrak S(P)P/L^2)$. This contradiction establishes the claimed sharp constant off the endpoint.

This finite-target information obstruction is distinct from the classical parity obstruction for analytic sieve axioms; see [Tao’s discussion of the latter](https://terrytao.wordpress.com/2014/11/21/a-general-parity-problem-obstruction/comment-page-1/) and [Friedlander–Iwaniec, *Exceptional zeros, sieve parity, Goldbach*](https://msp.org/ent/2022/1-1/ent-v1-n1-p02-p.pdf). The masks above are only asserted to preserve the data stated in the theorem.
