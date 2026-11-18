# A shared-coordinate improvement to a lower bound for the Fourier entropy–influence constant

**Draft research note.** 18 November 2026. The construction below gives a lower bound strictly larger than 6.52185115673538 for the uniform Boolean Fourier entropy–influence constant, even restricted to monotone functions. This is a small quantitative advance over the 6.521845710923046575… construction of Numaro. The increase in the amplified witness ratio is about 0.000005446. In fact a finite monotone function also clears the stated threshold (depth 48 below). It does not show finiteness or infinitude of the constant and does not settle the Friedgut–Kalai conjecture. There is no claim that the modified construction is optimal.

## Setup and antecedents

All coordinates are independent equiprobable signs. We encode a graph edge being present, and logic true, by sign −1; this flips the order of input and output together, preserving ordinary sign monotonicity. Write
$$
 H(f)=\sum_S \eta(\widehat f(S)^2),\quad \eta(u)=-u\log_2 u,\quad
 I(f)=\sum_S|S|\widehat f(S)^2,\qquad C=\sup_{I(f)>0} H(f)/I(f).
$$
We set $\eta(0)=0$, and also use the entropy sum for real-valued, non-unit-norm Fourier profiles. The Friedgut–Kalai conjecture asks whether $C<\infty$. For a balanced seed $f$ with $I(f)>1$, the **amplified witness ratio** is $R(f)=H(f)/(I(f)-1)$. One must not confuse this with the actual ratio of the finite seed. For ordinary disjoint composition of copies of a balanced seed, the Fourier probability law is obtained by sampling the outer Fourier set, then independently sampling a nonempty inner Fourier set for each selected input. The union identifies all these selections because the blocks are disjoint. Thus for the depth-$d$ iterates, $I_d=I(f)^d$, $H_d=H(f)(1+I(f)+\cdots+I(f)^{d-1})$. This proves $C\ge R(f)$ by a limit; monotonicity is preserved.

Sources: [O'Donnell–Wright–Zhou (2011), conjecture statement](https://www.cs.cmu.edu/~odonnell/papers/fei.pdf); [O'Donnell–Tan (2013), disjoint composition](https://arxiv.org/abs/1304.1347); [Hod (2017), lexicographic lower bounds](https://arxiv.org/abs/1711.00762); [public constants ledger with history and prior verification](https://teorth.github.io/optimizationproblems/constants/71a.html); [Numaro's n=18 seed, built on Mosaic's seeds](https://numaro.tech/research/fourier-entropy-influence-2026/). The proposal here is the edge-conditioned, **overlapping** substitution below, not the original seed, its amplification rule, or the observation that the conjecture is open.

## The reference seed in graph form

Write the nine core bits as the edges of the complete bipartite graph with three vertices on each side. Given the selected graph:
* If it contains a perfect matching, output true.
* If it has an isolated vertex, output false.
* Otherwise it belongs to a unique two-point chart associated with a center edge $e=(i,j)$. Here the four other edges incident to $i$ or $j$ are present and the four edges incident to neither are absent. The center bit $s_e$ is free. On this chart the reference seed outputs its private auxiliary bit $y_e$.

Indeed, the first two cases are disjoint. If neither occurs, Hall's theorem supplies a pair of left vertices with the same single right neighbor (a single-vertex obstruction and a three-vertex obstruction would respectively leave a left or right vertex isolated). Each of the other two right vertices must be connected to the remaining left vertex. The four arms and the four absent corner edges follow. The central left and right vertices are unique as each is the only vertex on its side of degree at least two. Each chart has probability $h=2^{-8}$. The number of perfect-matching cases and the number with an isolate are each 247, as can also be checked by enumeration of all 512 graphs.

Call this function $B$. It is monotone: a proper upward exit from a chart through a previously absent edge creates a perfect matching, while a proper downward exit by removing an arm isolates its degree-one endpoint. Monotonicity within a chart is immediate. The 18-bit truth-table SHA-256 agrees exactly with the prior public certificate, after restoring the prior order of the auxiliary bits. Thus the graph description is not an unrelated seed with the same statistic.

Define $u(x)$ to be the signed fixed output off the nine charts and zero on them; define $v(x)=s_e$ on chart $e$ and zero off their union. Set $q_t=u+tv$, and denote its core entropy by $L(t)=\sum_{S\subseteq[9]}\eta(\widehat{q_t}(S)^2)$. Finite Walsh summation gives the following 13 triples $(a,b,m)$: the absolute values of the normalized coefficients, with multiplicity $m$, are $|a+bt|/256$.
    
    (0,0,46) (1,1,108) (1,9,1) (2,-6,12) (2,2,72)
    (3,-5,18) (4,4,18) (5,-3,36) (8,0,72)
    (9,1,72) (19,3,12) (22,-2,36) (57,1,9)

The included checker derives, rather than assumes, this table by exact summation over all graphs. In particular every core singleton of $B$ has coefficient $b_0=57/256$ (direct singleton sum, or row-column symmetry with a single sum); each auxiliary singleton has coefficient $h$, its chart probability. The seed is balanced, $I_0=9(b_0+h)=261/128$, $H_0=L(0)+9h\cdot16$. The influence identity uses that for monotone signs, coordinate influence equals the corresponding singleton coefficient, by conditioning on all other inputs.

## Shared-coordinate graft

Let $g(s,w)$ be a balanced monotone Boolean gate with marked input $s$, singleton coefficient $t=\widehat g(\{s\})$. Use nine identical copies with pairwise disjoint private bits $w_e$. Keep the fixed output off the charts but output $g(s_e,w_e)$ on chart $e$. Crucially, $s_e$ is the *same* core coordinate appearing in that chart, not a fresh copy. Denote this function by $F$. It is monotone by the same upward and downward exit argument as for $B$, and is balanced: integrating over the private inputs gives exactly $q_t$, of mean zero.

The all-core part of its Walsh expansion is $q_t$. Consider now a Fourier character of $g$ involving at least one private coordinate (it may or may not contain $s$). Multiplying it by its chart indicator, the product of eight one-bit indicators independent of $s$, creates $2^8$ Fourier coefficients each having magnitude $h|\widehat g(S)|$. There are no collisions: different charts have disjoint marked private blocks; within a chart the nonempty private subset, the presence of $s$, and the subset of the other eight core variables recover the original choices. The two coefficients of $g$ excluded are the constant coefficient zero and the $s$-singleton of weight $t^2$. Hence
$$
 H(F)=L(t)+9h\{H(g)-\eta(t^2)+16(1-t^2)\}.
$$
For any core input the active-edge correction to its singleton is exactly $ht$: only its own chart has this coordinate free, and on any other chart the mean of the free sign is zero. For a private input the singleton is its gate singleton times $h$. Summing and using monotonicity yields
$$
 b(F):=\widehat F(\{\text{any one core coordinate}\})=b_0+ht,\qquad I(F)= I_0+9h(I(g)-1).
$$
Taking $g=B$ with one auxiliary as marked input already gives a 162-variable seed with $6.5218500836586124<R(F)<6.5218500836586125$.

## Four-link chain and iteration

Given a balanced monotone seed $A$ with a marked core input of singleton coefficient $b$, make a four-link chain by substituting the next copy into that marked input, using fresh bits throughout, the innermost marked bit being exposed. By the disjoint Fourier sampling rule (or expanding in the marked variable), replacing a single outer bit by $A$ adds the outer bit's influence times $H(A)$ to the entropy, and its influence times $I(A)-1$ to total influence. The new marked singleton is the product of the two marked singletons. Since $A$ is monotone, each mark's influence is indeed its singleton coefficient. Accordingly the gate has
$$
 t=b^4,\quad K=1+b+b^2+b^3,\quad H(g)=K H(A),\quad I(g)=1+K(I(A)-1).
$$
With $N$ inputs in $A$, the chain has $4N-3$, and the subsequent nine-chart graft consumes $9+9(4N-4)=36N-27$ inputs including the nine common core coordinates.

First put $A=B$: this produces $N=621$, $I=1146757521141/549755813888$, and
$$
 6.5218509316620414<R<6.5218509316620415.
$$
Now use this new seed as $A$ once more, with its just-computed $b=b_0+hb_0^4$; the graft template is still the original nine-chart **outer** core. This yields $N=22{,}329$ and
$$
 6.5218511567353856<R<6.5218511567353857.
$$
In particular $C>6.52185115673538$. All comparisons are rational certificates. No enumeration of a 22,329-bit truth table is claimed or needed.

## An actual finite witness

The final seed itself is **not** claimed to have actual $H/I$ above 6.52. Let $I_*$ be its influence and $R_*$ its amplified ratio. Numerically $I_*\approx2.08805523$; the certificate obtains it exactly. For the depth-$d$ ordinary unshared self-composition of this seed, the first identity in the setup gives the actual ratio
$$
  H_d/I_d=R_*(1-I_*^{-d}).
$$
The certified rational lower endpoint $L=6.5218511567353856$ is strictly below $R_*$. The checker uses exact rational exponentiation to verify both $L(1-I_*^{-20})>6.5218457109230466$ (above the previous seed's upper endpoint) and $L(1-I_*^{-48})>6.52185115673538$. Thus an explicitly defined finite balanced monotone function on $22329^{48}$ bits attains the last strict inequality. It is specified recursively, not enumerated.

## Why an increase exists

Against an independent graft at a fixed gate entropy, the exact entropy change is $D(t)=L(t)-L(0)-9h\{16t^2+\eta(t^2)\}$; the total influence does not change. The last two corrections are $o(t)$. Since $u$ and $v$ have disjoint supports, $\sum m a b=0$. The finite coefficient table gives
$$
 L'(0)=2^{-14}\log_2\!\frac{2^{864}5^{540}11^{1584}}{3^{1539}19^{1197}}>0.
$$
The sign is just an integer comparison. Consequently arbitrarily weak positive couplings improve entropy to first order, not by numerical rounding. Independent chains supply marks tending to zero while retaining exactly the reference amplified ratio.

## Reproduction and limits

Run `python3 -B -O verify.py` with no packages and no network. It verifies the two finite-depth inequalities, the baseline truth table hash, all coordinate monotonicities, the core Walsh table by direct summation, and every interval comparison. It bounds $\log$ by rational partial sums of $2\operatorname{atanh}((x-1)/(x+1))$ on $1\le x\le2$, with a positive geometric-tail bound. The rational endpoints are rounded outward only for display. No approximate Fourier transform or platform logarithm is trusted. Compare the earlier interval, whose slightly larger endpoint is still below 6.5218457109230466.

This improves the identified public reference, not the qualitative conjecture. The source ledger, known results on special classes, and a targeted search were checked; this is not a guarantee of global priority or of the absence of unpublished improvements.

A scope check on 18 November 2026 included [Shmalo, shared-data selectors and threshold-function upper bounds](https://arxiv.org/abs/2610.16069) and [Paraashar–Saurabh, approximation-based entropy upper bounds](https://arxiv.org/abs/2611.06451); neither states this numerical lower bound. The public ledger's associated issue search for “71a” or “Fourier Entropy” returned the n=17 and n=18 lower-bound PRs and a README update, with no later matching lower-bound PR found in those queries. Prior work on shared selectors is relevant conceptual background; we do not claim inventing selector decompositions.


### Independent calculation and provenance

As a cross-check, download Numaro's [original n=18 JSON artifact](https://numaro.tech/assets/research/fei/fei_c71_n18_artifact.json) and run:

```sh
python3 -B crosscheck.py /path/to/fei_c71_n18_artifact.json
```

The external file is not needed by the main certificate. The cross-check pins the historical truth-table SHA-256 and independently identifies the 9 two-point charts from the 512 auxiliary sections. It applies a fast integer Walsh transform to the entire old truth table without using the graph identification or the 13-row histogram. With $J(q)=\sum_S |S|\widehat q(S)^2$, it finds exactly $J(u+tv)=477/256+(45/256)t^2$. Each chart's private part contributes $h[I(g)-t^2+4(1-t^2)]$ to the full first moment; this also checks the total influence without summing monotone singletons. At 75-decimal-digit precision this separate implementation gives $R_*=6.5218511567353856387932146744763315074\ldots$. The rigorous rounding certificate is `verify.py`, not the corroborating decimal evaluation.

**AI assistance and review status.** The overlapping construction, proof exposition, programs and a separately implemented internal replay were developed and checked with AI assistance. Internal AI-assisted checks are not independent human peer review or a Lean formalization. The lower bound is the only claim: no upper bound, no resolution of the conjecture, no optimality or historical-priority claim. The cited public ledger and original artifacts establish the comparator and the scope of the search, not the absence of all other work.
