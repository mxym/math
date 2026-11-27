# A two-level walk construction for local almost-independent hashing

## 1. Model and theorem

Write all logarithms as base two. A uniform key consists of \(\ell\)
words of exactly \(w\) bits. Evaluation on one \(n\)-bit input
may adaptively probe the key, reading at most \(t\) words on every input
and key. A family is \(\varepsilon\)-almost \(k\)-wise independent
if the statistical distance of transcripts obtained from its
random-key function and a uniform random function is at most
\(\varepsilon\) for every oracle algorithm making at most \(k\)
adaptive queries. It suffices to treat distinct queries, since
repeats can be answered from a cache in both experiments.

**Main theorem.** At word size \(w=n\), for \(n\ge2\) and
\(n\le k\le\operatorname{poly}(n)\), an explicit
\(2^{-n}\)-almost \(k\)-wise independent family uses \(O(nk)\) seed
words and \(O(\sqrt{n/\log n})\) probes per evaluation. This is the
optimal locality order when polynomial-size keys are allowed. It
does not assert the same bound for linear-size keys.

We prove the main theorem by describing one construction with
an auxiliary parameter. Its wider guarantee is also recorded.

For integers \(n\ge1\), \(1\le k\le2^n\), \(1\le w\le n^2\)
and \(1\le u\le\lceil\log(2n)\rceil\), put
\[
 b=\min\{w,n,\lfloor\sqrt{wu}\rfloor\}.
\]
We construct such a family with \(n\)-bit output,
\(\varepsilon=2^{-n}\), key length \(O(2^u\lceil kn/w\rceil)\)
words and locality \(O(\lceil n/b\rceil)\) words. Evaluation time
(including public arithmetic and matrix construction) is polynomial
in \(n,t,w,\log\ell\). All constants are absolute.
The word count is equivalently
\(O(\max\{1,n/w,n/\sqrt{wu}\})\) because rounding the square root
down loses at most a factor two.

If \(k\le w/b\), use a uniform degree-at-most-\((k-1)\) polynomial
over \(\mathbb F_{2^n}\), identifying all \(n\)-bit inputs with field
elements. Vandermonde interpolation gives perfect independence. The
entire \(kn\)-bit coefficient list reads \(\lceil kn/w\rceil\le
\lceil n/b\rceil\) words. Also \(k\le w/b\le n^2\) in this branch,
so evaluating the polynomial is polynomial time in the stated
parameters. The rest of the proof treats \(k>w/b\).

## 2. A spectral estimate for fixed sets along a walk

For each power of four \(G=g^2\), use the
Margulis–Gabber–Galil 8-regular undirected multigraph on
\((\mathbb Z/g\mathbb Z)^2\), with neighbors
\[
 (x\pm2y,y),\quad (x\pm(2y+1),y),\quad
 (x,y\pm2x),\quad(x,y\pm(2x+1)).
\]
Loops and multiplicity are retained. The normalized adjacency has
second eigenvalue at most \(5\sqrt2/8\). Lazify it by holding
with probability \(1/2\), so a step uses four uniform bits
(one holding bit and three bits for the original move).
The lazy transition \(P_0\) then has all eigenvalues
nonnegative and its nonconstant operator norm is at most
\((1+5\sqrt2/8)/2<31/32\).
A single-vertex graph is allowed, with nonconstant norm zero.
Moreover \((31/32)^{32}<1/2\), for example by the binomial lower
bound on the reciprocal. These transitions are evaluated directly
on the two residue coordinates. If the vertex count is \(2^{2a}\),
a uniform starting state takes exactly \(2a\) unbiased bits.

Let \(P\) be a symmetric transition with uniform stationary
measure and nonconstant norm at most \(\lambda<1\). A stationary
walk observed at any prescribed \(r\) distinct times hits
prescribed sets, each of measure at most \(\mu\), at all those
times with probability at most
\[
                    \mu(\mu+\lambda)^{r-1}. \tag{1}
\]
To see this, use the uniform inner product, \(J\) the projection
onto constants, and \(M_i\) multiplication by the indicator of
the \(i\)th prescribed set. For a gap \(a\ge1\),
\[
 \|M_i P^a M_{i+1}\|
 \le \|M_i J M_{i+1}\|+\|P^a-J\|
 \le\sqrt{\mu_i\mu_{i+1}}+\lambda^a
 \le\mu+\lambda.
\]
The two end indicators have norms at most \(\sqrt\mu\).
The joint probability is the inner product formed by these end
indicators and the products of intervening operators. This proves
(1), including \(r=1\) directly. In particular, among \(D\)
prescribed sets at \(D\) times, a union bound for at least
\(r=\lceil D/8\rceil\) hits gives
\[
 \Pr[\#\text{ hits}\ge r]\le
              \binom Dr(\mu+\lambda)^r
             \le (8e(\mu+\lambda))^r. \tag{2}
\]
The sets must be fixed before sampling the walk. We will not apply
(1) to sets chosen adaptively from the walk history.

## 3. One stationary state's selection rule

Write \(g\) for the largest power of four at most \(w/b\).
In each data word use \(b\) disjoint stripes, each consisting of
\(g\) consecutive bit positions, leaving any surplus bits unused.
Thus \(b g\le w\) and \(g>w/(4b)\).
Set \(R=\lceil g/1024\rceil\); note \(1\le R\le g<k\).
Let \(B\) be the least power of two with
\[
                         BR\ge 2^{u+16}k .
\]
Each chunk consists of \(B\) independently uniform data words.

To select exactly one bit in each of the \(b\) stripes of a selected
word, start a uniform lazy walk on the \(g\) positions within a stripe.
Record the initial position for stripe one, then the position after
320 more lazy moves for each successive stripe. Different stripes
ensure that every output is distinct, even if the walk revisits
an intra-stripe position. The selection uses exactly
\[
                 L_{\mathrm{in}}=\log(g)+1280(b-1)
\]
random bits, and its transition between stripes has
\(\lambda\le2^{-10}\). For \(g=1\), the moves may equivalently be
ignored; the same bit count is harmless.

Define a field \(K=\mathbb F_{2^a}\), where
\[
 a=\max\{\lceil\log(nk)\rceil+14+\lceil b/4096\rceil,
                        \log B,\ L_{\mathrm{in}}\}.
\]
A uniform selector state has one independent \(K\)-element \(z\),
and the two independently uniform degree-at-most-\(R\) polynomials
\(F,G\in K[X]\), stored by their coefficients. These are
\((2R+3)a\) bits. Any needed padding to even bit length is ignored
when parsing. For input \(x\), form the polynomial whose coefficient
vector is the input split into \(a\)-bit pieces with fixed zero padding;
write \(h_z(x)\in K\) for its evaluation at \(z\). Select the
word index from the first \(\log B\) bits of \(F(h_z(x))\);
use the first \(L_{\mathrm{in}}\) bits of \(G(h_z(x))\) as the
inner walk seed. This is the same rule in every chunk, with indices
relative to the chunk.

Fix a list of at most \(k\) distinct inputs and a target among
them. For a uniform selector state, call it bad if more than \(b/8\)
of the target's selected locations in this chunk are also selected
by the other inputs' evaluations. We now bound the stationary
measure \(\mu\) of this set, without conditioning on any other chunk.

**Digest.** The probability that the target digest coincides with
a digest of another input is at most \(nk/2^a\), by the polynomial
root bound and union bound. This is at most \(2^{-14-b/4096}\).
No condition is imposed on collisions *among* those other inputs.

**Word.** Fix the digest key \(z\) so that the target digest is
distinct from the others. Count the number of *distinct* other
digests mapping to the target word. A uniform degree-\(R\)
polynomial evaluates independently uniformly on any \(R+1\)
distinct field elements, by the Vandermonde rank argument, so
the probability that some \(R\) of those digests all map to the
target word is at most
\[
  \binom{k-1}R B^{-R}\le(ek/(BR))^R\le 2^{-(u+14)R}
                                     \le2^{-14-b/4096}.
\]
For the last inequality note \(R\ge1\) and
\(uR\ge u g/1024>uw/(4096b)\ge b/4096\) since \(b^2\le wu\).
Repeated occurrences of a digest have exactly the same word
and inner seed; counting distinct digests is essential.

**Inside the word.** Fix \(z,F\) satisfying the preceding good
events. Fewer than \(R\) distinct other digests select the target
word. If there are zero then the inner step cannot fail. Otherwise
fix the \(G\)-values on those other digests. The target's \(G\)-value
is still uniform because there are at most \(R\) distinct points total
in this conditioning and the polynomial gives \(R+1\)-wise independence.
In each stripe there are at most \(R-1\) previously selected positions;
these are now fixed sets of measure \((R-1)/g<2^{-10}\).
By (2) on the inner walk, the probability of more than \(b/8\)
collisions is at most \((8e\,2^{-9})^{\lceil b/8\rceil}\le2^{-b/2}\).
If there are other digests in the word then \(R\ge2\), hence
\(g>1024\); since \(b\ge\lfloor\sqrt{w}\rfloor\) we have
\(g\le w/b<(b+1)^2/b\le b+3\), so \(b>1021\).
In that case \(2^{-b/2}\le2^{-14-b/4096}\).
Thus the whole bad-set measure satisfies
\[
                       \mu\le3\cdot2^{-14-b/4096}
                                 <2^{-12-b/4096}. \tag{3}
\]

## 4. Share selector randomness across chunks

Round \((2R+3)a\) up to the nearest even integer \(S\).
The outer walk is on \(2^S\) vertices, with each state parsed as
a selector and possible ignored padding as above. The key stores
the uniform \(S\)-bit start and independent groups of
\(4\tau\) edge bits per transition, where
\[
                       \tau=32(10+\lceil b/4096\rceil).
\]
Its powered transition has \(\lambda\le2^{-10-b/4096}\).
At each time the state is uniform; the absolute-position selector
state itself need not be stored. Let \(D\) be the number of chunks,
to be chosen in §5. In a fixed input list, the bad set in §3 is
fixed in advance (indeed the same set is used at every chunk).
The states are dependent and we do not condition on earlier states
to assert (3). Instead, (2) with this powered outer walk and
\(\mu+\lambda<2^{-9-b/4096}\) gives
\[
 \Pr[\text{at least }\lceil D/8\rceil\text{ bad chunks}]
           \le 2^{-bD/32768}. \tag{4}
\]
Indeed \(8e<2^5\), and the exponent includes at least
\(b\lceil D/8\rceil/4096\). If that many bad chunks do not occur,
the target shares fewer than \(Db/4\) selected bits with the other
inputs: count at most \(b\) in each of fewer than \(D/8\) bad
chunks and at most \(b/8\) in each remaining chunk.

## 5. Output, adaptive queries, and accounting

Choose a public binary \(n\)-row matrix \(A_0\) of \(L_0=O(n)\)
columns with minimum nonzero row-combination weight at least
\(7L_0/16\). For example, the explicit constant-error small-bias
construction of Ta-Shma, Theorem 1.1 at bias \(1/8\), supplies the
columns; each nonzero combination has weight at least \((1-1/8)L_0/2\).

Take \(D\) to be the smallest integer such that
\[
             Db\ge \max\{4L_0,32768(n+\lceil\log k\rceil)\}.
\]
Let \(L=Db\), and form \(A\) by appending as many full copies of
\(A_0\) as fit, followed by zero columns. Its nonzero row-combination
weight is at least \((7/16)(L-L_0)\ge21L/64>L/4\).
Therefore any \(\ge3L/4\) of its columns span the \(n\) output
coordinates. Evaluation concatenates the selected data bits in
chunk-then-stripe order and multiplies the resulting column vector
by \(A\). The data words are independent of the outer walk.
For every fixed \(j\)-tuple of distinct queries with \(j\le k\),
(4) and a union bound show that, except with probability \(2^{-n}\)
over the selector key, every query has \(\ge3L/4\) of its data
positions private to that query. When that holds, condition on
all data bits other than the private positions. The private
sets are disjoint across queries; on each private set the
corresponding submatrix of \(A\) maps uniform bits to a uniform
\(n\)-bit output. Therefore the joint outputs are exactly independent
and uniform.

For adaptivity, augment both real and ideal transcripts by the
complete selector key, sampling it with the same law in the ideal
experiment, independently of the random function. Fix the oracle
algorithm's independent random coins (or average the conditional
argument). For any consistent transcript \(\tau\) with \(j\)
distinct queries, the listed outputs determine the algorithm's
queries and stopping decision. If the augmented transcript is good
in the preceding sense for *its listed inputs and selector key*,
its mass in the real and ideal experiments is identical:
the probability of its ordered list of outputs is exactly
\(2^{-nj}\) for that selector key in both. In the ideal
experiment the query list is independent of the selector key, so
the bad part has mass at most
\(k\,2^{-bD/32768}\le2^{-n}\) by conditioning on the ideal list.
Since the masses are equal on the good part, the total variation
distance is at most the mass of the bad part. Removing the selector
key by projection cannot increase it. This argument does not
pretend that the real adaptively chosen list is independent of
the key.

For accounting, \(\log k\le n\), \(b\le n\), and \(D=O(n/b)\).
Because \(R\ge g/1024>w/(4096b)\) and \(R\le g\le w/b\),
\(B=O(2^u k b/w)\); its multiplicative constants are fixed.
The data words number \(DB=O(2^u kn/w)\). We have
\(\log B=O(1+u+\log k)\), \(L_{\mathrm{in}}=O(b)\)
(since \(g<b+3\)), and \(a=O(b+\log(nk)+1)\).
Using \(R=O(w/b)\) yields
\[
            S/w=O(1+(\log(nk)+1)/b)=O(n/b).
\]
The \((D-1)4\tau\) transition bits are \(O(Db)\) bits,
and divide into \(O(n/b)\) words since \(b\le w\).
Pack initial state, transition labels, and unused padding bits
(which are still uniform) contiguously into whole seed words before
the data array. Each evaluation reads the whole selector portion,
then one addressed data word per chunk; its total is \(O(n/b)\)
word probes. This selector storage is dominated by the data bound
in the case \(k>w/b\); bit rounding adds at most one word.
The evaluated states are recomputed successively, not stored for
all chunks in the key.

Finite fields of the required binary degrees can be constructed in
deterministic polynomial time (Shoup's fixed-characteristic result).
Computing a neighbor means a few additions modulo a power of two;
field evaluations have degree at most \(\max\{n,R\}\), and
the public matrix has \(L=O(n)\) columns. Arithmetic on chunk
offsets uses \(O(\log\ell)\) bits. Neither data array size nor the
number of previous queries is enumerated to evaluate one input.

## 6. The two key-length regimes

For \(u=1\), \(b=\lfloor\sqrt w\rfloor\) because \(w\le n^2\).
This is one construction at all word sizes, with linear-size key
and the former large-word locality bound. It answers the separate
all-word-size construction question of the source paper.

For the main theorem take \(w=n\), \(u=\lceil\log(2n)\rceil\).
Then \(2^u=O(n)\), \(b=\Theta(\sqrt{n\log n})\) and the key/probe
claims follow. More precisely, \(R=O(n/b)\) and for polynomial
\(k\), \(a=O(b+\log(nk))=O(b)\), so the starting state has
\(S=O(n)\) bits. Separately, \((D-1)4\tau=O((n/b)b)=O(n)\)
bits of transitions are stored and read. These two random portions
together occupy \(O(1)\) words at \(w=n\), in addition to the
\(D\) data probes. The integer caps on \(b\) cover all finite small
\(n\ge2\). If \(k>2^n\) at such an \(n\), it can be replaced by
\(2^n\), since there can be no more distinct queries.

For the matching lower bound, and its supplementary extension,
suppose \(n\le k\le\operatorname{poly}(n)\) and \(n\to\infty\).
For \(u=\lceil\log(2n)\rceil\) the above key is polynomial and
locality is \(O(\max\{1,n/w,n/\sqrt{w\log n}\})\). For any
competing family with a fixed polynomial key-length bound, two
lower bounds match this order. First, any single fixed input's output
is computed by a decision tree of depth \(t\) with at most \(2^w\)
possible responses to each probe. Its image has size at most
\(2^{tw}\); if \(tw<n\), its distance to uniform is at least
\(1-2^{tw-n}\ge1/2>2^{-n}\) for \(n\ge2\).
Thus \(t\ge\lceil n/w\rceil\).

If \(\ell=1\), the support of the whole \(k\)-tuple on any fixed
distinct inputs has size at most \(2^w\). By the same support
argument \(w\ge kn\) is necessary; under \(k\ge n,w\le n^2\)
this is only \(w=n^2,k=n\), where the claimed order is already 1.
Thus consider \(\ell\ge2\).

Second, Dodis–Lovett–Wichs Theorem 5.1 at output length \(n\)
and error \(2^{-n}\) states, when \(k>tw/n+1\),
\[
           t=\Omega\!\left(\min\{n/\log\ell,
                                 n/\sqrt{w\log\ell}\}\right).
\]
As \(\ell\le\operatorname{poly}(n)\), for \(w\ge\log n\)
this implies \(\Omega(n/\sqrt{w\log n})\).
If instead \(k\le tw/n+1\), then \(t\ge(k-1)n/w\), also at
least this order since \(k\ge n\) and \(w\le n^2\).
For \(w<\log n\) the one-query bound is already stronger.
Taking all bounds together proves the matching order in the
polynomial-key regime, with lower-bound constants allowed to
depend on the fixed polynomial degree. The improved locality
for \(u>1\) has a distinct key-size cost and does not prove the
same improvement at \(O(\lceil kn/w\rceil)\) key size.
