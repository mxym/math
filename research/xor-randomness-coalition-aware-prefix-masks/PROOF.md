# One-bit private XOR with coalition-aware prefix masks

## 1. Model and claims

There are \(n\ge2\) parties, one private input bit \(x_i\) each,
and perfectly private authenticated point-to-point channels.
All parties receive \(X=\bigoplus_i x_i\). A static semi-honest
coalition \(C\) of at most \(t\) parties follows the protocol
and sees its inputs, its local random tapes, its incoming and
outgoing messages and its local states. Perfect privacy means the
law of this view is identical for any two inputs with the same
\(x_C\) and \(X\). This is equivalent to perfect simulation here:
a simulator can sample the protocol on a fixed completion of
\(x_C\) with parity \(X\) and retain the coalition view. Such a
completion exists because \(t<n\). No trusted dealer or setup
randomness is available. Fixed public protocol descriptions are
not random tapes used during execution.

Put \(\ell=\lceil\log_2 n\rceil\) and \(N=n-t-1\).

* **Balanced-tree existence.** For \(1\le t<n\) there is a
  protocol with exactly \(t\) designated local random sources,
  logarithmically many rounds, and at most
  \(t[t+\min(N,8t+2\ell+2)]\) fair coin tosses.
* **Path existence.** The same holds with
  \(t[t+\min(N,2t+2\ell+2)]\) tosses and a path schedule, with
  linear rather than logarithmic round count.
* **Explicit fixed-tree protocol.** For any public fixed full binary
  tree on the leaves, there is a polynomial-time constructible
  protocol in the same model with arbitrary fixed \(t+1\) sources
  and at most
  \((t+1)\min(n-1,\ell\min(8t,n-1))\) fair tosses.
  Its round count is depth plus a constant, so a balanced tree
  is sufficient for logarithmic rounds. In the two-block tree it
  also works with exactly \(t\) sources and the same bound per source.
  This explicit construction
  does not claim a seed of length \(O(t\log(n/t))\) for all \(t\).

The balanced-tree and path existence results share the same rank
argument below. They do not assert that the matrices passing the
finite rank conditions can be found in polynomial time.

## 2. Prefix-mask protocol and privacy criterion

Fix a public rooted binary aggregation tree and number the leaves
\(1,\ldots,n\) according to its left-to-right depth-first order.
The leaves descended from a given node form one interval:
each subtree is fully traversed before the traversal exits it.
Write its interval as \((a,b]=\{a+1,\ldots,b\}\).
Assign one internal node to each of \(n-1\) different participants;
each participant also owns its own leaf. The root owner finally
sends the total to all. A path variant instead has party \(i\)
receive the running prefix ending at \(i-1\), incorporate its
own masked input, and send the prefix ending at \(i\) to the next
party (the last party distributes the total).

Every designated source \(d\) has an independent private tape
determining prefix bits \(s^{(d)}_0= s^{(d)}_n=0\) and
\(s^{(d)}_1,\ldots,s^{(d)}_{n-1}\). In a single setup round it
privately sends to party \(i\) the bit
\[
 r^{(d)}_i=s^{(d)}_{i-1}\oplus s^{(d)}_i.
\]
For its own recipient position the source can use this bit locally.
No raw prefix bits are sent as setup messages. Party \(i\) masks
its leaf by XORing every received bit \(r^{(d)}_i\) into \(x_i\),
then aggregates masked values along the fixed tree. Summation of
a node on \((a,b]\) is exactly
\[
 Y(a,b)=\bigoplus_{i=a+1}^b x_i\ \oplus         \bigoplus_d(s^{(d)}_a\oplus s^{(d)}_b).                 \tag{1}
\]
In particular all masks cancel at the root. Each internal owner
receives the two child values and sends the XOR upward, except
for the root broadcast. Every party otherwise sees only its own
leaf value and its setup messages. Its local state is determined
by these incident messages, local tape and input. Thus for a
corrupted party there are at most four relevant intervals:
the leaf, its assigned internal node (if any), and the two
children of that node. The final broadcast reveals only the
already fixed output, adding no variable endpoint. In the path
variant the relevant prefix endpoints for party \(i\) are
\(i-1,i\), also covering its local leaf and both path messages.

Let \(E(C)\subseteq\{1,\ldots,n-1\}\) comprise the endpoints
of these coalition intervals, including those of the leaf of
every corrupted setup recipient. Endpoints 0 and \(n\) are
constants and can be removed. **Sufficient condition:** if at
least one honest source has completely uniform independent
prefix bits on \(E(C)\), the protocol is perfectly private for
that coalition. The choice of good source may depend on the
fixed coalition and is not used by the actual execution.

To prove the condition, fix all other sources' tapes, even
those of other honest sources. These tapes are independent of
the good source and of the inputs. For two inputs \(x,x'\) as
in the definition, put
\[
 \Delta_j=\bigoplus_{i=1}^{j}(x_i\oplus x'_i),\qquad
 \Delta_0=\Delta_n=0.
\]
Translate the good source's marginal prefix vector on
\(E(C)\) by \((\Delta_j)_{j\in E(C)}\). The marginal distribution
is unchanged because it is uniform. In (1) the change of the
ordinary input XOR on \((a,b]\) is \(\Delta_a\oplus\Delta_b\)
and cancels the change of that source's mask. For every
corrupted recipient \(i\), its *individual* setup bit
\(r_i^{(d)}\) from the good source also stays the same:
\(\Delta_{i-1}\oplus\Delta_i=x_i\oplus x'_i=0\).
Any setup message sent by a corrupted source is determined by
one of the tapes already fixed; any other visible setup message
is also determined by those tapes. The good source's tape is
not part of the coalition view. No input-dependent message
other than those enumerated here crosses to the coalition.
Thus the translation leaves the entire conditional view law
unchanged, including individually visible setup contributions.
Averaging over the conditioned tapes proves the claim.
Uniformity of just the XOR of different sources would not have
provided this argument.

## 3. Choosing the public matrices

For the balanced construction take exactly parties \(1,\ldots,t\)
as sources. The top node joins two contiguous balanced trees:
the prefix block of these \(t\) leaves and the remaining
\(n-t\) leaves. The \(t-1\) internal nodes in the source
subtree and the top node are assigned bijectively to the \(t\)
sources; the remaining \(n-t-1\) internal nodes are mapped
injectively to the non-sources. Thus every interval any source
sees has endpoints in \(\{0,1,\ldots,t,n\}\). The only whole
outside interval a corrupted source may see is the right child
of the top node, with endpoints \(t,n\). Each corrupted
non-source contributes at most four intervals, hence at most
eight exterior prefix indices. For the path, keep the first
\(t\) parties as sources; their endpoints are in \([0,t]\),
and each corrupted non-source contributes at most two indices.
Use \(b=8\) for the balanced tree and \(b=2\) for the path.

Each source independently samples \(t\) near bits
\(s^{(d)}_1,\ldots,s^{(d)}_t\). For the exterior indices
\(\{t+1,\ldots,n-1\}\), its bit vector is \(M_d U_d\) for
a public \(N\)-by-\(m\) binary matrix, where \(U_d\) comprises
\(m\) additional independent fair bits. The near and exterior
seeds are independent for each source. Take
\[
 m=\min(N,bt+2\ell+2).
\]
If \(N\le bt+2\ell+2\) use identity matrices: the exterior
vector is then fully uniform, also covering the case \(N=0\).
Otherwise choose matrices with the following property. For
each \(c\) with \(1\le c\le\min(t,n-t)\), and each set \(J\)
of \(c\) non-sources, let \(E_{\rm out}(J)\) be its exterior
endpoints. For every subset of \(c\) sources, at least one
of their matrices has full row rank on \(E_{\rm out}(J)\).
Equivalently, for every such \(J\) at most \(c-1\) sources have
deficient rank. This is a single simultaneous property of the
public matrices. The exterior endpoints do not depend on which sources are
corrupted, since source endpoints are never exterior. An
empty endpoint set is automatically full rank.

To prove such matrices exist in the non-identity case,
sample the entries of all \(t\) matrices independently and
uniformly for this **offline existence proof only**. Fix
\(J\) and put \(h=|E_{\rm out}(J)|\le bc\). For one matrix,
any fixed nonzero binary linear combination of these rows
vanishes with probability \(2^{-m}\), because it is uniform
on \(\mathbb F_2^m\). Taking the union over combinations
bounds rank failure by \((2^h-1)2^{-m}<2^{bc-m}\).
For a fixed subset of \(c\) sources their failures are
independent by construction. A union bound over \(J\) and
the source subsets is therefore at most
\[
 \sum_{c=1}^{\min(t,n-t)}
      \binom{n-t}{c}\binom{t}{c}2^{(bc-m)c}
 \le \sum_{c\ge1}2^{-2c}=1/3 <1,
\]
using at most \(n^c\) choices of the exterior parties (hence
of the endpoint sets) and at most \(n^c\) choices of a bad
source subset, together with \(m=bt+2\ell+2\). Fix a passing tuple of matrices as part of
the protocol description. No fresh choice of matrices is made
during execution and no seed for choosing them is counted in
the execution.

Now write \(k=|C|\le t\) and \(c=|C\setminus\{1,\ldots,t\}|\).
If \(c\ge1\), exactly \(k-c\) sources are corrupted, so
there are \(t-k+c\ge c\) honest sources. By the rank property
one honest source has full rank on the exterior set.
Its near bits are all independent and uniform and independent
of the exterior ones, so it satisfies the privacy criterion.
If \(c=0,k<t\), all coalition endpoints are near, so any
honest source suffices. If \(c=0,k=t\), the coalition is
precisely the first \(t\) parties and no source is honest. Its tape and setup messages are then determined by
known seeds. In the path every observed prefix is determined
by these seeds and the corrupt parties' inputs; the public
output is the only other input-dependent message. In the
tree all source leaves and all intervals of the source
subtree have this same property. The sole additional
incoming masked interval is the entire outside block at
the top node. Its unmasked XOR is the known total minus
(the XOR of) the source inputs, and its mask is a known
function of the seeds. The top node broadcasts only the
total. Thus this entire view is determined by the known
inputs, output and seeds, even when all sources are corrupted.

There are \(t(t+m)\) independent fair tosses for every
execution. Setup takes one round of private sends; the two
balanced subtrees aggregate in \(O(\log n)\) rounds and
broadcast the total in one more round. No message schedules
or lengths depend on the inputs or coin outcomes.

## 4. A separate explicit generator for any fixed tree

For any fixed ordered tree and any selection of \(k\) subtree
intervals, their joint masks are a linear map of at most
\(2k\) nonconstant prefix bits. Therefore \(2k\)-wise
independent fair prefix bits give exactly the distribution
under fully independent prefixes, including any dependencies
between intervals that share endpoints. The ideal map from
prefixes to an XOR-zero leaf-mask vector is bijective:
\(r_i=s_{i-1}\oplus s_i\) and \(s_j=\bigoplus_{i=1}^j r_i\).
This is precisely the ideal distribution used for the
parity-sharing condition of Goyal–Ishai–Song, ePrint
2022/799, §2.3 Definitions 1–2. It is for a fixed ordered
tree; it does not assert the same seed for simultaneous
access to arbitrary subsets of leaves.

Take \(K=\min(8t,n-1)\). Let \(u_1,\ldots,u_{n-1}\) be distinct
elements of \(\mathbb F_{2^\ell}\). A uniform degree-less-than-\(K\)
polynomial consumes precisely \(K\ell\) fair bits, as the
coefficient elements are uniform. Any \(h\le K\) of its
evaluations are jointly uniform on the field to the power
\(h\), since the first \(h\) coefficient columns form an
invertible Vandermonde matrix. Apply any fixed nonzero
\(\mathbb F_2\)-linear one-bit functional to each evaluation;
they give \(K\)-wise independent fair prefix bits. If independent
prefix generation uses fewer bits, use it instead.
An irreducible polynomial representation of the field can
be found deterministically by enumerating monic degree-\(\ell\)
polynomials and testing irreducibility; even trial division
over polynomials of degree at most \(\ell/2\) is polynomial
in \(n\) since \(2^\ell<2n\) for \(n\ge2\).
This makes the protocol description and all computations
deterministic polynomial time apart from the counted coins.

Let any \(t+1\) parties be sources, each using this independent
generator for its own seed. Every coalition has an honest
source, and at most \(8t\) nonconstant endpoints as in §2.
Its selected good source therefore supplies the uniform
bits required by the same full-view argument (including
the individual setup messages). Total tosses are at most
\((t+1)\min(n-1,K\ell)\). For the specially assigned two-block
tree of §3, use only its first \(t\) sources instead: whenever
there is an honest source, its generator is uniform on all
relevant endpoints; when no source is honest, the last case
of §3 applies. This reduces the factor \(t+1\) to \(t\) in that
tree. In particular, one need not pay a separate generator
seed per tree depth for this fixed-tree problem.

## 5. Comparison to established lower bounds

In the balanced and path constructions every individual
message has the form \(u(x)\oplus v(R)\): for setup take
\(u=0\), for aggregation use (1), and for the final total
take \(v=0\). Here \(R\) is the vector of all local random
tapes. The schedule is fixed. Thus these are in the
restricted class of Gál–Rosén Definition 4.1.
For \(2\le t<n\), their Theorem 4.2 gives
\(\Omega(t\log(n/t))\) in this class, while
Goyal–Ishai–Song Theorem 2 gives \(\Omega(t^2)\) in the full
model for \(t\le n-2\); at \(t=n-1\) the same order follows by
monotonicity from \(t=n-2\) (asymptotically as \(n\) grows).
The maximum of two lower bounds is at least half their
sum. Conversely \(t\log_2 n=t\log_2(n/t)+t\log_2 t\)
and \(\log_2 t\le t\). Therefore the class-specific optimum
is
\[
 \Theta(t^2+t\log(n/t)),\qquad 2\le t<n.
\]
This conclusion holds also when asking to use no more than
\(t\) local random sources in that class, because the upper
bound does. In the unrestricted model the new upper matches
the quadratic lower bound whenever \(t\ge\log_2 n\); it
does not resolve all smaller growing thresholds. The older
unrestricted \(\Omega(\log n)\) lower bound for \(t\ge2\)
already precludes a universal \(O(t^2)\) upper for all
\(t=o(n)\) (for example take \(t\) growing as
\((\log n)^{1/4}\)). Neither this observation nor the
well-known one-source, one-bit protocol for \(t=1\) is
claimed as new. No long-vector amortized rate, adaptive
corruption, active security or general nonlinear
functionality is covered.
